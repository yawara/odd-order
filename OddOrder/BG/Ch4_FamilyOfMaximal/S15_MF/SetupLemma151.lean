import OddOrder.BG.Ch4_FamilyOfMaximal.S14_TypePCounting
import OddOrder.BG.Ch1_Preliminary.S03h_Thm38
import OddOrder.BG.Ch1_Preliminary.S03g_Thm310ElemAbelian
import OddOrder.BG.Ch1_Preliminary.S05_NarrowCharacterization
import OddOrder.Mathlib.Subgroup

/-!
# BG §15 notation + Lemma 15.1 (U M_sigma auxiliary structure)

Split from the former monolithic `OddOrder.BG.Ch4_FamilyOfMaximal.S15_MF` (directory split, issue
0103).
-/
namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open OddOrder.BG.Ch4.S14
open scoped Pointwise
open scoped IsMulCommutative
open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## §15 notation -/

/-- **BG `M_F`**: the maximal nilpotent normal Hall subgroup of `M`. -/
noncomputable abbrev MF (M : Subgroup G) : Subgroup G :=
  maxNilpotentNormalHall M

/-- `M_F ≤ M`: basic containment, directly from the `sSup` construction.  (The §15
well-definedness that the `sSup` is again Hall is `maxNilpotentNormalHall_isHall` below; this
containment is the more elementary half.) -/
theorem maxNilpotentNormalHall_le (M : Subgroup G) : maxNilpotentNormalHall M ≤ M :=
  sSup_le fun _ hN => hN.1

/-- `M` normalizes `M_F` (so `(M_F).subgroupOf M ⊴ M`): the `sSup` of `M`-normal
candidates is again `M`-normal.  Like `maxNilpotentNormalHall_le`, this is part of the
`§14`-independent §15 well-definedness (the Hall property is `maxNilpotentNormalHall_isHall`);
each candidate `N` is fixed by conjugation by `m ∈ M` because `(N.subgroupOf M).Normal`. -/
theorem maxNilpotentNormalHall_le_normalizer (M : Subgroup G) :
    M ≤ Subgroup.normalizer (maxNilpotentNormalHall M) := by
  intro m hm
  refine mem_normalizer_of_conj_smul_eq_self ?_
  unfold maxNilpotentNormalHall
  rw [Subgroup.pointwise_smul_def, (Subgroup.gc_map_comap _).l_sSup, sSup_eq_iSup]
  refine iSup_congr fun N => iSup_congr fun hN => ?_
  rw [← Subgroup.pointwise_smul_def]
  obtain ⟨hNM, hNnorm, -, -⟩ := hN
  exact conj_smul_eq_self_of_mem_normalizer
    (((Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hNnorm) hm)

/-- `M_F ⊴ M` in the relative sense `(M_F).subgroupOf M`: the directly usable form of
`maxNilpotentNormalHall_le_normalizer`, matching the normality clause in the defining
predicate of `M_F`. -/
theorem maxNilpotentNormalHall_subgroupOf_normal (M : Subgroup G) :
    ((maxNilpotentNormalHall M).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (maxNilpotentNormalHall_le M)).mpr
    (maxNilpotentNormalHall_le_normalizer M)

/-- `M_F ≤ F(M)`: the maximal nilpotent normal Hall subgroup lies inside the Fitting subgroup
`F(M)` (`OddOrder.BG.Ch2.S08.fittingInG`, defeq `(Ch01.fitting ↥M).map M.subtype`), because each
candidate `N` is nilpotent and normal in `M` (so `N.subgroupOf M ≤ fitting ↥M`).  `§14`-independent;
the structural bridge between `M_F` and `F(M)` used throughout §15/§16. -/
theorem maxNilpotentNormalHall_le_fittingInG [Finite G] (M : Subgroup G) :
    maxNilpotentNormalHall M ≤ OddOrder.BG.Ch2.S08.fittingInG M := by
  refine sSup_le fun N hN => ?_
  obtain ⟨hNM, hNnorm, hNnil, -⟩ := hN
  haveI := hNnorm
  haveI := hNnil
  calc N = (N.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hNM).symm
    _ ≤ OddOrder.BG.Ch2.S08.fittingInG M :=
        Subgroup.map_mono OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting

/-- **`M_F` is nilpotent** — the §15 well-definedness piece that the defining `sSup` is again
nilpotent.  `M_F ≤ F(M)` (`maxNilpotentNormalHall_le_fittingInG`) and `F(M)` is nilpotent
(image of the nilpotent `fitting ↥M` under the injective `M.subtype`).  `§14`-independent. -/
theorem maxNilpotentNormalHall_isNilpotent [Finite G] (M : Subgroup G) :
    Group.IsNilpotent ↥(maxNilpotentNormalHall M) := by
  haveI : Group.IsNilpotent ↥(OddOrder.Isaacs.Ch01.fitting (↥M)) :=
    OddOrder.Isaacs.Ch01.fitting.isNilpotent
  haveI : Group.IsNilpotent ↥(OddOrder.BG.Ch2.S08.fittingInG M) :=
    Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective (OddOrder.Isaacs.Ch01.fitting (↥M)) M.subtype
        M.subtype_injective)
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (maxNilpotentNormalHall_le_fittingInG M))

/-- **`M_F` absorbs every nilpotent normal Hall subgroup** (`§14`-independent): a subgroup `N ≤ M`
that is `M`-normal (`(N.subgroupOf M).Normal`), nilpotent, and a Hall `π(N)`-subgroup of `M`
(`IsHallSubgroup (Nat.card ↥N).primeFactors (N.subgroupOf M)`) is one of the candidates in the
`sSup` defining `M_F = maxNilpotentNormalHall M`, hence `≤ M_F`.  This is the `le_sSup` half of the
`M_F` characterization (the converse `M_F ≤ M_σ` is `maxNilpotentNormalHall_le_Msigma`); it supplies
`Q ≤ M_F` in Theorem 15.2 once `Q = O_q(M)` is shown to be such a subgroup. -/
theorem le_maxNilpotentNormalHall {M N : Subgroup G} (hNM : N ≤ M)
    (hNnorm : (N.subgroupOf M).Normal) (hNnil : Group.IsNilpotent ↥(N.subgroupOf M))
    (hNhall : OddOrder.Isaacs.Ch03.IsHallSubgroup (Nat.card ↥N).primeFactors (N.subgroupOf M)) :
    N ≤ maxNilpotentNormalHall M :=
  le_sSup ⟨hNM, hNnorm, hNnil, hNhall⟩

/-- If `M_σ` is nilpotent, then `M_σ ≤ M_F`: `M_σ` is then a nilpotent normal Hall subgroup of
`M` (normal `σ`-core, `σ`-Hall by `Msigma_isHall`, nilpotent by hypothesis), hence one of the
candidates in the `sSup` defining `M_F`.  `§14`-independent.  Combined with the (gated)
`M_F ≤ M_σ` of Theorem A this gives `M_F = M_σ ⟺ M_σ` nilpotent (recall `M_F` is always
nilpotent, `maxNilpotentNormalHall_isNilpotent`). -/
theorem Msigma_le_maxNilpotentNormalHall_of_nilpotent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M)) :
    OddOrder.BG.Ch3.S10.Msigma M ≤ maxNilpotentNormalHall M := by
  haveI := hnil
  have hle := OddOrder.BG.Ch3.S10.Msigma_le M
  have hcard : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) =
      Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  apply le_sSup
  refine ⟨hle, ?_, ?_, ?_⟩
  · rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  · exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm
  · obtain ⟨hHcard, hHidx⟩ := OddOrder.BG.Ch3.S10.Msigma_isHall hG hM
    refine ⟨fun q hq => by rwa [hcard] at hq, fun q hq hqπ => ?_⟩
    obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.mp hq
    have hdvd : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index ∣
        (OddOrder.BG.Ch3.S10.Msigma M).index :=
      Subgroup.relIndex_dvd_index_of_le hle
    exact hHidx q
      (Nat.mem_primeFactors.mpr ⟨hqp, hqd.trans hdvd, Subgroup.index_ne_zero_of_finite⟩)
      (hHcard q hqπ)

/-- **`M_F ≤ M_σ`** (BG §15, mmd L4116 "it is easy to see ... `M_F` ... lies in `M_σ`").
Every nilpotent normal Hall subgroup `N` of `M` is a `σ(M)`-group: for a prime `p ∣ |N|`, the
Sylow `p`-subgroup of `N` is characteristic in `N` (nilpotent) hence normal in `M`, and a full
Sylow `p`-subgroup of `M` (`N` Hall), so it maps to `O_p(M)`; minimality of `M` and simplicity
of `G` give `N_G(O_p(M)) ≤ M`, i.e. `p ∈ σ(M)`.  Then `N ≤ O_{σ(M)}(M) = M_σ` by maximality of
the `σ(M)`-core.  `§14`-independent. -/
theorem maxNilpotentNormalHall_le_Msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    maxNilpotentNormalHall M ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  refine sSup_le fun N hN => ?_
  obtain ⟨hNM, hNnorm, hNnil, hNHall⟩ := hN
  haveI := hNnorm
  haveI := hNnil
  set N' : Subgroup ↥M := N.subgroupOf M with hN'def
  have hcardN' : Nat.card ↥N' = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  -- `N'` is a `σ(M)`-group: every prime divisor of `|N|` lies in `σ(M)`.
  have hpi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma M) N' := by
    intro p hp
    have hpN : p ∈ (Nat.card ↥N).primeFactors := by rwa [hcardN'] at hp
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    have hpM : p ∈ (Nat.card ↥M).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨‹Fact p.Prime›.1,
        (Nat.dvd_of_mem_primeFactors hpN).trans
          (hcardN' ▸ Subgroup.card_subgroup_dvd_card N'), Nat.card_pos.ne'⟩
    -- `p ∤ [M : N']` (Hall), so the `p`-part of `|M|` is concentrated in `N'`.
    have hpidx : ¬ p ∣ N'.index := fun hdvd =>
      hNHall.2 p (Nat.mem_primeFactors.mpr
        ⟨‹Fact p.Prime›.1, hdvd, Subgroup.index_ne_zero_of_finite⟩) hpN
    have hfact : (Nat.card ↥M).factorization p = (Nat.card ↥N').factorization p := by
      conv_lhs => rw [← Subgroup.card_mul_index N']
      rw [Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpidx, add_zero]
    -- The Sylow `p`-subgroup of the nilpotent `N'` is characteristic, hence normal in `M`,
    -- and (Hall) a full Sylow `p`-subgroup of `M`.
    obtain ⟨SN⟩ := (inferInstance : Nonempty (Sylow p ↥N'))
    haveI hSNnorm : (SN : Subgroup ↥N').Normal :=
      OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent SN
    haveI hSNchar : (SN : Subgroup ↥N').Characteristic :=
      Sylow.characteristic_of_normal SN hSNnorm
    have hScard : Nat.card ↥((SN : Subgroup ↥N').map N'.subtype) =
        p ^ (Nat.card ↥M).factorization p := by
      rw [Subgroup.card_map_of_injective N'.subtype_injective, SN.card_eq_multiplicity, hfact]
    haveI hmapnorm : ((SN : Subgroup ↥N').map N'.subtype).Normal := inferInstance
    let P : Sylow p ↥M := Sylow.ofCard ((SN : Subgroup ↥N').map N'.subtype) hScard
    have hPnorm : (P : Subgroup ↥M).Normal := hmapnorm
    have hPmap : (P : Subgroup ↥M).map M.subtype = OddOrder.GroupTheory.opiCoreInG {p} M :=
      OddOrder.BG.Ch3.S10.sylowMap_eq_opiCoreInG_singleton_of_normal P hPnorm
    have hPne : OddOrder.GroupTheory.opiCoreInG {p} M ≠ ⊥ :=
      OddOrder.BG.Ch3.S10.opiCoreInG_singleton_ne_bot_of_sylowMap_eq hpM P hPmap
    rw [OddOrder.BG.Ch3.S10.mem_sigma_iff]
    refine ⟨hpM, P, ?_⟩
    rw [hPmap]
    exact OddOrder.BG.Ch2.S09.normalizer_opiCoreInG_singleton_le_maximal_of_ne_bot hG hM hPne
  calc N = N'.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hNM).symm
    _ ≤ (OddOrder.Isaacs.Ch03.oPiCore (OddOrder.BG.Ch3.S10.sigma M) ↥M).map M.subtype :=
        Subgroup.map_mono hpi.le_oPiCore
    _ = OddOrder.BG.Ch3.S10.Msigma M := rfl

/-- **`M_F = M_σ ⟺ M_σ` is nilpotent** (`§14`-independent).  Forward: `M_F` is always nilpotent
(`maxNilpotentNormalHall_isNilpotent`).  Backward: `maxNilpotentNormalHall_le_Msigma` (always)
and `Msigma_le_maxNilpotentNormalHall_of_nilpotent` give equality by antisymmetry. -/
theorem maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M ↔
      Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  refine ⟨fun h => h ▸ maxNilpotentNormalHall_isNilpotent M, fun hnil => ?_⟩
  exact le_antisymm (maxNilpotentNormalHall_le_Msigma hG hM)
    (Msigma_le_maxNilpotentNormalHall_of_nilpotent hG hM hnil)

/-- **`M_F ≤ M'`** (the `H ⊆ M'` part of BG Corollary 15.5(c), `H = M_F`): the containment chain
`M_F ≤ M_σ ≤ M' ≤ M` via `maxNilpotentNormalHall_le_Msigma` and `Msigma_le_derived`.
`§14`-independent.  (The `M'/M_F` nilpotency of 15.5(c) remains deferred — quotient API.) -/
theorem maxNilpotentNormalHall_le_derived [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    maxNilpotentNormalHall M ≤ derivedInG M :=
  (maxNilpotentNormalHall_le_Msigma hG hM).trans (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM)

/-- **General helper (§14-independent, reusable).**  In a finite group, the `sSup` of a set `s`
of normal `π`-subgroups is again a `π`-subgroup.  (Mirrors the `Finset.sup_induction` argument of
`Ch03.oPiCore.isPiGroup`, but for an arbitrary set rather than the defining family of `oPiCore`.)
Used for the §15 well-definedness "`M_F` is Hall": the supremum defining `M_F` collapses to a join
of normal subgroups, whose order has no new prime factors. -/
theorem isPiGroup_sSup_of_forall_normal {H : Type*} [Group H] [Finite H] (π : Set ℕ)
    (s : Set (Subgroup H)) (hnorm : ∀ N ∈ s, N.Normal)
    (hpi : ∀ N ∈ s, Ch03.Subgroup.IsPiGroup π N) :
    Ch03.Subgroup.IsPiGroup π (sSup s) := by
  classical
  haveI hSubF : Fintype {N : Subgroup H // N ∈ s} := Fintype.ofFinite _
  -- Carry both normality and the `π`-group property through the induction.
  set q : Subgroup H → Prop := fun K => K.Normal ∧ Ch03.Subgroup.IsPiGroup π K with hq_def
  suffices hgoal : q (sSup s) by exact hgoal.2
  -- Rewrite the `sSup` as a `Finset.sup` over the (finite) subtype `{N // N ∈ s}`.
  have hsup : sSup s =
      (Finset.univ : Finset {N : Subgroup H // N ∈ s}).sup (fun N => (N.val : Subgroup H)) := by
    rw [Finset.sup_eq_iSup]
    simp only [iSup_pos, Finset.mem_univ]
    rw [← sSup_eq_iSup']
  rw [hsup]
  refine Finset.sup_induction (p := q) ?_ ?_ ?_
  · -- `⊥` is a normal `π`-group (no prime factors).
    refine ⟨inferInstance, ?_⟩
    intro r hr
    simp only [Subgroup.card_bot, Nat.primeFactors_one, Finset.notMem_empty] at hr
  · -- closure under join of two normal `π`-subgroups.
    rintro a₁ ⟨ha₁N, ha₁Pi⟩ a₂ ⟨ha₂N, ha₂Pi⟩
    haveI := ha₁N
    haveI := ha₂N
    exact ⟨inferInstance, Ch03.Subgroup.IsPiGroup.sup_of_normal ha₁Pi ha₂Pi⟩
  · -- each generator is a normal `π`-group by hypothesis.
    intro b _
    exact ⟨hnorm b.val b.2, hpi b.val b.2⟩

/-- **BG §15 well-definedness: `M_F` is a Hall subgroup of `M`** (general finite-group fact,
§14-independent; no minimal-simple hypothesis needed).  `M_F = maxNilpotentNormalHall M` is, as a
relative subgroup `(M_F).subgroupOf M ⊴ M`, a `π(M_F)`-Hall subgroup of `M`, where
`π(M_F) = (Nat.card ↥(M_F)).primeFactors`.

Proof: `(M_F).subgroupOf M` is the join (in `↥M`) of the normal subgroups `N.subgroupOf M`
ranging over the candidates `N` of the `sSup` defining `M_F`; this join has no prime factor beyond
those of the candidates (`isPiGroup_sSup_of_forall_normal`).  Hence every prime `p ∣ |M_F|` divides
some candidate `|N₀|`, and that candidate is `π(N₀)`-Hall in `↥M` with `p ∈ π(N₀)`, so
`p ∤ [M : N₀.subgroupOf M]`; since `N₀.subgroupOf M ≤ (M_F).subgroupOf M`, also `p ∤ [M : M_F]`.
The index of `(M_F).subgroupOf M` therefore shares no prime with `|M_F|`, i.e. `M_F` is Hall. -/
theorem maxNilpotentNormalHall_isHall [Finite G] (M : Subgroup G) :
    Ch03.IsHallSubgroup (Nat.card ↥(maxNilpotentNormalHall M)).primeFactors
      ((maxNilpotentNormalHall M).subgroupOf M) := by
  classical
  set H : Subgroup G := maxNilpotentNormalHall M with hHdef
  set Hbar : Subgroup ↥M := H.subgroupOf M with hHbar
  -- The defining set of `M_F`, and its image in `↥M`.
  set S : Set (Subgroup G) := {N : Subgroup G | N ≤ M ∧ (N.subgroupOf M).Normal ∧
      Group.IsNilpotent ↥(N.subgroupOf M) ∧
      Ch03.IsHallSubgroup (Nat.card ↥N).primeFactors (N.subgroupOf M)} with hSdef
  have hHsSup : H = sSup S := rfl
  set T : Set (Subgroup ↥M) := (fun N => N.subgroupOf M) '' S with hTdef
  -- `card Hbar = card H` (since `H ≤ M`).
  have hHle : H ≤ M := maxNilpotentNormalHall_le M
  have hcardHbar : Nat.card ↥Hbar = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv
  -- `⨆ x ∈ T, map x = ⨆ N ∈ S, N`, since `map (N.subgroupOf M) = N` for `N ≤ M ∈ S`.
  have hiSup : (⨆ x ∈ T, x.map M.subtype) = ⨆ N ∈ S, N := by
    rw [hTdef, iSup_image]
    refine iSup_congr fun N => iSup_congr fun hN => ?_
    exact Subgroup.map_subgroupOf_eq_of_le hN.1
  -- Key identification: `Hbar = sSup T`.
  have hHbar_eq : Hbar = sSup T := by
    apply Subgroup.map_injective M.subtype_injective
    rw [hHbar, Subgroup.map_subgroupOf_eq_of_le hHle, hHsSup,
      (Subgroup.gc_map_comap M.subtype).l_sSup, hiSup, ← sSup_eq_iSup]
  -- Every element of `T` is normal in `↥M` and a `Pri`-group, where `Pri` is the set of primes
  -- occurring in some candidate's order.
  set Pri : Set ℕ := {p | ∃ N ∈ S, p ∈ (Nat.card ↥N).primeFactors} with hPridef
  have hTnorm : ∀ x ∈ T, x.Normal := by
    rintro x ⟨N, hN, rfl⟩; exact hN.2.1
  have hTpi : ∀ x ∈ T, Ch03.Subgroup.IsPiGroup Pri x := by
    rintro x ⟨N, hN, rfl⟩
    intro p hp
    -- `card (N.subgroupOf M) = card N`, so a prime factor of it is one of `N`.
    have hcardN : Nat.card ↥(N.subgroupOf M) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN.1).toEquiv
    exact ⟨N, hN, by rwa [hcardN] at hp⟩
  -- Hence `Hbar` is a `Pri`-group.
  have hHbarpi : Ch03.Subgroup.IsPiGroup Pri Hbar := by
    rw [hHbar_eq]; exact isPiGroup_sSup_of_forall_normal Pri T hTnorm hTpi
  -- Assemble the Hall property.
  refine ⟨fun p hp => ?_, fun p hp hpπ => ?_⟩
  · -- Prime factors of `|Hbar| = |H|` are exactly `π(M_F)`.
    rwa [hcardHbar] at hp
  · -- `p ∈ π(M_F)` and `p ∣ [M : Hbar]`: derive a contradiction.
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    -- `p ∈ π(M_F)`, so `p ∣ |Hbar|`, so `p ∈ Π`: pick a candidate `N₀` with `p ∣ |N₀|`.
    have hpHbar : p ∈ (Nat.card ↥Hbar).primeFactors := by
      rw [hcardHbar]; exact hpπ
    obtain ⟨N₀, hN₀, hpN₀⟩ := hHbarpi p hpHbar
    -- `N₀.subgroupOf M` is `π(N₀)`-Hall with `p ∈ π(N₀)`, so `p ∤ [M : N₀.subgroupOf M]`.
    have hpN₀Hall : ¬ p ∣ (N₀.subgroupOf M).index := by
      intro hdvd
      exact hN₀.2.2.2.2 p
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hpN₀
    -- `N₀.subgroupOf M ≤ Hbar`, so `[M : Hbar] ∣ [M : N₀.subgroupOf M]`, so `p ∤ [M : Hbar]`.
    have hN₀_le_H : N₀ ≤ H := hHsSup ▸ le_sSup hN₀
    have hle : N₀.subgroupOf M ≤ Hbar := by
      rw [hHbar]; exact Subgroup.subgroupOf_mono M hN₀_le_H
    exact hpN₀Hall ((Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.index_dvd_of_le hle))

/-- The Fitting subgroup of `M`, viewed in the ambient group as in BG §8/§15. -/
noncomputable abbrev fittingInAmbient (M : Subgroup G) : Subgroup G :=
  OddOrder.BG.Ch2.S08.fittingInG M

/-- **`F(H) = H` for a nilpotent subgroup `H`** (`§14`-independent, reusable): the Fitting
subgroup of a nilpotent group is the whole group (`fitting ↥H = ⊤`), so its ambient realization
`fittingInAmbient H` is just `H`.  Used by Corollary 15.5 (the `M_F = M_σ` case, where `M_σ` is
nilpotent so `F(M_σ) = M_σ = M_F`) and the `M_F` cyclic ⟹ `F(M)` cyclic step of Corollary 15.6. -/
theorem fittingInAmbient_eq_self_of_isNilpotent [Finite G] {H : Subgroup G}
    [Group.IsNilpotent ↥H] : fittingInAmbient H = H := by
  haveI : Group.IsNilpotent ↥(⊤ : Subgroup ↥H) :=
    Group.nilpotent_of_mulEquiv Subgroup.topEquiv.symm
  have htop : OddOrder.Isaacs.Ch01.fitting ↥H = ⊤ :=
    top_le_iff.mp OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
  change (OddOrder.Isaacs.Ch01.fitting ↥H).map H.subtype = H
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- **Converse of `fittingInAmbient_eq_self_of_isNilpotent`** (`§14`-independent, reusable): if the
ambient realization of the Fitting subgroup is all of `H` (`fittingInAmbient H = H`), then `H` is
nilpotent.  Together with the forward direction this is `IsNilpotent ↥H ↔ fittingInAmbient H = H`.

Used in Theorem 15.2's step 2 (the contrapositive of Theorem 3.8): from `⁅M_σ, K⁆ = M_σ ⊆ F(M_σ)`
one gets `F(M_σ) = M_σ`, hence `M_σ` nilpotent — contradicting `M_F ≠ M_σ`. -/
theorem isNilpotent_of_fittingInAmbient_eq_self [Finite G] {H : Subgroup G}
    (h : fittingInAmbient H = H) : Group.IsNilpotent ↥H := by
  have htop : OddOrder.Isaacs.Ch01.fitting ↥H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact h
  have hnil : Group.IsNilpotent ↥(OddOrder.Isaacs.Ch01.fitting ↥H) :=
    OddOrder.Isaacs.Ch01.fitting.isNilpotent
  rw [htop] at hnil
  haveI := hnil
  exact Group.nilpotent_of_mulEquiv Subgroup.topEquiv

/-! ### The Aut-abelian core (`§14`-independent, reusable)

The next two lemmas package the elementary fact behind the "`M_F` not cyclic" half of
Corollary 15.6: if a normal subgroup `N ⊴ H` is **cyclic**, then `Aut(N)` is abelian, so the
conjugation map `H → Aut(N)` (kernel `C_H(N)`) sends `H'` to `1`, i.e. `H' ≤ C_H(N)`.
Specialised to `N = F(M)` and combined with the self-centralizing property of the Fitting
subgroup (`centralizer_fitting_le_fitting`), `F(M)` cyclic forces `M'' = 1`. -/

/-- The conjugation action commutator of `H` on itself is the ordinary derived subgroup:
`actionCommutator (MulAut.conj) = commutator H`.  (Both are the closure of the commutator
elements `g * (a g⁻¹ a⁻¹) = ⁅g, a⁆`.) -/
private theorem actionCommutator_conj_eq_commutator {H : Type*} [Group H] :
    OddOrder.Isaacs.Ch04.actionCommutator (MulAut.conj : H →* MulAut H) = commutator H := by
  rw [commutator_eq_closure]
  unfold OddOrder.Isaacs.Ch04.actionCommutator
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, commutatorSet_def]
  constructor
  · rintro ⟨g, a, rfl⟩
    exact ⟨g, a, by rw [commutatorElement_def, MulAut.conj_apply]; group⟩
  · rintro ⟨g₁, g₂, rfl⟩
    exact ⟨g₁, g₂, by rw [commutatorElement_def, MulAut.conj_apply]; group⟩

open OddOrder.BG.Ch1.OperatorQuotientAction in
/-- **Aut-abelian core**: if `N ⊴ H` is cyclic, then `H' ≤ C_H(N)`.  Conjugation gives a
homomorphism `H → Aut(↥N)` with kernel `C_H(N)`; `↥N` cyclic makes `Aut(↥N)` abelian, so the
derived subgroup `H'` lands in the kernel.  Reuses the BG Thm 4.12 machinery
(`actionCommutator_le_centralizer_of_isCyclic_isAInvariant`) with `φ = MulAut.conj`. -/
theorem commutator_le_centralizer_of_normal_isCyclic {H : Type*} [Group H]
    {N : Subgroup H} [IsCyclic ↥N] (hN : N.Normal) :
    commutator H ≤ Subgroup.centralizer (N : Set H) := by
  have hinv : OddOrder.Isaacs.Ch03.IsAInvariant (MulAut.conj : H →* MulAut H) N := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a g hg
    rw [MulAut.conj_apply]
    exact hN.conj_mem g hg a
  have h := actionCommutator_le_centralizer_of_isCyclic_isAInvariant
    (φ := (MulAut.conj : H →* MulAut H)) (S := N) hN hinv
  rwa [actionCommutator_conj_eq_commutator] at h

/-- **BG §15, `F(M)` cyclic ⟹ `M'' = 1`** (`§14`-independent).  If the ambient Fitting subgroup
`F(M)` is cyclic then `M' ≤ C_M(F(M)) ≤ F(M)` (Aut-abelian core + Fitting self-centralizing),
so `M'` is abelian and `M'' = 1`.  This is the engine of Corollary 15.6's "`M_F` not cyclic"
clause. -/
theorem fittingInAmbient_cyclic_imp_derivedDerived_eq_bot [Finite G] {M : Subgroup G}
    [IsSolvable ↥M] (hcyc : IsCyclic ↥(fittingInAmbient M)) :
    derivedInG (derivedInG M) = ⊥ := by
  -- `fitting ↥M` is cyclic (transport of `hcyc` along `fittingInAmbient M ≅ fitting ↥M`)
  haveI hfitcyc : IsCyclic ↥(OddOrder.Isaacs.Ch01.fitting ↥M) := by
    have e : ↥(OddOrder.Isaacs.Ch01.fitting ↥M) ≃* ↥(fittingInAmbient M) :=
      Subgroup.equivMapOfInjective (OddOrder.Isaacs.Ch01.fitting ↥M) M.subtype M.subtype_injective
    exact isCyclic_of_surjective e.symm e.symm.surjective
  -- `commutator ↥M ≤ centralizer (fitting ↥M) ≤ fitting ↥M`
  have hcomm_le : commutator ↥M ≤ OddOrder.Isaacs.Ch01.fitting ↥M :=
    (commutator_le_centralizer_of_normal_isCyclic
      (inferInstance : (OddOrder.Isaacs.Ch01.fitting ↥M).Normal)).trans
      OddOrder.BG.Ch1.S01.centralizer_fitting_le_fitting
  -- push to the ambient group: `M' = ⁅M, M⁆ ≤ F(M)`
  have hderiv_le : derivedInG M ≤ fittingInAmbient M := Subgroup.map_mono hcomm_le
  -- `F(M)` cyclic ⟹ abelian ⟹ `F(M) ≤ C_G(F(M))`
  have hself : (fittingInAmbient M : Subgroup G) ≤ Subgroup.centralizer (fittingInAmbient M) := by
    haveI := hcyc
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h : (⟨y, hy⟩ : ↥(fittingInAmbient M)) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨y, hy⟩ := mul_comm' _ _
    calc y * x = ↑((⟨y, hy⟩ : ↥(fittingInAmbient M)) * ⟨x, hx⟩) := by rw [Subgroup.coe_mul]
      _ = ↑((⟨x, hx⟩ : ↥(fittingInAmbient M)) * ⟨y, hy⟩) := by rw [h]
      _ = x * y := by rw [Subgroup.coe_mul]
  -- `M'' = ⁅M', M'⁆ ≤ ⁅F(M), F(M)⁆ = 1`
  rw [show derivedInG (derivedInG M) = ⁅derivedInG M, derivedInG M⁆ from
        Subgroup.map_subtype_commutator (derivedInG M)]
  refine le_bot_iff.mp (le_trans (Subgroup.commutator_mono hderiv_le hderiv_le) ?_)
  exact le_of_eq (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hself)

/-- **§14-independent engine for BG Corollary 15.6's `K* ⊆ M''` clause.**  Given the type-`P`
complement structure `M = K M'` with `K ∩ M' = 1` (BG Theorem 14.7(h), here as the relative-
complement hypothesis `hcompl` inside `↥M`) and the coprimality of `|M'|` and `|K|`, Lemma 6.3
(`centralizer_inf_le_derivedInG_of_isComplement'`, proved) yields `C_{M'}(K) ⊆ M''`; since
`K* = C_{M_σ}(K) = M_σ ⊓ C_G(K) ⊆ C_{M'}(K)` (because `M_σ ⊆ M'`), this gives `K* ⊆ M''`.

The complement/coprimality data are the only `§14` inputs; everything else is unconditional, so
Corollary 15.6 reduces its `K* ⊆ M''` clause to a single citation once Theorem 14.7(h) (or the
`IsComplement' (derivedInG M) K` strengthening of Lemma 15.1) lands.  Mirrors the Lemma 6.3
transport in `S12_E.Msigma_E_relations`, with `M'` in place of `M_σ` and `K` in place of `E`. -/
theorem Msigma_inf_centralizer_le_derivedDerived_of_isComplement' [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M))
    (hcop : Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M))
      (Nat.card ↥(K.subgroupOf M))) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≤
      derivedInG (derivedInG M) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hMσ_le_deriv : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M :=
    OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  have hderivM : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `H := (derivedInG M).subgroupOf M = commutator ↥M`, normal in `↥M`.
  have hid : (derivedInG M).subgroupOf M = commutator ↥M :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)
  haveI hHnorm : ((derivedInG M).subgroupOf M).Normal := by rw [hid]; infer_instance
  have hH_le : (derivedInG M).subgroupOf M ≤ commutator ↥M := le_of_eq hid
  -- Lemma 6.3 inside `↥M`:  `C_{↥M}(K') ⊓ H ≤ derivedInG H`.
  have h632 := OddOrder.BG.Ch1.S06.centralizer_inf_le_derivedInG_of_isComplement'
    (G := ↥M) hcompl hH_le hcop
  -- Transport identity:  `(derivedInG H).map M.subtype = derivedInG (derivedInG M)`.
  have hderiv_transport :
      (derivedInG ((derivedInG M).subgroupOf M)).map M.subtype =
        derivedInG (derivedInG M) := by
    rw [show derivedInG ((derivedInG M).subgroupOf M)
          = ⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆
          from Subgroup.map_subtype_commutator _,
      Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hderivM,
      show ⁅(derivedInG M : Subgroup G), derivedInG M⁆ = derivedInG (derivedInG M)
          from (Subgroup.map_subtype_commutator _).symm]
  -- Pointwise: every `x ∈ M_σ ⊓ C_G(K)` lands in `derivedInG (derivedInG M)`.
  intro x hx
  obtain ⟨hxMσ, hxC⟩ := hx
  have hxM : x ∈ M := hMσM hxMσ
  have hxmem : (⟨x, hxM⟩ : ↥M) ∈
      Subgroup.centralizer ((K.subgroupOf M : Subgroup ↥M) : Set ↥M)
        ⊓ (derivedInG M).subgroupOf M := by
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, ?_⟩
    · intro k' hk'
      have hkK : ((k' : ↥M) : G) ∈ K := Subgroup.mem_subgroupOf.mp hk'
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (k' : G) hkK)
    · exact Subgroup.mem_subgroupOf.mpr (hMσ_le_deriv hxMσ)
  have hmapped := Subgroup.mem_map_of_mem M.subtype (h632 hxmem)
  rwa [hderiv_transport] at hmapped

/-- The nonidentity part of the ambient Fitting subgroup of `M`. -/
def fittingSharp (M : Subgroup G) : Set G :=
  sharpSubgroup (fittingInAmbient M)

/-- The BG §15 hypothesis that `F(M)` is a TI-subgroup of `G`. -/
def FittingIsTI (M : Subgroup G) : Prop :=
  IsTISubset (fittingSharp M) (Subgroup.normalizer ((fittingInAmbient M : Subgroup G) : Set G))

/-- The subgroup generated by the centralizers in `U` of nonidentity elements of
`M_sigma`; this packages BG Lemma 15.1(d). -/
noncomputable def centralizerGeneratedBySigma (M U : Subgroup G) : Subgroup G :=
  sSup {C : Subgroup G | ∃ x ∈ sigmaSharp M,
    C = U ⊓ Subgroup.centralizer ({x} : Set G)}

/-! ### Lemma 15.1 helpers -/

/-- **`K ≠ ⊥` for a Hall `κ(M)`-subgroup of `M` forces `IsTypeP M`** (`§14`-independent bridge).
A nontrivial Hall `κ(M)`-subgroup has a prime divisor, which lies in `κ(M)`; hence `κ(M)` is
nonempty, i.e. `M` is type `P`.  This converts the `K ≠ ⊥` case split of Lemma 15.1 into the
`IsTypeP M` hypothesis that the §14 results (`typeP_duality`, `typeP_structure`) require. -/
theorem isTypeP_of_isHall_kappa_subgroupOf_ne_bot [Finite G] {M K : Subgroup G}
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) (hKne : K.subgroupOf M ≠ ⊥) :
    S14.IsTypeP M := by
  have hcard : Nat.card ↥(K.subgroupOf M) ≠ 1 := fun h => hKne (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
  exact ⟨p, hK.1 p (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩)⟩

/-- **Abstract second-derived containment** (`§14`-independent, reusable): if `N ⊴ H` and the
derived subgroup of the quotient `H ⧸ N` is abelian, then `⁅H', H'⁆ ≤ N` (the second derived
subgroup of `H`, as a subgroup of `H`, lies in `N`).  The quotient map `mk'` sends `⁅H', H'⁆`
onto `(H/N)''`, which is trivial because `(H/N)'` is abelian; hence `⁅H', H'⁆ ≤ ker mk' = N`.
This is the "(M/M_σ)' abelian ⟹ M'' ≤ M_σ" step of Lemma 15.1(a). -/
theorem commutator_commutator_le_of_quotient_commutator_commutative {H : Type*} [Group H]
    {N : Subgroup H} [hN : N.Normal] (hab : IsMulCommutative ↥(commutator (H ⧸ N))) :
    ⁅commutator H, commutator H⁆ ≤ N := by
  -- `(H/N)'' = ⁅(H/N)', (H/N)'⁆ = ⊥` since `(H/N)'` is abelian.
  have hdd_bot : ⁅commutator (H ⧸ N), commutator (H ⧸ N)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := hab.is_comm.comm (⟨y, hy⟩ : ↥(commutator (H ⧸ N))) ⟨x, hx⟩
    exact congrArg Subtype.val this
  -- `(H/N)' = (H').map mk'` and `(H/N)'' = ⁅H', H'⁆.map mk'` (mk' surjective).
  have hsurj : (QuotientGroup.mk' N).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
  have hmap1 : (commutator H).map (QuotientGroup.mk' N) = commutator (H ⧸ N) := by
    rw [map_commutator_eq, hsurj, _root_.commutator_def]
  have hmap2 : (⁅commutator H, commutator H⁆).map (QuotientGroup.mk' N) =
      ⁅commutator (H ⧸ N), commutator (H ⧸ N)⁆ := by
    rw [Subgroup.map_commutator, hmap1]
  rw [hdd_bot, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap2
  exact hmap2

/-- **`IsMulCommutative` of a commutator subgroup transports along a `MulEquiv`** (`§14`-
independent, reusable): if `A ≃* B` and `A'` is abelian, then `B'` is abelian.  The equivalence
maps `A'` onto `B'`, so `↥A' ≃* ↥B'`. -/
theorem isMulCommutative_commutator_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : IsMulCommutative ↥(commutator A)) : IsMulCommutative ↥(commutator B) := by
  have hmap : (commutator A).map (e : A →* B) = commutator B := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective, _root_.commutator_def]
  exact OddOrder.BG.Ch3.S11.isMulCommutative_of_mulEquiv
    ((MulEquiv.subgroupMap e (commutator A)).trans (MulEquiv.subgroupCongr hmap)) hA

/-- **Lemma 15.1(a), the `M'' ≤ M_σ` conjunct** (`§14`-independent): the second derived subgroup
of a maximal subgroup `M` is contained in `M_σ`.  Equivalently `(M/M_σ)'` is abelian; this is
Corollary 12.10(b) (`E' = (M/M_σ)'` abelian via the complement `M = M_σ ⋊ E`).  Proof: pick a
`SubgroupESetup` complement `E`, get `IsMulCommutative (derivedInG E)` from Cor 12.10(b), transport
it to `(↥M ⧸ N)'` abelian along `↥M ⧸ N ≃* E` (`IsComplement'.QuotientMulEquiv`), then apply the
abstract `commutator_commutator_le_of_quotient_commutator_commutative` and push to the ambient. -/
theorem derivedDerived_le_Msigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    derivedInG (derivedInG M) ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  -- §12 complement setup and `(M/M_σ)' = E'` abelian (Cor 12.10(b)).
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := OddOrder.BG.Ch3.S12.exists_subgroupESetup hG hM
  obtain ⟨_, ⟨_, hE'ab⟩, _⟩ := OddOrder.BG.Ch3.S12.nilpotent_sigmaComplement_abelian hG hsetup
  set N : Subgroup ↥M := (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M with hNdef
  haveI hNnorm : N.Normal := by rw [hNdef, OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  -- `derivedInG E ≅ commutator ↥E`, so `commutator ↥E` is abelian.
  have hcommE_ab : IsMulCommutative ↥(commutator ↥E) := by
    have e : ↥(commutator ↥E) ≃* ↥(derivedInG E) :=
      Subgroup.equivMapOfInjective (commutator ↥E) E.subtype E.subtype_injective
    exact OddOrder.BG.Ch3.S11.isMulCommutative_of_mulEquiv e.symm hE'ab
  -- transport `commutator ↥E` abelian to `commutator (↥M ⧸ N)` abelian via the complement iso.
  have hquot_ab : IsMulCommutative ↥(commutator (↥M ⧸ N)) := by
    have hcompl : (E.subgroupOf M).IsComplement' N := hsetup.isComplement'_subgroupOf.symm
    have e1 : (↥M ⧸ N) ≃* ↥(E.subgroupOf M) := hcompl.QuotientMulEquiv
    have e2 : ↥(E.subgroupOf M) ≃* ↥E := Subgroup.subgroupOfEquivOfLe hsetup.E_le
    exact isMulCommutative_commutator_of_mulEquiv (e1.trans e2).symm hcommE_ab
  -- abstract lemma: `⁅commutator ↥M, commutator ↥M⁆ ≤ N`, then push to the ambient.
  have hle : ⁅commutator ↥M, commutator ↥M⁆ ≤ N :=
    commutator_commutator_le_of_quotient_commutator_commutative hquot_ab
  -- `derivedInG (derivedInG M) = ⁅commutator ↥M, commutator ↥M⁆.map M.subtype`.
  have hderiv_eq : derivedInG (derivedInG M) =
      (⁅commutator ↥M, commutator ↥M⁆).map M.subtype := by
    rw [show derivedInG (derivedInG M) = ⁅derivedInG M, derivedInG M⁆ from
        Subgroup.map_subtype_commutator (derivedInG M),
      derivedInG, Subgroup.map_commutator]
  rw [hderiv_eq]
  calc (⁅commutator ↥M, commutator ↥M⁆).map M.subtype
      ≤ N.map M.subtype := Subgroup.map_mono hle
    _ = OddOrder.BG.Ch3.S10.Msigma M := by
        rw [hNdef, Subgroup.map_subgroupOf_eq_of_le (OddOrder.BG.Ch3.S10.Msigma_le M)]

/-- **`K = ⊥` forces `κ(M) = ∅`** (`§14`-independent): if the Hall `κ(M)`-subgroup `K ≤ M` of `M`
is trivial, then `M` has no `κ(M)`-prime, so `κ(M) = ∅`, i.e. `M` is type `F`.  (A `κ(M)`-prime
would divide `|M|` — `κ(M) ⊆ π(M)` — and the Hall `κ(M)`-subgroup would be nontrivial.) -/
theorem isTypeF_of_isHall_kappa_eq_bot [Finite G] {M K : Subgroup G} (_hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) (hKbot : K = ⊥) :
    S14.IsTypeF M := by
  by_contra hF
  -- `¬ IsTypeF M` means `κ(M) ≠ ∅`, so there is a `κ(M)`-prime `p`.
  rw [S14.IsTypeF, ← ne_eq, ← Set.nonempty_iff_ne_empty] at hF
  obtain ⟨p, hp⟩ := hF
  -- `p ∈ κ(M)`, so `p` is prime with a line `P ∈ ℰ_p¹(G)`, `P ≤ M`, `M_σ ⊓ C_G(P) ≠ 1`.
  have hpp : p.Prime := hp.1
  obtain ⟨_, P, hP, hPM, _⟩ := hp.2
  haveI : Fact p.Prime := ⟨hpp⟩
  -- `p ∣ |P|` (since `|P| = p`) and `P ≤ M`, so `p ∣ |M|`.
  have hpdvdP : p ∣ Nat.card ↥P := by
    obtain ⟨_, hPcard⟩ := hP
    rw [hPcard, pow_one]
  have hpM : p ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpp, hpdvdP.trans (Subgroup.card_dvd_of_le hPM), Nat.card_pos.ne'⟩
  -- `p ∤ [M : K.subgroupOf M]` (Hall), so `p ∣ |K.subgroupOf M|`, contradicting `K = ⊥`.
  have hpidx : ¬ p ∣ (K.subgroupOf M).index := fun hdvd =>
    hK.2 p (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Subgroup.index_ne_zero_of_finite⟩) hp
  have hpKcard : p ∣ Nat.card ↥(K.subgroupOf M) := by
    have hsplit : Nat.card ↥(K.subgroupOf M) * (K.subgroupOf M).index = Nat.card ↥M :=
      Subgroup.card_mul_index _
    rcases (Nat.Prime.dvd_mul hpp).mp (hsplit ▸ (Nat.dvd_of_mem_primeFactors hpM)) with h | h
    · exact h
    · exact absurd h hpidx
  rw [hKbot, Subgroup.bot_subgroupOf, Subgroup.card_bot] at hpKcard
  exact (Nat.Prime.one_lt hpp).ne' (Nat.dvd_one.mp hpKcard)

/-- **`K = ⊥ → U` is a `σ(M)'`-complement and `M = U ⊔ M_σ`** (`§14`-independent Hall complement).
When `κ(M) = ∅` (i.e. `K = ⊥`), `(κ(M) ∪ σ(M))' = σ(M)'`, so `U ≤ M` is a `σ(M)'`-Hall subgroup of
`M`; it must coincide with the §12 complement `E` (both `σ(M)'`-Hall in `M`, with `U ≤ E`), and
`M_σ ⊔ E = M`.  Returns the `SubgroupESetup` exhibiting `U` as the complement (`E = U`), which
also feeds the type-`F` half of Lemma 15.1(d)(e) (Theorem 12.12 with `E := U`). -/
theorem subgroupESetup_of_isHall_kappa_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) (hKbot : K = ⊥)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∃ E₁ E₂ E₃ : Subgroup G, OddOrder.BG.Ch3.S12.SubgroupESetup M U E₁ E₂ E₃ := by
  classical
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσ
  have hF : S14.IsTypeF M := isTypeF_of_isHall_kappa_eq_bot hKM hK hKbot
  have hκ : S14.kappa M = ∅ := hF
  -- `U` is a `σ'`-Hall subgroup of `M`.
  have hUσ' : Ch03.IsHallSubgroup (σᶜ) (U.subgroupOf M) := by
    have heq : (S14.kappa M ∪ σ)ᶜ = σᶜ := by rw [hκ, Set.empty_union]
    rwa [heq] at hU
  have hU_pi : Subgroup.IsPiSubgroup (σᶜ) U := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at hp
    exact hUσ'.1 p hp
  -- §12 complement `E ⊇ U`, `σ'`-Hall.
  obtain ⟨E, E₁, E₂, E₃, hsetup, hUE, hE_pi⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hUM hU_pi
  -- `U = E`:  `E` is a `σ'`-group, `U` is `σ'`-Hall, and `U ≤ E`, so `|E| ∣ |U|` and `|U| ∣ |E|`.
  have hUEeq : U = E := by
    have hEpi : Ch03.Subgroup.IsPiGroup (σᶜ) (E.subgroupOf M) := by
      intro q hq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv] at hq
      exact hE_pi q hq
    have hEdvdU : Nat.card ↥E ∣ Nat.card ↥U := by
      have hd := hUσ'.card_dvd_of_isPiGroup hEpi
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at hd
    exact Subgroup.eq_of_le_of_card_ge hUE
      (Nat.dvd_antisymm hEdvdU (Subgroup.card_dvd_of_le hUE)).le
  -- transport the `SubgroupESetup` from `E` to `U`.
  exact ⟨E₁, E₂, E₃, hUEeq ▸ hsetup⟩

/-! ## Lemma 15.1: the `U M_sigma` auxiliary structure -/

/-- **The three Hall factors `K`, `U`, `M_σ` partition `|M|`** (`§14`-independent counting helper).
With `K` a `κ(M)`-Hall, `U` a `(κ(M) ∪ σ(M))'`-Hall, and `M_σ` the `σ(M)`-Hall of `M`, the three
prime sets `κ`, `(κ ∪ σ)'`, `σ` are pairwise disjoint and cover every prime, so the orders multiply
to `|M|`.  Proven by prime-by-prime factorization: each prime `p` of `|M|` lies in exactly one of
the three sets, and the corresponding Hall subgroup carries the full `p`-part (its index is a
`p'`-number). -/
theorem card_mul_card_mul_card_eq_of_three_hall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    Nat.card ↥(K.subgroupOf M) * Nat.card ↥(U.subgroupOf M) *
      Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) = Nat.card ↥M := by
  classical
  set a := Nat.card ↥(K.subgroupOf M) with ha
  set b := Nat.card ↥(U.subgroupOf M) with hb
  set c := Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) with hc
  set n := Nat.card ↥M with hn
  have hMσ : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M)
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
  have hane : a ≠ 0 := Nat.card_pos.ne'
  have hbne : b ≠ 0 := Nat.card_pos.ne'
  have hcne : c ≠ 0 := Nat.card_pos.ne'
  have hnne : n ≠ 0 := Nat.card_pos.ne'
  -- Each Hall card divides `|M|`.
  have hadvd : a ∣ n := Subgroup.card_subgroup_dvd_card _
  have hbdvd : b ∣ n := Subgroup.card_subgroup_dvd_card _
  have hcdvd : c ∣ n := Subgroup.card_subgroup_dvd_card _
  -- Prime-set membership of the three Hall cards.
  have hUprimes_compl : ∀ p ∈ b.primeFactors, p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    hU.1
  have hUprimes_notκ : ∀ p ∈ b.primeFactors, p ∉ S14.kappa M := fun p hp hpκ =>
    hUprimes_compl p hp (Or.inl hpκ)
  have hUprimes_notσ : ∀ p ∈ b.primeFactors, p ∉ OddOrder.BG.Ch3.S10.sigma M := fun p hp hpσ =>
    hUprimes_compl p hp (Or.inr hpσ)
  have hKprimes_notσ : ∀ p ∈ a.primeFactors, p ∉ OddOrder.BG.Ch3.S10.sigma M := fun p hp =>
    S14.kappa_subset_sigmaCompl (hK.1 p hp)
  -- Pairwise coprimality of the three Hall cards (disjoint prime sets).
  have hcop_ab : Nat.Coprime a b :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := S14.kappa M) hane hbne hK.1
      hUprimes_notκ
  have hcop_ac : Nat.Coprime a c :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := OddOrder.BG.Ch3.S10.sigma M) hcne hane hMσ.1 hKprimes_notσ |>.symm
  have hcop_bc : Nat.Coprime b c :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := OddOrder.BG.Ch3.S10.sigma M) hcne hbne hMσ.1 hUprimes_notσ |>.symm
  -- `a * b * c ∣ n` from pairwise coprimality + each `∣ n`.
  have habc_dvd : a * b * c ∣ n :=
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_mul_iff_left.mpr ⟨hcop_ac, hcop_bc⟩)
      (hcop_ab.mul_dvd_of_dvd_of_dvd hadvd hbdvd) hcdvd)
  -- `n ∣ a * b * c` by prime-by-prime factorization: each prime of `n` lies in `κ`, `σ`, or
  -- `(κ ∪ σ)'`, and the corresponding Hall subgroup carries its full `p`-part.
  have hn_dvd : n ∣ a * b * c := by
    rw [← Nat.factorization_prime_le_iff_dvd hnne (mul_ne_zero (mul_ne_zero hane hbne) hcne)]
    intro p hp
    rw [Nat.factorization_mul (mul_ne_zero hane hbne) hcne,
      Nat.factorization_mul hane hbne, Finsupp.add_apply, Finsupp.add_apply]
    -- For a Hall `π`-subgroup `H` of `M` with `p ∉ index`, `n.factorization p = (card H).factor p`.
    -- Choose the Hall whose prime set contains `p`.
    by_cases hpκ : p ∈ S14.kappa M
    · -- `p ∈ κ`: `K` carries the `p`-part.
      have hpidx : ¬ p ∣ (K.subgroupOf M).index := fun hd =>
        hK.2 p (Nat.mem_primeFactors.mpr ⟨hp, hd, Subgroup.index_ne_zero_of_finite⟩) hpκ
      have hsplit : a * (K.subgroupOf M).index = n := Subgroup.card_mul_index _
      have : n.factorization p = a.factorization p := by
        rw [← hsplit, Nat.factorization_mul hane (Subgroup.index_ne_zero_of_finite),
          Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpidx, add_zero]
      omega
    · by_cases hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M
      · -- `p ∈ σ`: `M_σ` carries the `p`-part.
        have hpidx : ¬ p ∣ ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index := fun hd =>
          hMσ.2 p (Nat.mem_primeFactors.mpr ⟨hp, hd, Subgroup.index_ne_zero_of_finite⟩) hpσ
        have hsplit : c * ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index = n :=
          Subgroup.card_mul_index _
        have : n.factorization p = c.factorization p := by
          rw [← hsplit, Nat.factorization_mul hcne (Subgroup.index_ne_zero_of_finite),
            Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpidx, add_zero]
        omega
      · -- `p ∈ (κ ∪ σ)'`: `U` carries the `p`-part.
        have hpcompl : p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
          Set.mem_compl (fun h => h.elim hpκ hpσ)
        have hpidx : ¬ p ∣ (U.subgroupOf M).index := fun hd =>
          hU.2 p (Nat.mem_primeFactors.mpr ⟨hp, hd, Subgroup.index_ne_zero_of_finite⟩) hpcompl
        have hsplit : b * (U.subgroupOf M).index = n := Subgroup.card_mul_index _
        have : n.factorization p = b.factorization p := by
          rw [← hsplit, Nat.factorization_mul hbne (Subgroup.index_ne_zero_of_finite),
            Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpidx, add_zero]
        omega
  exact Nat.dvd_antisymm habc_dvd hn_dvd

/-- **BG Lemma 15.1(b)** (mmd L4169): for a maximal `M` with nontrivial κ-Hall `K`,
`M' = U M_σ` and `U` is abelian (`U` a `(κ∪σ)'`-Hall subgroup of `M`).

Proof: `K ≠ ⊥` forces `IsTypeP M`, so Theorem 14.7(h) (`typeP_duality`) gives that `M'` complements
the κ-Hall `K` in `M`, with `|M'|`, `|K|` coprime.  Then:
* `U ⊓ M_σ = ⊥` (coprime orders: `|U|` is a `(κ∪σ)'`-number, `|M_σ|` a `σ`-number);
* `M_σ ≤ M'` (`Msigma_le_derived`) and `U ≤ M'` (the κ'-number `|U|` is coprime to the κ-number
  index `[M:M'] = |K|`, so `U ≤ M'` via `le_of_coprime_index`); hence `U M_σ ≤ M'`;
* `|M'| = |U|·|M_σ|` from the three-Hall partition `|M| = |K|·|U|·|M_σ|`
  (`card_mul_card_mul_card_eq_of_three_hall`) and the complement `|M'|·|K| = |M|`; combined with
  `U ⊓ M_σ = ⊥` (so `|U M_σ| = |U|·|M_σ|`) this gives `|U M_σ| = |M'|`, hence equality;
* `U` abelian: `⁅U,U⁆ ≤ U ⊓ M_σ = ⊥` (using `U ≤ M'` and `M'' ≤ M_σ` from
  `derivedDerived_le_Msigma`), so `commutator ↥U = ⊥`. -/
theorem typeP_hall_derived_eq_and_abelian [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧ IsMulCommutative ↥U := by
  classical
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `IsTypeP M` from `K ≠ ⊥`.
  have hKofne : K.subgroupOf M ≠ ⊥ := by
    rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hKne (hd.eq_bot_of_le hKM)
  have hP : S14.IsTypeP M := isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK hKofne
  -- Theorem 14.7(h): `M'` complements `K` in `M`, with coprime orders.
  obtain ⟨hcompl, _hcoprime, _⟩ := typeP_duality hG hM hP hKM hK rfl
  -- `M_σ ≤ M'`.
  have hMσ_le_M' : Mσ ≤ derivedInG M := OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  -- `M_σ` is `σ`-Hall in `M`.
  have hMσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (Mσ.subgroupOf M) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
  -- `U ⊓ M_σ = ⊥`: `|U|` is a `(κ∪σ)'`-number, `|M_σ|` a `σ`-number, so coprime.
  have hUMσ_bot : U ⊓ Mσ = ⊥ := by
    have hcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥Mσ) := by
      refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
        (π := (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) Nat.card_pos.ne' Nat.card_pos.ne'
        ?_ ?_
      · intro p hp
        exact hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
      · intro p hp hpcompl
        have hpMσ : p ∈ (Nat.card ↥(Mσ.subgroupOf M)).primeFactors := by
          rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le
              M)).toEquiv]
        exact hpcompl (Or.inr (hMσHall.1 p hpMσ))
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  -- `U ≤ M'`: `|U|` (a κ'-number) is coprime to `[M:M'] = |K|` (a κ-number).
  have hU_le_M' : U ≤ derivedInG M := by
    have hM'norm : ((derivedInG M).subgroupOf M).Normal := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
      infer_instance
    haveI := hM'norm
    -- `[M:M'] = |K|` (index of the complement factor).
    have hidx : ((derivedInG M).subgroupOf M).index = Nat.card ↥(K.subgroupOf M) :=
      hcompl.symm.index_eq_card
    -- `Coprime |U.subgroupOf M| [M:M']`.
    have hcop : Nat.Coprime (Nat.card ↥(U.subgroupOf M)) ((derivedInG M).subgroupOf M).index := by
      rw [hidx]
      refine (Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := S14.kappa M)
        Nat.card_pos.ne' Nat.card_pos.ne' hK.1 ?_).symm
      intro p hp hpκ
      exact hU.1 p hp (Or.inl hpκ)
    have hUsub_le : U.subgroupOf M ≤ (derivedInG M).subgroupOf M :=
      S14.le_of_coprime_index (N := (derivedInG M).subgroupOf M) (H := U.subgroupOf M) hcop
    -- Push back to the ambient via `M.subtype`.
    calc U = (U.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hUM).symm
      _ ≤ ((derivedInG M).subgroupOf M).map M.subtype := Subgroup.map_mono hUsub_le
      _ = derivedInG M := Subgroup.map_subgroupOf_eq_of_le hM'le
  -- `U M_σ ≤ M'`.
  have hsup_le : U ⊔ Mσ ≤ derivedInG M := sup_le hU_le_M' hMσ_le_M'
  -- Cardinalities.  `|M'| = |U|·|M_σ|`.
  have hcardM' : Nat.card ↥(derivedInG M) = Nat.card ↥U * Nat.card ↥Mσ := by
    -- complement: `|M'.subgroupOf M| · |K.subgroupOf M| = |M|`.
    have hcompl_card : Nat.card ↥((derivedInG M).subgroupOf M) * Nat.card ↥(K.subgroupOf M)
        = Nat.card ↥M := hcompl.card_mul
    -- three-Hall partition: `|K|·|U|·|M_σ| = |M|` (subgroupOf).
    have hthree := card_mul_card_mul_card_eq_of_three_hall hG hM hK hU
    -- transport subgroupOf cards to ambient cards.
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv] at hcompl_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
      at hthree
    -- `|M'| · |K| = |M| = |K| · |U| · |M_σ|`, cancel `|K|`.
    have hKpos : 0 < Nat.card ↥(K.subgroupOf M) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hKpos
    rw [hcompl_card, ← hthree]
    ring
  -- `|U M_σ| = |U|·|M_σ|` (disjoint, `U ≤ M ≤ N_G(M_σ)`).
  have hUnorm : U ≤ Subgroup.normalizer (Mσ : Set G) := by
    refine le_trans hUM ?_
    rw [hMσdef, OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  have hcardSup : Nat.card ↥(U ⊔ Mσ) = Nat.card ↥U * Nat.card ↥Mσ :=
    card_sup_eq_mul_of_le_normalizer_of_disjoint hUnorm hUMσ_bot
  -- `M' = U M_σ` by `le_antisymm` + equal cardinality.
  have hderiv_eq : derivedInG M = U ⊔ Mσ := by
    refine (Subgroup.eq_of_le_of_card_ge hsup_le ?_).symm
    rw [hcardSup, hcardM']
  refine ⟨hderiv_eq, ?_⟩
  -- `U` abelian: `derivedInG U ≤ U ⊓ M_σ = ⊥`, so `commutator ↥U = ⊥`.
  have hUU_le_M'' : derivedInG U ≤ Mσ :=
    (OddOrder.BG.Ch3.S12.derivedInG_le_derivedInG hU_le_M').trans
      (derivedDerived_le_Msigma hG hM)
  have hUU_le_U : derivedInG U ≤ U := Subgroup.map_subtype_le (commutator ↥U)
  have hUU_bot : derivedInG U = ⊥ := le_bot_iff.mp (hUMσ_bot ▸ le_inf hUU_le_U hUU_le_M'')
  -- `derivedInG U = (commutator ↥U).map U.subtype = ⊥` and `U.subtype` injective ⟹ `comm ↥U = ⊥`.
  have hcomm_bot : commutator ↥U = ⊥ := by
    have := hUU_bot
    rw [derivedInG, Subgroup.map_eq_bot_iff, U.ker_subtype] at this
    exact le_bot_iff.mp this
  exact (commutator_eq_bot_iff ↥U).mp hcomm_bot

/-- **BG Lemma 15.1(d)** (mmd L4171): the subgroup `⟨C_U(x) | x ∈ M_σ#⟩` generated by the
centralizers in `U` of the nonidentity `σ`-elements is abelian.

Proof by the `K = ⊥` case split:

* `K ≠ ⊥`: `U` itself is abelian (`typeP_hall_derived_eq_and_abelian`, mmd 15.1(b)); the
  generated subgroup `centralizerGeneratedBySigma M U ≤ U` (a `sSup` of subgroups `U ⊓ C(x) ≤ U`),
  so a subgroup of an abelian group is abelian.
* `K = ⊥`: `M` is type `F`, so `κ(M) = ∅` and `U` is the `σ`-complement `E` of a §12 `E`-setup
  (`subgroupESetup_of_isHall_kappa_eq_bot`).  Theorem 12.12(a)
  (`frobenius_factorization_of_regular`) supplies an abelian normal subgroup `A₀ ≤ U` swallowing
  every `C_U(x)` (`x ∈ M_σ#`); its regularity hypothesis `hreg` is discharged via Lemma 14.1
  (`msigma_structure_of_notMem_sigma_kappa`): a prime-order power `f` of a `(τ₁∪τ₃)`-element
  `e ∈ U#` generates `A = ⟨f⟩ ∈ ℰ_p^{r_p(M)}(M)` with `p ∉ σ(M)` (`τ₁∪τ₃ ⊆ σ′`) and
  `p ∉ κ(M) = ∅`, giving `M_σ ⊓ C(A) = ⊥`, whence `M_σ ⊓ C(e) ≤ M_σ ⊓ C(f) = ⊥`.  Then
  `centralizerGeneratedBySigma M U ≤ A₀` (`sSup` of swallowed generators), so abelian. -/
theorem typeP_centralizerGeneratedBySigma_isMulCommutative [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    IsMulCommutative ↥(centralizerGeneratedBySigma M U) := by
  classical
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  by_cases hKbot : K = ⊥
  · -- **Case `K = ⊥`**: `U` is the `σ`-complement `E` of a §12 `E`-setup; Theorem 12.12(a).
    have hκ : S14.kappa M = ∅ := isTypeF_of_isHall_kappa_eq_bot hKM hK hKbot
    obtain ⟨E₁, E₂, E₃, hsetup⟩ :=
      subgroupESetup_of_isHall_kappa_eq_bot hG hM hKM hUM hK hKbot hU
    -- Discharge the regularity hypothesis of Theorem 12.12 via Lemma 14.1.
    have hreg : ∀ e ∈ U, e ≠ 1 →
        (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
          Mσ ⊓ Subgroup.centralizer ({e} : Set G) = ⊥ := by
      intro e heU hene hprimes
      -- pick a prime divisor `p` of `orderOf e`; then `p ∈ τ₁(M) ∪ τ₃(M)`.
      have hord1 : orderOf e ≠ 1 := fun hc => hene (orderOf_eq_one_iff.mp hc)
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord1
      haveI : Fact p.Prime := ⟨hp⟩
      have hpτ : p ∈ tau1 M ∪ tau3 M :=
        hprimes p (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, (orderOf_pos e).ne'⟩)
      -- the prime-order power `f = e^(orderOf e / p)` and its cyclic group `A = ⟨f⟩`.
      set f : G := e ^ (orderOf e / p) with hfdef
      have hford : orderOf f = p := orderOf_pow_orderOf_div (orderOf_pos e).ne' hpdvd
      have hfU : f ∈ U := U.pow_mem heU _
      have hfM : f ∈ M := hUM hfU
      set A : Subgroup G := Subgroup.zpowers f with hAdef
      have hAcard : Nat.card ↥A = p := by rw [hAdef, Nat.card_zpowers]; exact hford
      have hAelem : A.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hAcard
      have hAM : A ≤ M := by rw [hAdef, Subgroup.zpowers_le]; exact hfM
      -- Lemma 14.1 hypotheses: `p ∈ π(M)`, `p ∉ σ(M)` (`τ₁∪τ₃ ⊆ σ′`), `p ∉ κ(M) = ∅`.
      have hpπ : p ∈ S14.piSet M :=
        Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans ((U.orderOf_dvd_natCard heU).trans
          (Subgroup.card_dvd_of_le hUM)), Nat.card_pos.ne'⟩
      have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
        hpτ.elim (fun h => tau1_subset_sigma_compl M h) (fun h => tau3_subset_sigma_compl M h)
      have hpκ : p ∉ S14.kappa M := by rw [hκ]; simp
      -- maximal-rank elementary abelian witness: `r_p(M) = 1`, so `A ∈ ℰ_p^{r_p(M)}(M)`.
      have hr1 : pRank ↥M p = 1 :=
        hpτ.elim tau1_pRank_eq_one tau3_pRank_eq_one
      have hAr : A ∈ elemAbelianOfRank G p (pRank ↥M p) := by
        rw [hr1, mem_elemAbelianOfRank]
        exact ⟨hAelem, by rw [hAcard, pow_one]⟩
      -- Lemma 14.1: `M_σ ⊓ C(A) = ⊥`; antitonicity `C(e) ≤ C(f) = C(A)` lifts it to `e`.
      obtain ⟨_, hCA, _⟩ :=
        S14.msigma_structure_of_notMem_sigma_kappa hG hM hpπ hpσ hpκ hAr hAM
      -- `C(A) = C(f)` and `C(e) ≤ C(f)`: centralizing `e` centralizes its power `f = e^k`.
      have hCfA : Subgroup.centralizer (A : Set G) = Subgroup.centralizer ({f} : Set G) := by
        rw [hAdef, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      have hCef : Subgroup.centralizer ({e} : Set G) ≤ Subgroup.centralizer ({f} : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
        rw [hfdef]
        exact (show Commute x e from hx).pow_right _
      rw [eq_bot_iff, ← hCA, hCfA]
      exact inf_le_inf_left _ hCef
    -- Theorem 12.12(a): abelian normal `A₀ ≤ U` swallowing every `C_U(x)`.
    obtain ⟨⟨A₀, hA₀le, hA₀ab, _hA₀norm, hA₀swallow⟩, _⟩ :=
      frobenius_factorization_of_regular hG hsetup hreg
    -- `centralizerGeneratedBySigma M U ≤ A₀`, so abelian.
    refine isMulCommutative_of_le hA₀ab ?_
    rw [centralizerGeneratedBySigma]
    refine sSup_le ?_
    rintro C ⟨x, hx, rfl⟩
    obtain ⟨hxMσ, hxne⟩ := hx
    exact hA₀swallow x hxMσ (by simpa using hxne)
  · -- **Case `K ≠ ⊥`**: `U` is abelian; the generated subgroup is `≤ U`.
    obtain ⟨_, hUab⟩ := typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKbot hK hU
    refine isMulCommutative_of_le hUab ?_
    rw [centralizerGeneratedBySigma]
    refine sSup_le ?_
    rintro C ⟨x, _, rfl⟩
    exact inf_le_left

/-- **`E`-setup-free Frobenius packaging** (generalizes `isFrobeniusGroup_of_regular`,
`S12_Theorem1212`): for a maximal `M` and a nonidentity `U₀ ≤ M` with `M_σ ⊓ U₀ = 1` acting
regularly on `M_σ` (`M_σ ⊓ C_G(a) = 1` for `a ∈ U₀#`), the product `M_σ U₀` is a Frobenius group
with kernel `M_σ` and complement `U₀`.  The proof of `isFrobeniusGroup_of_regular` only uses the
`SubgroupESetup` via `h.mem_maximal`, `h.E_le` and `h.E_compl_inf`; here those become the explicit
`hM`, `hU0M` and `hU0inf`, so the `K ≠ ⊥` (type-`P`) case of Lemma 15.1(e) can reuse it with
`U₀ ≤ U ≤ M` without aligning a `σ`-complement. -/
theorem isFrobeniusGroup_of_regular_le_maximal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hU0M : U0 ≤ M) (hU0ne : U0 ≠ ⊥)
    (hU0inf : OddOrder.BG.Ch3.S10.Msigma M ⊓ U0 = ⊥)
    (hreg₀ : ∀ a ∈ U0, a ≠ 1 →
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({a} : Set G) = ⊥) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(OddOrder.BG.Ch3.S10.Msigma M ⊔ U0)
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (OddOrder.BG.Ch3.S10.Msigma M ⊔ U0))
      (U0.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M ⊔ U0)) := by
  have hMσne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ := OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
  haveI hMσM_normal : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
    rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have hM_le_N : M ≤ Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch3.S10.Msigma_le M)).mp hMσM_normal
  have hsup_le_M : OddOrder.BG.Ch3.S10.Msigma M ⊔ U0 ≤ M :=
    sup_le (OddOrder.BG.Ch3.S10.Msigma_le M) hU0M
  have hsup_le_N : OddOrder.BG.Ch3.S10.Msigma M ⊔ U0 ≤
      Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) :=
    hsup_le_M.trans hM_le_N
  refine
    { isNormal := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hsup_le_N
      isComplement := ?_
      ne_bot_kernel := ?_
      ne_bot_complement := ?_
      conj_frobenius := ?_ }
  · haveI : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf
        (OddOrder.BG.Ch3.S10.Msigma M ⊔ U0)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hsup_le_N
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff]
      have hinf : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf
            (OddOrder.BG.Ch3.S10.Msigma M ⊔ U0) ⊓
            U0.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M ⊔ U0)
          = (OddOrder.BG.Ch3.S10.Msigma M ⊓ U0).subgroupOf
            (OddOrder.BG.Ch3.S10.Msigma M ⊔ U0) := rfl
      rw [hinf, hU0inf, Subgroup.bot_subgroupOf]
    · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
        Subgroup.subgroupOf_self, Subgroup.coe_top]
  · rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hMσne (hd.eq_bot_of_le le_sup_left)
  · rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hU0ne (hd.eq_bot_of_le le_sup_right)
  · intro a ha hane n hn hne hfix
    have ha_mem : (a : G) ∈ U0 := Subgroup.mem_subgroupOf.mp ha
    have hn_mem : (n : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := Subgroup.mem_subgroupOf.mp hn
    have ha_ne : (a : G) ≠ 1 := fun hc => hane (by exact_mod_cast hc)
    have hfixG : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      have := Subtype.ext_iff.mp hfix
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    have hncent : (n : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff] at hm; subst hm
      exact mul_inv_eq_iff_eq_mul.mp hfixG
    have hmem : (n : G) ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓
        Subgroup.centralizer ({(a : G)} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hn_mem, hncent⟩
    rw [hreg₀ (a : G) ha_mem ha_ne, Subgroup.mem_bot] at hmem
    exact hne (by exact_mod_cast hmem)

/-- **Frobenius-factor assembly engine** (BG Lemma 15.1(e), `K ≠ ⊥` core).  Given an abelian
`U ≤ M` with `M_σ ⊓ U = 1`, and for **each** prime `p ∣ |U|` a `p`-subgroup `Z_p ≤ U` that
realizes the `p`-part of `exp U` (`v_p(exp U) ≤ v_p(exp Z_p)`) and acts regularly on `M_σ`, the
internal direct product `U₀ = ⊔_p Z_p` has `exp U₀ = exp U` and `U₀ M_σ` is a Frobenius group with
kernel `M_σ` and complement `U₀`.

Because `U` is abelian, every internal-direct-product hypothesis is automatic (`U ≤ N_G(Z_p)` from
`U ≤ C_G(Z_p)`); regularity propagates from prime-order elements (each lands in one `Z_p` by
`mem_Z_of_orderOf_prime_mem`); the exponent is matched prime-by-prime
(`exponent_eq_of_forall_factorization_le`); and `isFrobeniusGroup_of_regular_le_maximal` packages
the result.  This isolates the type-`P` content of Lemma 15.1(e) to constructing the per-prime
`Z_p` (`τ₁∪τ₃`: cyclic `Sylow_p(U)`; `τ₂`: a regular cyclic line). -/
theorem frobenius_factor_of_regular_components [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hUM : U ≤ M) (hUne : U ≠ ⊥)
    (hUab : IsMulCommutative ↥U)
    (hUinf : OddOrder.BG.Ch3.S10.Msigma M ⊓ U = ⊥)
    (hcomp : ∀ p ∈ (Nat.card ↥U).primeFactors, ∃ Z : Subgroup G,
      Z ≤ U ∧ IsPGroup p ↥Z ∧
        (Monoid.exponent ↥U).factorization p ≤ (Monoid.exponent ↥Z).factorization p ∧
        (∀ z ∈ Z, z ≠ 1 →
          OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({z} : Set G) = ⊥)) :
    ∃ U0 : Subgroup G, U0 ≤ U ∧ Monoid.exponent ↥U0 = Monoid.exponent ↥U ∧
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M)
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M))
        (U0.subgroupOf (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M)) := by
  classical
  set T := (Nat.card ↥U).primeFactors with hTdef
  choose! Z hZU hZpg hZexp hZreg using hcomp
  set U0 : Subgroup G := T.sup Z with hU0def
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  -- `U` abelian ⟹ `U ≤ C_G(U) ≤ C_G(Z_p) ≤ N_G(Z_p)`.
  have hUcentU : U ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hUab
  have hUnorm : ∀ p ∈ T, U ≤ Subgroup.normalizer ((Z p : Subgroup G) : Set G) := fun p hp =>
    ((hUcentU.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hZU p hp)))).trans
      (Subgroup.centralizer_le_normalizer _))
  have hU0U : U0 ≤ U := Finset.sup_le hZU
  have hU0inf : OddOrder.BG.Ch3.S10.Msigma M ⊓ U0 = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left _ hU0U).trans hUinf.le)
  -- **Exponent**: `exp U₀ = exp U`.
  have hexp : Monoid.exponent ↥U0 = Monoid.exponent ↥U := by
    refine exponent_eq_of_forall_factorization_le hU0U fun r hrp => ?_
    haveI : Fact r.Prime := ⟨hrp⟩
    by_cases hrT : r ∈ T
    · obtain ⟨g, hg⟩ := hrp.exists_orderOf_eq_pow_factorization_exponent ↥(Z r)
      have hZrU0 : Z r ≤ U0 := Finset.le_sup hrT
      refine ⟨Subgroup.inclusion hZrU0 g, ?_⟩
      rw [orderOf_injective (Subgroup.inclusion hZrU0) (Subgroup.inclusion_injective _) g, hg,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.Prime.factorization_self hrp,
        mul_one]
      exact hZexp r hrT
    · have hrnU : ¬ r ∣ Nat.card ↥U := fun hd =>
        hrT (Nat.mem_primeFactors.mpr ⟨hrp, hd, Nat.card_pos.ne'⟩)
      have h0 : (Monoid.exponent ↥U).factorization r = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        exact Or.inr (Or.inl fun hd => hrnU (hd.trans Group.exponent_dvd_nat_card))
      exact ⟨1, by rw [h0]; exact Nat.zero_le _⟩
  have hU0ne : U0 ≠ ⊥ := by
    intro hbot
    refine hUne (Subgroup.eq_bot_iff_forall _ |>.mpr fun x hx => ?_)
    haveI : Subsingleton ↥U :=
      Monoid.exp_eq_one_iff.mp (by rw [← hexp, hbot]; exact Monoid.exp_eq_one_of_subsingleton)
    have hx1 : (⟨x, hx⟩ : ↥U) = 1 := Subsingleton.elim _ _
    simpa using Subtype.ext_iff.mp hx1
  -- **Regularity**: every nonidentity element of `U₀` is regular on `M_σ`.
  have hU0reg : ∀ a ∈ U0, a ≠ 1 →
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by
    refine inf_centralizer_eq_bot_of_forall_prime_order ?_
    intro a haU0 harp
    have haU : a ∈ U := hU0U haU0
    have hrT : orderOf a ∈ T := Nat.mem_primeFactors.mpr
      ⟨harp, (Subgroup.orderOf_coe (⟨a, haU⟩ : ↥U)) ▸ orderOf_dvd_natCard _, Nat.card_pos.ne'⟩
    have haZr : a ∈ Z (orderOf a) :=
      mem_Z_of_orderOf_prime_mem T Z hTp hZU hUnorm hZpg hrT haU0 rfl
    have hane : a ≠ 1 := fun hc => by
      rw [hc, orderOf_one] at harp; exact harp.ne_one rfl
    exact hZreg (orderOf a) hrT a haZr hane
  refine ⟨U0, hU0U, hexp, ?_⟩
  rw [show U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M
      = OddOrder.BG.Ch3.S10.Msigma M ⊔ U0 from sup_comm _ _]
  exact isFrobeniusGroup_of_regular_le_maximal hG hM (hU0U.trans hUM) hU0ne hU0inf hU0reg

/-- **Per-prime regular component** for the type-`P` Frobenius factor (BG Lemma 15.1(e), `K ≠ ⊥`):
for each prime `p ∣ |U|` (with `U` the abelian `(κ∪σ)'`-Hall of a maximal `M`), `Sylow_p(U)`
contains a `p`-subgroup `Z` realizing the `p`-part of `exp U` and acting regularly on `M_σ`.  This
is the single mathematical kernel of the `K ≠ ⊥` branch; the assembly into `U₀ = ⊔_p Z_p` is
`frobenius_factor_of_regular_components`.

Proof (BG mmd 4178 + Theorem 12.12 `C_E(S)=E` argument), to be supplied:

* `p ∈ τ₁(M) ∪ τ₃(M)` (`r_p(M) = 1`): `Z = Sylow_p(U)` is cyclic; regularity is Lemma 14.1
  (`Ω₁(Z) ∈ ℰ_p¹(M)`, `p ∉ σ ∪ κ`), the same discharge as the `K = ⊥` branch.
* `p ∈ τ₂(M)` (`r_p(M) = 2`): since `U` is abelian, `C_U(Sylow_p(U)) = U`, so we are always in the
  "easy" `C_E(S) = E` case.  Abelian `Sylow_p(G)`: `Sylow_p(U) = Sylow_p(G) ≤ M` (full-Sylow-in-`G`
  via `centralizer_le_E_of_tau2`), and `exists_cyclic_Enormal_regular_of_CES_eq` supplies the
  regular cyclic line.  Nonabelian `Sylow_p(G)`: `Sylow_p(U) = C_S(A) = A₀ × Z` (Theorem 12.7,
  mmd 3237) and `Z` is the regular cyclic factor of full exponent (`A₀` has order `p`). -/
theorem typeP_hall_regular_component_at_prime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hUM : U ≤ M) (hUab : IsMulCommutative ↥U)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} (hp : p ∈ (Nat.card ↥U).primeFactors) :
    ∃ Z : Subgroup G, Z ≤ U ∧ IsPGroup p ↥Z ∧
      (Monoid.exponent ↥U).factorization p ≤ (Monoid.exponent ↥Z).factorization p ∧
      (∀ z ∈ Z, z ≠ 1 →
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({z} : Set G) = ⊥) := by
  classical
  haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  -- `p ∈ π(U) ⟹ p ∉ σ(M) ∪ κ(M)` (U is a `(κ∪σ)'`-Hall).
  have hpcompl : p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
  have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := fun h => hpcompl (Set.mem_union_right _ h)
  have hpκ : p ∉ S14.kappa M := fun h => hpcompl (Set.mem_union_left _ h)
  have hpdvdM : p ∣ Nat.card ↥M :=
    (Nat.dvd_of_mem_primeFactors hp).trans (Subgroup.card_dvd_of_le hUM)
  have hpπ : p ∈ S14.piSet M := Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvdM, Nat.card_pos.ne'⟩
  -- **Linchpin**: an `E`-setup of `M` with `U ≤ E` (`U` is a `σ'`-subgroup).
  have hUpi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) U := by
    intro q hq
    exact fun hqσ => (hU.1 q (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]))
      (Set.mem_union_right _ hqσ)
  obtain ⟨E, E₁, E₂, E₃, hsetup, hUE, _hEpi⟩ :=
    exists_subgroupESetup_with_le hG hM hUM hUpi
  have hpE : p ∈ (Nat.card ↥E).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out,
      (Nat.dvd_of_mem_primeFactors hp).trans (Subgroup.card_dvd_of_le hUE), Nat.card_pos.ne'⟩
  by_cases hpτ2 : p ∈ tau2 M
  · -- **τ₂ case** (`r_p(M) = 2`): the regular cyclic line in `Sylow_p(U)`.
    by_cases habel : ∀ Sp : Sylow p G, IsMulCommutative ↥(Sp : Subgroup G)
    · -- **abelian `Sylow_p(G)`**: `Sylow_p(U)` is a full `G`-Sylow, so the trimmed `C_E(S)=E`
      -- construction (`exists_regular_cyclic_in_abelianSylow_tau2`) supplies `Z ≤ Sylow_p(U) ≤ U`.
      -- `ν_p(|U|) = ν_p(|M|)` (`U` is the `(κ∪σ)'`-Hall, `p ∈ (κ∪σ)'`).
      have hUMfact : (Nat.card ↥U).factorization p = (Nat.card ↥M).factorization p := by
        have hmul := Subgroup.card_mul_index (U.subgroupOf M)
        have hcard_eqUM : Nat.card ↥(U.subgroupOf M) = Nat.card ↥U :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
        have hidx : ((U.subgroupOf M).index).factorization p = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          exact Or.inr (Or.inl fun hd => (hU.2 p (Nat.mem_primeFactors.mpr
            ⟨Fact.out, hd, Subgroup.index_ne_zero_of_finite⟩)) hpcompl)
        have hh := congrArg (fun n => n.factorization p) hmul
        simp only [Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply, hidx, add_zero] at hh
        rw [hcard_eqUM] at hh; exact hh
      -- `SUG = Sylow_p(U)` pushed into `G`.
      obtain ⟨SU⟩ : Nonempty (Sylow p ↥U) := inferInstance
      set SUG : Subgroup G := (SU : Subgroup ↥U).map U.subtype with hSUGdef
      have hSUG_U : SUG ≤ U := Subgroup.map_subtype_le _
      have hSUG_M : SUG ≤ M := hSUG_U.trans hUM
      have hSUGcard : Nat.card ↥SUG = p ^ (Nat.card ↥U).factorization p := by
        rw [hSUGdef, Subgroup.card_map_of_injective U.subtype_injective, SU.card_eq_multiplicity]
      have hSUGcardM : Nat.card ↥SUG = p ^ (Nat.card ↥M).factorization p := by
        rw [hSUGcard, hUMfact]
      have hSUGsubM_card : Nat.card ↥(SUG.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSUG_M).toEquiv]; exact hSUGcardM
      set SM : Sylow p ↥M := Sylow.ofCard (SUG.subgroupOf M) hSUGsubM_card with hSMdef
      have hpRankSUG : 2 ≤ pRank ↥SUG p := by
        have e1 := pRank_sylow_eq SM
        rw [hSMdef, Sylow.coe_ofCard] at e1
        have e2 : pRank ↥(SUG.subgroupOf M) p = pRank ↥SUG p :=
          le_antisymm
            (pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hSUG_M).toMonoidHom)
              (Subgroup.subgroupOfEquivOfLe hSUG_M).injective)
            (pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hSUG_M).symm.toMonoidHom)
              (Subgroup.subgroupOfEquivOfLe hSUG_M).symm.injective)
        have hr2 : pRank ↥M p = 2 := hpτ2.2
        omega
      -- a rank-2 `A ≤ SUG` (de-private `S12_Proposition1215`).
      obtain ⟨A, hA, hASUG⟩ := exists_mem_elemAbelianOfRank_two_le_of_two_le_pRank
        (Fact.out : p.Prime) hpRankSUG
      have hAE : A ≤ E := hASUG.trans (hSUG_U.trans hUE)
      -- **full `G`-Sylow**: `ν_p(|M|) = ν_p(|G|)` via abelian `S' ⊇ A` with `S' ≤ C_G(A) ≤ E ≤ M`.
      obtain ⟨S', hAS'⟩ := hA.1.isPGroup.exists_le_sylow
      have hS'M : (S' : Subgroup G) ≤ M :=
        ((le_centralizer_of_le_of_le (habel S') le_rfl hAS').trans
          (centralizer_le_E_of_tau2 hG hsetup hpτ2 hA hAE).1).trans hsetup.E_le
      have hMG : (Nat.card ↥M).factorization p ≤ (Nat.card G).factorization p :=
        (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
          (Subgroup.card_subgroup_dvd_card M) p
      have hGM : (Nat.card G).factorization p ≤ (Nat.card ↥M).factorization p := by
        have hdvd : Nat.card ↥(S' : Subgroup G) ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hS'M
        rw [S'.card_eq_multiplicity] at hdvd
        exact (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp hdvd
      have hfull : (Nat.card ↥M).factorization p = (Nat.card G).factorization p :=
        le_antisymm hMG hGM
      have hSUGfull : Nat.card ↥SUG = p ^ (Nat.card G).factorization p := by
        rw [hSUGcardM, hfull]
      set SG : Sylow p G := Sylow.ofCard SUG hSUGfull with hSGdef
      have hSGcoe : (SG : Subgroup G) = SUG := by rw [hSGdef, Sylow.coe_ofCard]
      have hSGab : IsMulCommutative ↥(SG : Subgroup G) := by
        rw [hSGcoe]
        exact Subgroup.le_centralizer_iff_isMulCommutative.mp
          (hSUG_U.trans ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hUab).trans
            (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hSUG_U))))
      obtain ⟨Z, hZS, _hZcyc, _hZne, hZexp, hZreg⟩ :=
        exists_regular_cyclic_in_abelianSylow_tau2 hG hsetup hpτ2 hA hAE
          (hSGcoe ▸ hASUG) (hSGcoe ▸ hSUG_M) hSGab
      have hZSUG : Z ≤ SUG := hSGcoe ▸ hZS
      refine ⟨Z, hZSUG.trans hSUG_U, (SG.isPGroup'.to_le hZS), ?_, hZreg⟩
      -- exponent: `exp Z = exp SUG`, and `ν_p(exp U) ≤ ν_p(exp SUG)` (`Sylow_p(U)`).
      have hSUGsubU : SUG.subgroupOf U = (SU : Subgroup ↥U) := by
        rw [hSUGdef, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective U.subtype_injective]
      have hSUGsubU_card : Nat.card ↥(SUG.subgroupOf U) = p ^ (Nat.card ↥U).factorization p := by
        rw [hSUGsubU, SU.card_eq_multiplicity]
      have hZexp' : Monoid.exponent ↥Z = Monoid.exponent ↥SUG := by rw [hZexp, hSGcoe]
      rw [hZexp']
      exact factorization_exponent_le_of_sylow hSUG_U hSUGsubU_card
    · -- **nonabelian `Sylow_p(G)`**: `Sylow_p(U) = C_{S'}(A) = A₀ ⊔ Z` (Lemma 10.13); `Z` is the
      -- regular cyclic factor (`Ω₁(Z) ≠ A₀`, regular by the canonical line's clause (c)).
      have hUMfact : (Nat.card ↥U).factorization p = (Nat.card ↥M).factorization p := by
        have hmul := Subgroup.card_mul_index (U.subgroupOf M)
        have hcard_eqUM : Nat.card ↥(U.subgroupOf M) = Nat.card ↥U :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
        have hidx : ((U.subgroupOf M).index).factorization p = 0 := by
          rw [Nat.factorization_eq_zero_iff]
          exact Or.inr (Or.inl fun hd => (hU.2 p (Nat.mem_primeFactors.mpr
            ⟨Fact.out, hd, Subgroup.index_ne_zero_of_finite⟩)) hpcompl)
        have hh := congrArg (fun n => n.factorization p) hmul
        simp only [Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply, hidx, add_zero] at hh
        rw [hcard_eqUM] at hh; exact hh
      obtain ⟨SU⟩ : Nonempty (Sylow p ↥U) := inferInstance
      set SUG : Subgroup G := (SU : Subgroup ↥U).map U.subtype with hSUGdef
      have hSUG_U : SUG ≤ U := Subgroup.map_subtype_le _
      have hSUG_M : SUG ≤ M := hSUG_U.trans hUM
      have hSUGcard : Nat.card ↥SUG = p ^ (Nat.card ↥U).factorization p := by
        rw [hSUGdef, Subgroup.card_map_of_injective U.subtype_injective, SU.card_eq_multiplicity]
      have hSUGcardM : Nat.card ↥SUG = p ^ (Nat.card ↥M).factorization p := by
        rw [hSUGcard, hUMfact]
      have hSUGpg : IsPGroup p ↥SUG := IsPGroup.of_card hSUGcard
      have hSUGsubM_card : Nat.card ↥(SUG.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSUG_M).toEquiv]; exact hSUGcardM
      set SM : Sylow p ↥M := Sylow.ofCard (SUG.subgroupOf M) hSUGsubM_card with hSMdef
      have hpRankSUG : 2 ≤ pRank ↥SUG p := by
        have e1 := pRank_sylow_eq SM
        rw [hSMdef, Sylow.coe_ofCard] at e1
        have e2 : pRank ↥(SUG.subgroupOf M) p = pRank ↥SUG p :=
          le_antisymm
            (pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hSUG_M).toMonoidHom)
              (Subgroup.subgroupOfEquivOfLe hSUG_M).injective)
            (pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hSUG_M).symm.toMonoidHom)
              (Subgroup.subgroupOfEquivOfLe hSUG_M).symm.injective)
        have hr2 : pRank ↥M p = 2 := hpτ2.2
        omega
      obtain ⟨A, hA, hASUG⟩ := exists_mem_elemAbelianOfRank_two_le_of_two_le_pRank
        (Fact.out : p.Prime) hpRankSUG
      have hAE : A ≤ E := hASUG.trans (hSUG_U.trans hUE)
      have hAM : A ≤ M := hASUG.trans hSUG_M
      have hSUGab : IsMulCommutative ↥SUG :=
        Subgroup.le_centralizer_iff_isMulCommutative.mp
          (hSUG_U.trans ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hUab).trans
            (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hSUG_U))))
      have hAmax : IsMaximalElementaryAbelian p A :=
        (isMaximalElementaryAbelian_of_mem_tau2 hG hM Fact.out hpτ2 hAM hA).1
      -- nonabelian Sylow `S' ⊇ SUG`.
      push Not at habel
      obtain ⟨S', hSUGS'⟩ := hSUGpg.exists_le_sylow
      have hAS' : A ≤ (S' : Subgroup G) := hASUG.trans hSUGS'
      have hS'nonab : ¬ IsMulCommutative ↥(S' : Subgroup G) := by
        obtain ⟨S₀, hS₀⟩ := habel
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ S'
        intro hab
        apply hS₀
        have hcoe : (S₀ : Subgroup G) = MulAut.conj g⁻¹ • (S' : Subgroup G) := by
          rw [← hg, Sylow.coe_subgroup_smul, ← mul_smul, ← map_mul, inv_mul_cancel,
            map_one, one_smul]
        rw [hcoe, mulAut_smul_eq_map]
        exact OddOrder.BG.Ch3.S11.isMulCommutative_of_mulEquiv
          (Subgroup.equivMapOfInjective _ _ (MulAut.conj g⁻¹).injective) hab
      -- `C_G(A) ⊓ S' = SUG`.
      have hSUG_le_C : SUG ≤ Subgroup.centralizer (A : Set G) ⊓ (S' : Subgroup G) :=
        le_inf (le_centralizer_of_le_of_le hSUGab le_rfl hASUG) hSUGS'
      have hC_le_M : Subgroup.centralizer (A : Set G) ⊓ (S' : Subgroup G) ≤ M :=
        (inf_le_left.trans (centralizer_le_E_of_tau2 hG hsetup hpτ2 hA hAE).1).trans hsetup.E_le
      have hCcard_le : Nat.card ↥(Subgroup.centralizer (A : Set G) ⊓ (S' : Subgroup G)) ≤
          Nat.card ↥SUG := by
        rw [hSUGcardM]
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (S'.isPGroup'.to_le inf_le_right)
        rw [hk]
        exact Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le
          ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp
            (hk ▸ Subgroup.card_dvd_of_le hC_le_M))
      have hCeqSUG : Subgroup.centralizer (A : Set G) ⊓ (S' : Subgroup G) = SUG :=
        (Subgroup.eq_of_le_of_card_ge hSUG_le_C hCcard_le).symm
      -- canonical line `A₀` + clause (c).
      obtain ⟨A₀, _hA₀eq, hA₀card, hA₀A, hMσA₀, hcReg, _hA₀max⟩ :=
        exists_canonical_line_of_nonabelianSylow hG hsetup hpτ2 hA hAE habel
      have hMσ_ne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ := OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
      have hA₀mem : A₀ ∈ elemAbelianOfRank G p 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hA₀card, by rw [hA₀card, pow_one]⟩
      have hA₀C : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (A₀ : Set G) ≠ ⊥ := by
        rw [inf_eq_left.mpr hMσA₀]; exact hMσ_ne
      have hM_single : maximalSubgroupsContaining (Subgroup.centralizer (A₀ : Set G)) = {M} :=
        maximalContaining_centralizer_line_eq_singleton hG hsetup hpτ2 hA hAE hA₀mem hA₀A hA₀C
      have hCA₀_le_M : Subgroup.centralizer (A₀ : Set G) ≤ M := by
        have hlt : Subgroup.centralizer (A₀ : Set G) < ⊤ :=
          lt_of_le_of_lt (Subgroup.centralizer_le_normalizer _)
            (normalizer_lt_top_of_le_of_ne_bot hG hM (hA₀A.trans hAM)
              (ne_bot_of_mem_elemAbelianOfRank_one hA₀mem))
        obtain ⟨Mst, hco, hle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hlt.ne
        have hmem : Mst ∈ maximalSubgroupsContaining (Subgroup.centralizer (A₀ : Set G)) :=
          mem_maximalSubgroupsContaining.mpr ⟨hco, hle⟩
        rw [hM_single, Set.mem_singleton_iff] at hmem
        exact hmem ▸ hle
      -- `S' ⊄ M` (nonabelian, but `Sylow_p(M) = SUG` abelian).
      have hS'_not_le_M : ¬ ((S' : Subgroup G) ≤ M) := by
        intro hS'M
        have hcardle : Nat.card ↥(S' : Subgroup G) ≤ Nat.card ↥SUG := by
          rw [hSUGcardM, S'.card_eq_multiplicity]
          exact Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le
            ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp
              (S'.card_eq_multiplicity ▸ Subgroup.card_dvd_of_le hS'M))
        exact hS'nonab ((Subgroup.eq_of_le_of_card_ge hSUGS' hcardle) ▸ hSUGab)
      -- `A₀ ≠ Ω₁(Z(S'))`.
      set Z₀' : Subgroup G := OddOrder.BG.Ch3.S10.omega1CenterInG (S' : Subgroup G) p with hZ₀'def
      have hS'_cent_Z₀ : (S' : Subgroup G) ≤ Subgroup.centralizer (Z₀' : Set G) := by
        intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [SetLike.mem_coe, hZ₀'def, OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map] at hz
        obtain ⟨z', hz', rfl⟩ := hz
        have hz'c : z' ∈ Subgroup.center ↥(S' : Subgroup G) := (mem_omega1OfAbelian.mp hz').1
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'c ⟨q, hq⟩)).symm
      have hA₀_ne_Z₀ : A₀ ≠ Z₀' := by
        rintro rfl
        exact hS'_not_le_M (hS'_cent_Z₀.trans hCA₀_le_M)
      -- Lemma 10.13: `C_{S'}(A) = A₀ ⊔ Z` with `Z` cyclic, `A₀ ⊓ Z = ⊥`.
      have hpG : p ∈ (Nat.card G).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Fact.out,
          (hA.2 ▸ dvd_pow_self p two_ne_zero).trans (Subgroup.card_subgroup_dvd_card A),
          Nat.card_pos.ne'⟩
      obtain ⟨Z, _hZS', hZcyc, _hZ₀Z, hA₀Z, hCdecomp⟩ :=
        (OddOrder.BG.Ch3.S10.nonabelian_pSubgroup_rankTwo_elemAbelian_structure hG hpG hA hAmax
          S'.isPGroup' hS'nonab hAS' ⟨hA₀mem, hA₀A⟩ hA₀_ne_Z₀).2.1
      have hSUGdecomp : SUG = A₀ ⊔ Z := hCeqSUG ▸ hCdecomp
      have hZSUG : Z ≤ SUG := hSUGdecomp ▸ le_sup_right
      refine ⟨Z, hZSUG.trans hSUG_U, hSUGpg.to_le hZSUG, ?_, ?_⟩
      · -- exponent: `ν_p(exp U) ≤ ν_p(exp SUG) ≤ ν_p(exp Z)` (`exp SUG ∣ exp Z`,
        -- since `SUG = A₀ ⊔ Z` with `|A₀| = p ∣ exp Z`).
        have hSUGsubU_card : Nat.card ↥(SUG.subgroupOf U) = p ^ (Nat.card ↥U).factorization p := by
          rw [show SUG.subgroupOf U = (SU : Subgroup ↥U) from by
            rw [hSUGdef, Subgroup.subgroupOf,
              Subgroup.comap_map_eq_self_of_injective U.subtype_injective], SU.card_eq_multiplicity]
        refine le_trans (factorization_exponent_le_of_sylow hSUG_U hSUGsubU_card) ?_
        haveI := hSUGab
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hSUGpg.to_le hZSUG)
        have hA₀NZ : A₀ ≤ Subgroup.normalizer (Z : Set G) :=
          (le_centralizer_of_le_of_le hSUGab (hA₀A.trans hASUG) hZSUG).trans
            (Subgroup.centralizer_le_normalizer _)
        have hcardSUG : Nat.card ↥SUG = p ^ (k + 1) := by
          rw [hSUGdecomp, card_sup_eq_mul_of_le_normalizer_of_disjoint hA₀NZ hA₀Z, hA₀card, hk,
            ← pow_succ']
        -- `SUG` is not cyclic (it contains the rank-2 elementary abelian `A`), so
        -- `exp SUG < |SUG|`.
        have hSUGnotcyc : ¬ IsCyclic ↥SUG := by
          intro hcyc
          haveI := hcyc
          have hAcyc : IsCyclic ↥A :=
            isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hASUG).toMonoidHom
              (Subgroup.subgroupOfEquivOfLe hASUG).surjective
          have hdvdp : Monoid.exponent ↥A ∣ p :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => hA.1.2 x)
          rw [hAcyc.exponent_eq_card, hA.2] at hdvdp
          exact absurd (Nat.le_of_dvd (Fact.out : p.Prime).pos hdvdp)
            (by nlinarith [(Fact.out : p.Prime).two_le])
        have hexpSUGne : Monoid.exponent ↥SUG ≠ Nat.card ↥SUG :=
          fun heq => hSUGnotcyc (IsCyclic.of_exponent_eq_card heq)
        obtain ⟨m, hm_le, hm⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
          (hcardSUG ▸ Group.exponent_dvd_nat_card)
        have hmk : m ≤ k := by
          by_contra hc
          push Not at hc
          exact hexpSUGne (by rw [hm, show m = k + 1 by omega, hcardSUG])
        have hfp : ∀ n, (p ^ n).factorization p = n := fun n => by
          rw [Nat.factorization_pow, Finsupp.smul_apply,
            Nat.Prime.factorization_self (Fact.out : p.Prime), smul_eq_mul, mul_one]
        rw [hm, hZcyc.exponent_eq_card, hk, hfp, hfp]
        exact hmk
      · -- regularity: every prime-order `z ∈ Z` generates a line `⟨z⟩ ≠ A₀` (`A₀ ⊓ Z = ⊥`),
        -- which clause (c) shows is regular on `M_σ`.
        refine inf_centralizer_eq_bot_of_forall_prime_order ?_
        intro z hzZ hzprime
        have hordz : orderOf z = p := by
          obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp (hSUGpg.to_le hZSUG)
          have hqdvd : orderOf z ∣ p ^ j := by
            have h := (Subgroup.orderOf_coe (⟨z, hzZ⟩ : ↥Z)) ▸ orderOf_dvd_natCard (⟨z, hzZ⟩ : ↥Z)
            rwa [hj] at h
          exact (Nat.prime_dvd_prime_iff_eq hzprime Fact.out).mp (hzprime.dvd_of_dvd_pow hqdvd)
        set X : Subgroup G := Subgroup.zpowers z with hXdef
        have hXcard : Nat.card ↥X = p := by rw [hXdef, Nat.card_zpowers]; exact hordz
        have hXmem : X ∈ elemAbelianOfRank G p 1 :=
          ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
        have hXZ : X ≤ Z := by rw [hXdef, Subgroup.zpowers_le]; exact hzZ
        have hXE : X ≤ E := (hXZ.trans hZSUG).trans (hSUG_U.trans hUE)
        have hXneA₀ : X ≠ A₀ := by
          intro he
          have hbot : A₀ = ⊥ := le_bot_iff.mp (hA₀Z ▸ le_inf le_rfl (he ▸ hXZ))
          rw [hbot, Subgroup.card_bot] at hA₀card
          exact (Fact.out : p.Prime).ne_one hA₀card.symm
        have hreg := (hcReg X hXmem hXE hXneA₀).1
        rwa [hXdef, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hreg
  · -- **τ₁ ∪ τ₃ case** (`r_p(M) = 1`): `Z = Sylow_p(U)` is regular by Lemma 14.1.
    have hr1 : pRank ↥M p = 1 := by
      have hle : pRank ↥M p ≤ 2 := hsetup.pRank_M_le_two hG hpE
      have hge : 1 ≤ pRank ↥M p :=
        (one_le_pRank_of_mem_primeFactors hpE).trans
          (pRank_le_of_injective (Subgroup.inclusion_injective hsetup.E_le))
      have hne2 : pRank ↥M p ≠ 2 := fun h2 => hpτ2 ⟨hpσ, h2⟩
      omega
    -- `Z = Sylow_p(U)`, pushed into `G`.
    set SU : Sylow p ↥U := default with hSUdef
    set Z : Subgroup G := (SU : Subgroup ↥U).map U.subtype with hZdef
    have hZU : Z ≤ U := Subgroup.map_subtype_le _
    have hZcard : Nat.card ↥Z = p ^ (Nat.card ↥U).factorization p := by
      rw [hZdef, Subgroup.card_map_of_injective U.subtype_injective, SU.card_eq_multiplicity]
    have hZpg : IsPGroup p ↥Z := IsPGroup.of_card hZcard
    have hZsub : Z.subgroupOf U = (SU : Subgroup ↥U) := by
      rw [hZdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective U.subtype_injective]
    have hZcard' : Nat.card ↥(Z.subgroupOf U) = p ^ (Nat.card ↥U).factorization p := by
      rw [hZsub, SU.card_eq_multiplicity]
    refine ⟨Z, hZU, hZpg, factorization_exponent_le_of_sylow hZU hZcard', ?_⟩
    -- **Regularity** (Lemma 14.1, `r_p = 1`, `p ∉ σ ∪ κ`): same discharge as the `K = ⊥` branch.
    intro z hzZ hzne
    obtain ⟨k, hk0⟩ := (IsPGroup.iff_orderOf.mp hZpg) ⟨z, hzZ⟩
    have hk : orderOf z = p ^ k := (Subgroup.orderOf_coe ⟨z, hzZ⟩).trans hk0
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rw [pow_zero, orderOf_eq_one_iff] at hk; exact absurd hk hzne
      · exact hpos
    have hpdvd : p ∣ orderOf z := hk ▸ dvd_pow_self p (by omega)
    set f : G := z ^ (orderOf z / p) with hfdef
    have hford : orderOf f = p := orderOf_pow_orderOf_div (orderOf_pos z).ne' hpdvd
    have hfZ : f ∈ Z := Z.pow_mem hzZ _
    have hfM : f ∈ M := (hZU.trans hUM) hfZ
    set A : Subgroup G := Subgroup.zpowers f with hAdef
    have hAcard : Nat.card ↥A = p := by rw [hAdef, Nat.card_zpowers]; exact hford
    have hAelem : A.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hAcard
    have hAM : A ≤ M := by rw [hAdef, Subgroup.zpowers_le]; exact hfM
    have hAr : A ∈ elemAbelianOfRank G p (pRank ↥M p) := by
      rw [hr1, mem_elemAbelianOfRank]; exact ⟨hAelem, by rw [hAcard, pow_one]⟩
    obtain ⟨_, hCA, _⟩ := S14.msigma_structure_of_notMem_sigma_kappa hG hM hpπ hpσ hpκ hAr hAM
    have hCfA : Subgroup.centralizer (A : Set G) = Subgroup.centralizer ({f} : Set G) := by
      rw [hAdef, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hCzf : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer ({f} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      rw [hfdef]; exact (show Commute x z from hx).pow_right _
    rw [eq_bot_iff, ← hCA, hCfA]
    exact inf_le_inf_left _ hCzf

/-- **BG Lemma 15.1(e)** (mmd L4148): the Frobenius factor `U₀ M_σ`.  For a maximal `M` with
`κ(M)`-Hall `K` and `(κ ∪ σ)'`-Hall `U ≠ 1`, there is a subgroup `U₀ ≤ U` of the same exponent as
`U` such that `U₀ M_σ` is a Frobenius group with kernel `M_σ` and complement `U₀`.

Proof by the `K = ⊥` / `K ≠ ⊥` split:

* `K = ⊥` (type `F`): `U` is the `σ`-complement `E` of a §12 `E`-setup
  (`subgroupESetup_of_isHall_kappa_eq_bot`), and Theorem 12.12(b)
  (`frobenius_factorization_of_regular`, part (b)) supplies `U₀ = E₀ ≤ E = U` directly, with
  `exp U₀ = exp U` and `U₀ M_σ` Frobenius.  The regularity hypothesis is discharged exactly as in
  `typeP_centralizerGeneratedBySigma_isMulCommutative` (Lemma 14.1 for `(τ₁∪τ₃)`-elements).

* `K ≠ ⊥` (type `P`): `U` is abelian (`typeP_hall_derived_eq_and_abelian`).  We build `U₀ ≤ U`
  **`M`-internally** as the internal direct product `⨆_{p ∈ π(U)} Z_p`, where for each prime
  `p ∈ π(U)` the cyclic `Z_p ≤ Sylow_p(U)` realizes the `p`-part of `exp U` and acts regularly on
  `M_σ`:
  - `p ∈ (τ₁ ∪ τ₃)` (`r_p(M) = 1`): `Sylow_p(U)` is cyclic, take `Z_p = Sylow_p(U)`; regular by
    Lemma 14.1 (`Ω₁(Sylow_p(U)) ∈ ℰ_p¹(M)`, `p ∉ σ ∪ κ`).
  - `p ∈ τ₂` (`r_p(M) = 2`): `Sylow_p(U)` is abelian of rank `2`; Theorem 12.5(f) gives a regular
    line `A₁ ∈ ℰ_p¹(M)` inside `A := Ω₁(Sylow_p(U))`, and a cyclic `Z_p ≤ Sylow_p(U)` with
    `Ω₁(Z_p) = A₁`, `exp Z_p = exp Sylow_p(U)` propagates regularity to all of `Z_p`. -/
theorem typeP_hall_frobenius_factor [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUne : U ≠ ⊥) :
    ∃ U0 : Subgroup G, U0 ≤ U ∧ Monoid.exponent ↥U0 = Monoid.exponent ↥U ∧
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M)
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M))
        (U0.subgroupOf (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M)) := by
  classical
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  by_cases hKbot : K = ⊥
  · -- **Case `K = ⊥`** (type `F`): `U = E` is the §12 `σ`-complement; Theorem 12.12(b).
    obtain ⟨E₁, E₂, E₃, hsetup⟩ :=
      subgroupESetup_of_isHall_kappa_eq_bot hG hM hKM hUM hK hKbot hU
    -- Discharge the regularity hypothesis of Theorem 12.12 via Lemma 14.1 (copied from
    -- `typeP_centralizerGeneratedBySigma_isMulCommutative`'s `K = ⊥` branch).
    have hreg : ∀ e ∈ U, e ≠ 1 →
        (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
          Mσ ⊓ Subgroup.centralizer ({e} : Set G) = ⊥ := by
      intro e heU hene hprimes
      have hord1 : orderOf e ≠ 1 := fun hc => hene (orderOf_eq_one_iff.mp hc)
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord1
      haveI : Fact p.Prime := ⟨hp⟩
      have hpτ : p ∈ tau1 M ∪ tau3 M :=
        hprimes p (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, (orderOf_pos e).ne'⟩)
      set f : G := e ^ (orderOf e / p) with hfdef
      have hford : orderOf f = p := orderOf_pow_orderOf_div (orderOf_pos e).ne' hpdvd
      have hfU : f ∈ U := U.pow_mem heU _
      have hfM : f ∈ M := hUM hfU
      set A : Subgroup G := Subgroup.zpowers f with hAdef
      have hAcard : Nat.card ↥A = p := by rw [hAdef, Nat.card_zpowers]; exact hford
      have hAelem : A.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hAcard
      have hAM : A ≤ M := by rw [hAdef, Subgroup.zpowers_le]; exact hfM
      have hpπ : p ∈ S14.piSet M :=
        Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans ((U.orderOf_dvd_natCard heU).trans
          (Subgroup.card_dvd_of_le hUM)), Nat.card_pos.ne'⟩
      have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
        hpτ.elim (fun h => tau1_subset_sigma_compl M h) (fun h => tau3_subset_sigma_compl M h)
      have hpκ : p ∉ S14.kappa M := by
        rw [isTypeF_of_isHall_kappa_eq_bot hKM hK hKbot]; simp
      have hr1 : pRank ↥M p = 1 :=
        hpτ.elim tau1_pRank_eq_one tau3_pRank_eq_one
      have hAr : A ∈ elemAbelianOfRank G p (pRank ↥M p) := by
        rw [hr1, mem_elemAbelianOfRank]
        exact ⟨hAelem, by rw [hAcard, pow_one]⟩
      obtain ⟨_, hCA, _⟩ :=
        S14.msigma_structure_of_notMem_sigma_kappa hG hM hpπ hpσ hpκ hAr hAM
      have hCfA : Subgroup.centralizer (A : Set G) = Subgroup.centralizer ({f} : Set G) := by
        rw [hAdef, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      have hCef : Subgroup.centralizer ({e} : Set G) ≤ Subgroup.centralizer ({f} : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
        rw [hfdef]
        exact (show Commute x e from hx).pow_right _
      rw [eq_bot_iff, ← hCA, hCfA]
      exact inf_le_inf_left _ hCef
    -- Theorem 12.12(b): the same-exponent regular complement `E₀ ≤ U`.
    obtain ⟨_, E₀, hE₀le, hexp, hFrob⟩ :=
      frobenius_factorization_of_regular hG hsetup hreg
    refine ⟨E₀, hE₀le, hexp, ?_⟩
    -- `FrobFactConclusion` states it for `M_σ ⊔ E₀`; commute to `E₀ ⊔ M_σ`.
    rw [show E₀ ⊔ Mσ = Mσ ⊔ E₀ from sup_comm _ _]
    exact hFrob
  · -- **Case `K ≠ ⊥`** (type `P`): `U` is abelian (15.1(b)); assemble `U₀ = ⊔_p Z_p` from the
    -- per-prime regular components (`typeP_hall_regular_component_at_prime`) via the engine.
    obtain ⟨_, hUab⟩ := typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKbot hK hU
    have hUinf : Mσ ⊓ U = ⊥ := by
      have hMσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (Mσ.subgroupOf M) :=
        OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
      have hcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥Mσ) := by
        refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
          (π := (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) Nat.card_pos.ne' Nat.card_pos.ne'
          ?_ ?_
        · intro q hq
          exact hU.1 q (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
        · intro q hq hqcompl
          have hqMσ : q ∈ (Nat.card ↥(Mσ.subgroupOf M)).primeFactors := by
            rwa [Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
          exact hqcompl (Or.inr (hMσHall.1 q hqMσ))
      rw [inf_comm]; exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
    exact frobenius_factor_of_regular_components hG hM hUM hUne hUab hUinf
      (fun p hp => typeP_hall_regular_component_at_prime hG hM hUM hUab hU hp)

/-- **Forward lemma: the `§14`-gated structural content of BG Lemma 15.1** (faithful to mmd L4116,
proof deferred).  Bundles the conjuncts of Lemma 15.1 that depend on the still-`sorry` §14 results
(Proposition 14.2(a)'s normal complement `M = K U M_σ`, Theorem 14.7(d)(h)) and Theorem 12.12:

* `K ≠ ⊥ → M' = U M_σ ∧ U` abelian (mmd 15.1(b), Theorem 14.7(h) + Corollary 12.10(b));
* mmd 15.1(c): the `C_{M_σ}(X) ≠ 1` ⟹ `𝓜(C_G(X)) = {M}`, `X` cyclic `τ₂` funnel (Corollary 14.3 +
  Theorem 12.5(d) + Corollary 12.10(b));
* mmd 15.1(d): `⟨C_U(x) | x ∈ M_σ#⟩` abelian (Theorem 12.12(a) for `K = 1`; `U` abelian for
  `K ≠ 1`);
* mmd 15.1(e): the Frobenius subgroup `U₀ M_σ` (Theorem 12.12(b) for `K = 1`; the componentwise
  construction for `K ≠ 1`).

These are isolated here so that `typeP_auxiliary_structure` discharges conjuncts 3 (`M_σ ≤ M'`) and
4 (`M'' ≤ M_σ`) with no `sorry` of its own, citing this lemma only for the §14-gated parts.  Once
§14 (Prop 14.2(a), Thm 14.7(h)) and the Theorem 12.12 `K ≠ 1` Frobenius construction land, this
forward lemma is the single discharge point. -/
theorem typeP_auxiliary_structure_gated [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    (K ≠ ⊥ → derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧ IsMulCommutative ↥U) ∧
      (∀ X : Subgroup G, X ≤ U → X ≠ ⊥ →
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ →
          maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} ∧
            IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M)) ∧
      IsMulCommutative ↥(centralizerGeneratedBySigma M U) ∧
      (U ≠ ⊥ → ∃ U0 : Subgroup G,
        U0 ≤ U ∧ Monoid.exponent U0 = Monoid.exponent U ∧
          OddOrder.Isaacs.Ch06.IsFrobeniusGroup
            ↥(U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M)
            ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf
              (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M))
            (U0.subgroupOf (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M))) :=
  -- All four conjuncts of BG Lemma 15.1 are now standalone clean lemmas (issue 7007).
  ⟨fun hKbot => typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKbot hK hU,
   fun _X hXU hXne hCX => typeP_hall_small_subgroup_cyclic_tau2 hG hM hUM hU hXU hXne hCX,
   typeP_centralizerGeneratedBySigma_isMulCommutative hG hM hKM hUM hK hU,
   fun hUne => typeP_hall_frobenius_factor hG hM hKM hUM hK hU hUne⟩

/-- **BG Lemma 15.1** (mmd L4116): auxiliary structure around the `U`-factor of an
**arbitrary** maximal subgroup `M = KUM_σ`.  The quotient assertion `M'/M_sigma` abelian is
encoded as `M'' <= M_sigma`, avoiding premature quotient API commitments.

Faithfulness fix (Lane G): the previous scaffold added a spurious `IsTypeP M` hypothesis;
mmd Lemma 15.1 holds for every `M ∈ ℳ` (the `K ≠ 1` clauses are guarded inline), and the
general form is what Theorem A(2) and Theorem B cite.

`K ≠ 1` exposure (Lane G): the `K ≠ ⊥` clause now also records `M = K M'` as the relative
complement `IsComplement' (M'.subgroupOf M) (K.subgroupOf M)` together with the `(|M'|, |K|)`
coprimality — both are mmd 15.1(a)+(b) (`M = KUM_σ`, `K ≠ 1 → M' = UM_σ`, with `|K|` a
`κ(M)`-number and `|M'|` a `κ(M)'`-number).  This supplies exactly the hypotheses of
`Msigma_inf_centralizer_le_derivedDerived_of_isComplement'` (the §14-independent `K* ⊆ M''`
engine), so Corollary 15.6's `K* ⊆ M''` clause becomes a single citation once §14 lands.

Faithfulness fix (Lane G 2026-06-15): added `hKM : K ≤ M` and `hUM : U ≤ M`.  In BG, `K` and
`U` are *subgroups of* `M` (Hall `κ(M)`- and `(κ∪σ)'`-subgroups of `M`); without these the
`κ`/`σ`-prime bookkeeping degenerates (e.g. `K ⊓ M = 1` with `K ≠ 1` makes `K ≠ ⊥ → …` false).
The sole caller (`fitting_decomposition`) constructs `K = K'.map M.subtype`, `U = U'.map M.subtype`,
so both containments hold there.

Proof status (2026-06-23): **now fully sorry-free + axiom-clean** (`#print axioms
typeP_auxiliary_structure` = `[propext, Classical.choice, Quot.sound]`).  The §14-gated parts below
have all landed — `typeP_auxiliary_structure_gated` is now a clean term-mode citation of four
standalone lemmas, and Thm 14.7 (`typeP_duality`) is itself sorry-free — so the "(sorried)"
qualifiers in the historical status below are stale.  Original (Lane G 2026-06-15) breakdown:
* **Conjunct 3** (`M_σ ≤ M'`, Thm 10.2(c)) and **conjunct 4** (`M'' ≤ M_σ` via
  `derivedDerived_le_Msigma`, Cor 12.10(b)) are **sorry-free** (`#print axioms
  derivedDerived_le_Msigma` = `[propext, Classical.choice, Quot.sound]`), citing no `sorry`.
* **Conjunct 1** (`U M_σ ⊴ M`): the `K = ⊥` branch is sorry-free
  (`subgroupESetup_of_isHall_kappa_eq_bot` ⟹ `U M_σ = M`); the `K ≠ ⊥` branch reduces to
  `M' = U M_σ` (forward lemma).
* **Conjunct 2** (`K` cyclic): `K = ⊥` sorry-free; `K ≠ ⊥` cites the (sorried) §14 `typeP_duality`
  (Thm 14.7(d)), with `IsTypeP M` derived from `K ≠ ⊥`
  (`isTypeP_of_isHall_kappa_subgroupOf_ne_bot`).
* **Conjunct 5** (`K ≠ ⊥` package): `IsComplement'` + coprimality cite the (sorried) §14
  `typeP_duality` (Thm 14.7(h)); `M' = U M_σ` and `U` abelian come from the forward lemma.
* **Conjuncts 6** (Cor 14.3 funnel — the `X` cyclic-`τ₂` step needs `X` abelian, which routes
  through Hall-`τ₂`-conjugacy for `K = ⊥`), **7**, and **8** are gated on the still-`sorry` §14
  results (Prop 14.2(a) normal complement, Thm 14.7) and Theorem 12.12.

All of the `§14`-structural content is isolated in the single faithful forward lemma
`typeP_auxiliary_structure_gated`; this theorem itself introduces no `sorry` of its own. -/
theorem typeP_auxiliary_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    M ≤ Subgroup.normalizer ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) ∧
      IsCyclic ↥K ∧
      OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M ∧
      derivedInG (derivedInG M) ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
      (K ≠ ⊥ → derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧
        IsMulCommutative ↥U ∧
        Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) ∧
        Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M))
          (Nat.card ↥(K.subgroupOf M))) ∧
      (∀ X : Subgroup G, X ≤ U → X ≠ ⊥ →
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ →
          maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} ∧
            IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M)) ∧
      IsMulCommutative ↥(centralizerGeneratedBySigma M U) ∧
      (U ≠ ⊥ → ∃ U0 : Subgroup G,
        U0 ≤ U ∧ Monoid.exponent U0 = Monoid.exponent U ∧
          OddOrder.Isaacs.Ch06.IsFrobeniusGroup
            ↥(U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M)
            ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf
              (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M))
            (U0.subgroupOf (U0 ⊔ OddOrder.BG.Ch3.S10.Msigma M))) := by
  classical
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  -- The §14-gated structural facts (forward lemma).
  obtain ⟨hM'gated, hX, hCab, hFrob⟩ :=
    typeP_auxiliary_structure_gated hG hM hKM hUM hK hU
  -- **Conjunct 5** (`K ≠ ⊥` package): `M' = U M_σ`, `U` abelian (forward), plus the complement /
  -- coprimality from Theorem 14.7(h) (`typeP_duality`, with `IsTypeP` from `K ≠ ⊥`).
  have hconj5 : K ≠ ⊥ → derivedInG M = U ⊔ Mσ ∧ IsMulCommutative ↥U ∧
      Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) ∧
      Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M)) (Nat.card ↥(K.subgroupOf M)) := by
    intro hKne
    obtain ⟨hM'eq, hUab⟩ := hM'gated hKne
    -- `IsTypeP M` from `K ≠ ⊥` (`K ≤ M` makes `K.subgroupOf M ≠ ⊥`).
    have hKofne : K.subgroupOf M ≠ ⊥ := by
      rw [ne_eq, Subgroup.subgroupOf_eq_bot]
      exact fun hd => hKne (hd.eq_bot_of_le hKM)
    have hP : S14.IsTypeP M := isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK hKofne
    obtain ⟨hcompl, hcop, _⟩ := typeP_duality hG hM hP hKM hK hKstar
    exact ⟨hM'eq, hUab, hcompl, hcop⟩
  -- **Conjunct 2** (`K` cyclic).
  have hconj2 : IsCyclic ↥K := by
    by_cases hKne : K = ⊥
    · rw [hKne]; infer_instance
    · have hKofne : K.subgroupOf M ≠ ⊥ := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        exact fun hd => hKne (hd.eq_bot_of_le hKM)
      have hP : S14.IsTypeP M := isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK hKofne
      obtain ⟨_, _, _Mstar, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ := typeP_duality hG hM hP hKM hK hKstar
      haveI := hcyc
      exact Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  -- **Conjunct 1** (`M ≤ N_G(U M_σ)`): `U M_σ = M` (`K = ⊥`) or `= M'` (`K ≠ ⊥`), both normal.
  have hconj1 : M ≤ Subgroup.normalizer ((U ⊔ Mσ : Subgroup G) : Set G) := by
    by_cases hKne : K = ⊥
    · -- `K = ⊥ → U M_σ = M`, so `N_G(U M_σ) = N_G(M) ⊇ M`.
      obtain ⟨E₁, E₂, E₃, hsetup⟩ :=
        subgroupESetup_of_isHall_kappa_eq_bot hG hM hKM hUM hK hKne hU
      have hUMσ : U ⊔ Mσ = M := by rw [sup_comm]; exact hsetup.E_compl_sup
      rw [hUMσ]; exact Subgroup.le_normalizer
    · -- `K ≠ ⊥ → U M_σ = M'`, and `M ≤ N_G(M')` (`M' ⊴ M`).
      obtain ⟨hM'eq, _, _, _⟩ := hconj5 hKne
      rw [← hM'eq]
      exact OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M
  exact ⟨hconj1, hconj2, OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM,
    derivedDerived_le_Msigma hG hM, hconj5, hX, hCab, hFrob⟩

end OddOrder.BG.Ch4.S15
