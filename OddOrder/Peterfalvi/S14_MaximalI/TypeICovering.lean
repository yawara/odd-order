/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S14_MaximalI.NormPackage

/-!
# Peterfalvi (12.17) + the (8.8) case-(b) dichotomy

The all-type-I non-existence argument: the type-I maximals assemble into a (7.10) Frobenius
family (`TypeICovering`), (7.11) rules it out (`not_all_maximal_typeI`), and combined with the
(8.8) dichotomy this forces the case-(b) pairing data (`theorem88_caseB_holds`).

Split from `DadeContradiction.lean` (file-size policy); consumes the (12.7) `typeI_frobenius`
of `NormPackage.lean`.
-/
namespace OddOrder.Peterfalvi.S14
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## (12.17): forcing case (b) of Theorem (8.8) — the all-type-I non-existence argument

Peterfalvi (12.17) shows that case (a) of Theorem (8.8) — *every* maximal subgroup of `G` being of
type I — is impossible.  The argument assembles the type-I maximals into a Frobenius family in the
sense of (7.10) (`S09.FrobeniusFamily`) and derives the contradiction from (7.11)
(`S09.not_trivial_G0`).  Combined with the (8.8) dichotomy (`theorem88_dichotomy`, BG §16), this
forces the case-(b) pairing data `Theorem88CaseBData`, which the Feit–Thompson endgame consumes.

The genuinely group-theoretic content of the family — the Frobenius structure (from (12.7)) and the
self-normalizing identity `L = N_G(L_F)` — is proved here.  The remaining §8/§10 covering inputs
(TI sharp-sets via (8.13.c1), coprime kernels and the `G#` cover via (8.17)) are isolated in the
faithful carrier `TypeICovering`. -/

section Theorem1217

variable [Finite G]

/-! The normalizer bridge `maximalSubgroup_eq_normalizer_maxNilpotentNormalHall` (`L = N_G(L_F)`
for maximal `L` with `L_F ≠ ⊥`) now lives with the (8.6.a)/(8.16) centralizer-containment block
before (12.10), where the type-`P` pins consume it. -/

/-- **Peterfalvi (8.13.c1)+(2.3), all-type-I case** — the escaping-centralizer control that makes
each type-I kernel's Fitting subgroup a `TI`-subgroup, supplying the `FittingIsTI` gate of the
(12.17) `isTI` covering input.

For a maximal subgroup `M` of a minimal simple group of odd order in which **every** maximal subgroup
is of type I (`hall`), the Fitting subgroup `F(M)` is `TI` (`S15.FittingIsTI M`).  In the all-type-I
configuration the (8.13.c1) escaping-centralizer control forces `R(x) = 1` on `M_σ#` (the (8.14)
signalizer is trivial), so `M_σ = M_F = F(M)` is a genuine trivial-intersection subgroup.

**Genuinely still-missing**: the (8.13.c1) escaping-centralizer control is `escapingCentralizers_control`
(S10:526), itself an open BG §16 / (2.3) residual, and the passage from it to `FittingIsTI` is not
assembled anywhere in reach of `S14`.  BG §16 exposes `FittingIsTI` only in the `M_F ≠ M_σ` /
type-`P₂` directions (`fittingIsTI_of_isTypeP2`, `fitting_isTI_of_mf_ne_msigma`), never for the
all-type-I `M_F = M_σ` case, which is exactly the escaping-centralizer content here.

**Soundness**: the statement is TRUE and **not** a false general implication.  It is *not* claimed
for an arbitrary type-I subgroup — the (12.10)/(12.16) Frobenius witness `L` is type-I-like yet
has `H^# = (L_F)#` **not** `TI` in `G` (Pf (12.10), see `sibleyTarget_frobI`), so the conclusion
genuinely requires the ambient all-type-I hypothesis `hall` (which excludes the counterexample
configuration and puts us in the (8.17.a) type-I covering case where (8.13.c1) applies).  Tied to
`hG`, `M` maximal, its type-I witness, and `hall`. -/
private theorem allTypeI_fittingIsTI (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (_hI : IsTypeI M)
    (_hall : ∀ N : Subgroup G, N ∈ maximalSubgroups G → IsTypeI N) :
    OddOrder.BG.Ch4.S15.FittingIsTI M := by
  sorry

/-- **Peterfalvi (8.8.a) dichotomy, all-type-I case** — the case-(b) covering branch of BG Theorem
E cannot occur when every maximal subgroup is of type I.

If `data`'s cover admits a `BGTheoremENonTypeICovering` (the two-exceptional-subgroup case (8.8.b)
of BG Theorem E) while every maximal subgroup is of type I (`hall`), a contradiction results.

**Genuinely still-missing**: the `BGTheoremENonTypeICovering` carrier records only the exceptional
`Ẑ`-set and its cover geometry — it does **not** expose the type-`P` maximal whose Theorem 14.7
duality produced `Ẑ` (see `nonTypeICovering_of_isTypeP`, whose inputs `Mref, Kref, …` are consumed
but not re-exported).  So no non-type-I maximal is directly extractable from `hNonTypeI` to
contradict `hall`.  The (8.8) dichotomy's *exclusivity* — case (b) selected `iff` some maximal is
non-type-I — is the BG §16 (8.8.a) residual (parallel to `theorem88_dichotomy`), not assembled in
reach of `S14`.

**Soundness**: the statement is TRUE — the (8.8.b) covering branch is produced (in
`nonTypeICovering_of_isTypeP`) *only* from a type-`P` (= non-type-I, `isTypeNonI_of_isTypeP`)
maximal, which `hall` forbids; so the two hypotheses are jointly contradictory.  It is **not** a
false general implication: it does not claim `BGTheoremENonTypeICovering` is empty unconditionally
(it is inhabited whenever a non-type-I maximal exists) — only its incompatibility with the
all-type-I hypothesis `hall`.  Tied to `hG`, the specific `data`, its non-type-I covering, and
`hall`. -/
private theorem not_nonTypeICovering_of_all_typeI (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {data : OddOrder.Peterfalvi.S10.BGTheoremECoverData G}
    (_hcov : OddOrder.Peterfalvi.S10.BGTheoremENonTypeICovering data)
    (_hall : ∀ N : Subgroup G, N ∈ maximalSubgroups G → IsTypeI N) :
    False := by
  sorry

/-- **A type-I maximal has no "hat" beyond its kernel** (the (12.17)-side collapse of the (8.14)
signalizer support): for a type-I maximal `N`, every element of `N` whose `N_σ`-centralizer is
nontrivial already lies in `N_σ`.

By (12.7) (`typeI_frobenius`) `N` is a Frobenius group with kernel `N_F = N_σ`
(`maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2`), and the centralizer of a nonidentity
kernel element is contained in the kernel (Isaacs Thm 6.4 (1) ⇒ (4),
`IsFrobeniusGroup.centralizer_kernel_le`); so `x ∈ N` centralizing some `1 ≠ r ∈ N_σ` lies in
`N_σ`. -/
private theorem typeI_hatMsigma_subset_Msigma (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {N : Subgroup G} (hNmax : N ∈ maximalSubgroups G) (hNI : IsTypeI N) :
    OddOrder.BG.Ch4.S16.hatMsigma N ⊆ (OddOrder.BG.Ch3.S10.Msigma N : Set G) := by
  rintro x ⟨hxN, hRne⟩
  -- a nonidentity element `r` of `N_σ ⊓ C_G(x)`
  have hr : ∃ r ∈ OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G), r ≠ 1 := by
    by_contra h
    push Not at h
    exact hRne (Subgroup.eq_bot_iff_forall _ |>.mpr h)
  obtain ⟨r, hr, hr1⟩ := hr
  have hrσ : r ∈ OddOrder.BG.Ch3.S10.Msigma N := (Subgroup.mem_inf.mp hr).1
  have hrC : r ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp hr).2
  have hrN : r ∈ N := OddOrder.BG.Ch3.S10.Msigma_le N hrσ
  -- `N` is Frobenius with kernel `typeF.H = N_F = N_σ` ((12.7)).
  obtain ⟨fd, -⟩ := typeI_frobenius hG hnoV hNmax hNI
  have hHσ : fd.typeI.typeF.H = OddOrder.BG.Ch3.S10.Msigma N := by
    rw [fd.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2 hG hNmax
      (Or.inl ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hNmax).1.mp hNI))
  have hrH : r ∈ fd.typeI.typeF.H := by rw [hHσ]; exact hrσ
  -- inside `↥N`: `x` centralizes the nonidentity kernel element `r`, so `x` is in the kernel.
  have hcent := fd.frobenius.centralizer_kernel_le ⟨r, hrN⟩ (Subgroup.mem_subgroupOf.mpr hrH)
    (fun h => hr1 (Subtype.ext_iff.mp h))
  have hxbar : (⟨x, hxN⟩ : ↥N) ∈ Subgroup.centralizer ({(⟨r, hrN⟩ : ↥N)} : Set ↥N) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hrC).symm
  have hxH : x ∈ fd.typeI.typeF.H := Subgroup.mem_subgroupOf.mp (hcent hxbar)
  rw [hHσ] at hxH
  exact hxH

/-- **Peterfalvi (12.17), the no-escaping control**: in the all-type-I configuration, no
centralizer of an `M_σ#`-element escapes `M`.

An escape produces the BG Theorem D(4) neighbour `N` (`exists_RData_escape_structure`, the
sorry-free escape structure of Theorem D) with `x ∈ Â_σ(N) ∖ N_σ`; but `N` is type I (`hall`),
so `Â_σ(N) ⊆ N_σ` (`typeI_hatMsigma_subset_Msigma`) — contradiction.  This is the exact
hypothesis under which the faithful BG Theorem E cover collapses onto the Frobenius kernels
(`Mtilde_eq_sigmaSharp_of_forall_centralizer_le`, issue 9080). -/
private theorem allTypeI_centralizer_le (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hall : ∀ N : Subgroup G, N ∈ maximalSubgroups G → IsTypeI N)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∀ x ∈ OddOrder.BG.Ch4.S14.sigmaSharp M, Subgroup.centralizer ({x} : Set G) ≤ M := by
  intro x hx
  by_contra hesc
  obtain ⟨R, -, N, ⟨hNmem, -, -, hxA, -, -, -⟩, -⟩ :=
    OddOrder.BG.Ch4.S16.exists_RData_escape_structure hG hM hx hesc
  exact hxA.2 (typeI_hatMsigma_subset_Msigma hG hnoV hNmem.1 (hall N hNmem.1) hxA.1.1)

/-- **§8/§10 covering inputs to Peterfalvi (12.17)** — the all-type-I case of Theorem (8.8).

When every maximal subgroup of `G` is of type I, the §8 covering theory (BG Theorem E, (8.17), and
the escaping-centralizer control (8.13.c1)) supplies a finite family of conjugacy-class
representatives `reps i` whose maximal nilpotent normal Hall subgroups `(reps i)_F`:
* number at least two (`two_le`);
* have TI sharp-sets `((reps i)_F)#` (`isTI`, via (8.13.c1)+(2.3));
* are pairwise of coprime order (`coprime`, via the (8.17) prime partition);
* cover `G#` up to conjugacy (`covers`, the (8.17.a) type-I covering).

These are exactly the inputs the (12.17) argument feeds to (7.11), beyond the genuinely
group-theoretic family facts (Frobenius structure, `reps i = N_G((reps i)_F)`) discharged in
`not_all_maximal_typeI`. -/
structure TypeICovering (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) where
  /-- Number of conjugacy classes of maximal subgroups. -/
  k : ℕ
  /-- Conjugacy-class representatives of the maximal subgroups. -/
  reps : Fin k → Subgroup G
  /-- Each representative is maximal. -/
  reps_maximal : ∀ i, reps i ∈ maximalSubgroups G
  /-- (7.10): at least two members. -/
  two_le : 2 ≤ k
  /-- (8.13.c1)+(2.3): each kernel sharp-set is a TI-subset. -/
  isTI : ∀ i, IsTISubset ((maxNilpotentNormalHall (reps i) : Set G) \ {1}) (reps i)
  /-- (8.17): the kernels have pairwise-coprime order. -/
  coprime : ∀ ⦃i j⦄, i ≠ j →
    Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall (reps i)))
      (Nat.card ↥(maxNilpotentNormalHall (reps j)))
  /-- (8.17.a): the conjugates of the kernels cover every nonidentity element. -/
  covers : ∀ x : G, x ≠ 1 →
    ∃ i, ∃ g : G, g * x * g⁻¹ ∈ (maxNilpotentNormalHall (reps i) : Set G) \ {1}


/-- **Peterfalvi (8.17)/(8.13.c1), all-type-I case**: the §8 covering inputs of (12.17) exist.

Built as an honest reduction from BG Theorem E (`S10.bgTheoremE_cover_data`): in the all-type-I case
every representative `M_i` has `data.tau i = .I` (type exclusivity, `not_isTypeI_of_isTypeNonI`), so
`mainSubgroup (M_i) (τ_i) = (M_i)_F`.  The `reps`/`reps_maximal` plumbing, `coprime` (the (8.17)
prime-factor partition is disjoint, hence the kernels are coprime), `two_le` (a single class would
make `|G#| = (|M_s|-1)|G:M| < |G|-1 = |G#|`), and `covers` (the (12.17)-faithful collapse, issue
9080: no centralizer escapes by (12.7)+Theorem D(4) (`allTypeI_centralizer_le`), so the faithful
BG Cor 14.9 cover collapses onto the kernels, `Mtilde_eq_sigmaSharp_of_forall_centralizer_le`) are
all discharged.  Two upstream facts remain isolated as residual sorries: `isTI`, the
escaping-centralizer control (8.13.c1)+(2.3) making each kernel sharp-set a TI-subset; and the
selection of the type-I cover branch under `hall`, the (8.8.a) dichotomy (BG §16, parallel to
`theorem88_dichotomy`). -/
theorem exists_typeICovering (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) :
    Nonempty (TypeICovering hG hall) := by
  classical
  -- `BGTheoremECoverData.ι : Type*` is universe-polymorphic; pin the index type to `Type 0`.
  obtain ⟨data, hcover⟩ := OddOrder.Peterfalvi.S10.bgTheoremE_cover_data.{_, 0} hG
  haveI : Fintype data.ι := data.finite_index
  -- **Every representative is type I**, so `data.tau i = .I` and hence
  -- `mainSubgroup (M_i) (τ_i) = (M_i)_F`.  Type exclusivity is
  -- `not_isTypeI_of_isTypeNonI` (BG §16): a type-`P` (= non-type-I) maximal is not type I.
  have hMF : ∀ i, mainSubgroup (data.reps i) (data.tau i)
      = maxNilpotentNormalHall (data.reps i) := by
    intro i
    have hI : IsTypeI (data.reps i) := hall _ (data.maximal i)
    have htau := data.typed i
    have htauI : data.tau i = PeterfalviType.I := by
      by_contra hne
      have hNonI : IsTypeNonI (data.reps i) := by
        cases hc : data.tau i with
        | I => exact absurd hc hne
        | II => rw [hc] at htau; exact Or.inl htau
        | III => rw [hc] at htau; exact Or.inr (Or.inl htau)
        | IV => rw [hc] at htau; exact Or.inr (Or.inr (Or.inl htau))
        | V => rw [hc] at htau; exact Or.inr (Or.inr (Or.inr htau))
      exact OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG (data.maximal i) hNonI hI
    simp only [htauI, mainSubgroup]
  -- The `Fin k`-indexing of the representatives (`e : data.ι ≃ Fin k`).
  set e := Fintype.equivFin data.ι with he
  rcases hcover with hTypeI | hNonTypeI
  · -- **(8.8.a) type-I cover branch.**
    refine ⟨{
      k := Fintype.card data.ι
      reps := fun j => data.reps (e.symm j)
      reps_maximal := fun j => data.maximal (e.symm j)
      two_le := ?_
      isTI := ?_
      coprime := ?_
      covers := ?_ }⟩
    · -- **`two_le`** (discharged): at least two conjugacy classes of maximal subgroups (7.10).
      -- A single class would force `|G#| = |thickenedA1(M)| = (|M_s| - 1)|G : M|`; but
      -- `(|M_s| - 1)|G : M| ≤ (|M| - 1)|G : M| = |G| - |G : M| ≤ |G| - 2 < |G| - 1 = |G#|`, and an
      -- empty class would force `|G#| = 0`, both impossible.  No counting of disjoint unions is
      -- needed: a one-element index makes the cover `⋃ᵢ thickenedA1(Mᵢ)` equal to a single
      -- `thickenedA1(M)`, whose cardinality is strictly below `|G#|`.
      haveI : Nontrivial G := hG.simple.toNontrivial
      by_contra hlt
      rw [Nat.not_le] at hlt
      have hcard01 : Fintype.card data.ι = 0 ∨ Fintype.card data.ι = 1 := by omega
      rcases hcard01 with h0 | h1
      · -- empty index: the cover is empty, but `G#` contains a nonidentity element.
        rw [Fintype.card_eq_zero_iff] at h0
        have hempty : (⋃ i, data.cover i) = ∅ :=
          Set.iUnion_of_empty _
        rw [← hTypeI.cover_nonidentity] at hempty
        obtain ⟨b, hb⟩ := exists_ne (1 : G)
        have hbmem : b ∈ sharpSubgroup (⊤ : Subgroup G) := by
          simp only [sharpSubgroup, Subgroup.coe_top, Set.mem_sdiff, Set.mem_univ, true_and,
            Set.mem_singleton_iff]
          exact hb
        rw [hempty] at hbmem
        exact hbmem.elim
      · -- one class: `⋃ᵢ thickenedA1(Mᵢ) = thickenedA1(M)`, of cardinality `< |G#|`.
        obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp h1
        have hunion : (⋃ i, data.cover i) = data.cover i₀ := by
          ext x
          simp only [Set.mem_iUnion]
          exact ⟨fun ⟨i, hi⟩ => by rwa [hi₀ i] at hi, fun hx => ⟨i₀, hx⟩⟩
        rw [← hTypeI.cover_nonidentity] at hunion
        have hcard_eq : Nat.card ↥(data.cover i₀) = Nat.card G - 1 := by
          rw [Nat.card_coe_set_eq, ← hunion]
          show ((↑(⊤ : Subgroup G) : Set G) \ {1}).ncard = Nat.card G - 1
          rw [Subgroup.coe_top, Set.ncard_diff_singleton_of_mem (Set.mem_univ 1), Set.ncard_univ]
        rw [data.cover_card i₀] at hcard_eq
        -- Arithmetic contradiction.
        have hmain_le : mainSubgroup (data.reps i₀) (data.tau i₀) ≤ data.reps i₀ :=
          (hMF i₀).le.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le (data.reps i₀))
        have ham : Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀))
            ≤ Nat.card ↥(data.reps i₀) := Subgroup.card_le_of_le hmain_le
        have hidx0 : (data.reps i₀).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        have hidx1 : (data.reps i₀).index ≠ 1 :=
          fun h => (data.maximal i₀).1 (Subgroup.index_eq_one.mp h)
        have hidx : 2 ≤ (data.reps i₀).index := by omega
        have hmidx : Nat.card ↥(data.reps i₀) * (data.reps i₀).index = Nat.card G :=
          Subgroup.card_mul_index (data.reps i₀)
        have hm_pos : 0 < Nat.card ↥(data.reps i₀) := Nat.card_pos
        have hG2 : 2 ≤ Nat.card G :=
          le_trans hidx (hmidx ▸ Nat.le_mul_of_pos_left (data.reps i₀).index hm_pos)
        have hb1 : (Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀)) - 1)
            * (data.reps i₀).index
            ≤ (Nat.card ↥(data.reps i₀) - 1) * (data.reps i₀).index :=
          Nat.mul_le_mul_right _ (Nat.sub_le_sub_right ham 1)
        have hrhs : (Nat.card ↥(data.reps i₀) - 1) * (data.reps i₀).index
            = Nat.card G - (data.reps i₀).index := by rw [Nat.sub_one_mul, hmidx]
        rw [hrhs] at hb1
        -- `hcard_eq : P = |G| - 1`, `hb1 : P ≤ |G| - idx`, `idx ≥ 2`, `|G| ≥ 2` ⟹ `False`.
        set P := (Nat.card ↥(mainSubgroup (data.reps i₀) (data.tau i₀)) - 1)
          * (data.reps i₀).index with hP
        omega
    · -- `isTI`: each kernel sharp-set `((M_i)_F)#` is a TI-subset, by (8.13.c1)+(2.3).
      -- Honest derivation: `FittingIsTI (M_j)` (the (8.13.c1) escaping-centralizer gate,
      -- `allTypeI_fittingIsTI`) feeds `maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`
      -- (S16, `M_F# TI` with normalizer `N_G(M_F)`); and `N_G(M_F) = M_j` for the type-I maximal
      -- (`maximalSubgroup_eq_normalizer_maxNilpotentNormalHall`, kernel `≠ ⊥`).
      intro j
      set M := data.reps (e.symm j) with hMdef
      have hMmax : M ∈ maximalSubgroups G := data.maximal (e.symm j)
      have hMI : IsTypeI M := hall _ hMmax
      -- `M_F ≠ ⊥` for the type-I maximal.
      have hMFne : maxNilpotentNormalHall M ≠ ⊥ := by
        obtain ⟨td⟩ := hMI
        rw [← td.typeF.H_eq]
        exact td.typeF.H_nontrivial
      -- `N_G(M_F) = M`.
      have hNorm : M = Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
        maximalSubgroup_eq_normalizer_maxNilpotentNormalHall hG hMmax hMFne
      -- `M_F#` is TI with normalizer `N_G(M_F)`, from `FittingIsTI M`; rewrite `N_G(M_F) = M` in
      -- the TI witness (not in the goal — that would fold `M` inside `maxNilpotentNormalHall M`).
      have hTI :=
        OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG hMmax
          (allTypeI_fittingIsTI hG hMmax hMI hall)
      rw [← hNorm] at hTI
      -- `sharpSubgroup (maxNilpotentNormalHall M)` unfolds to `(maxNilpotentNormalHall M) \ {1}`.
      exact hTI
    · -- **`coprime`** (discharged): the kernels have pairwise-coprime order because the (8.17)
      -- partition makes their prime-factor sets disjoint.
      intro j j' hjj'
      have hne : e.symm j ≠ e.symm j' := fun h => hjj' (e.symm.injective h)
      have hdisj := data.primeFactors_disjoint (e.symm j) (e.symm j') hne
      simp only [hMF] at hdisj
      have hcard1 : Nat.card ↥(maxNilpotentNormalHall (data.reps (e.symm j))) ≠ 0 :=
        Nat.card_pos.ne'
      have hcard2 : Nat.card ↥(maxNilpotentNormalHall (data.reps (e.symm j'))) ≠ 0 :=
        Nat.card_pos.ne'
      exact (Nat.disjoint_primeFactors hcard1 hcard2).mp hdisj
    · -- **`covers`** (discharged, the (12.17)-faithful route of issue 9080): the faithful BG
      -- cover `𝒞_G(M̃)` (BG Cor 14.9, all-type-`F`) covers `G#`; in the all-type-I case no
      -- centralizer escapes (`allTypeI_centralizer_le`, from (12.7) via Theorem D(4)), so every
      -- signalizer is trivial and `M̃ = M_σ# = (M_F)#`
      -- (`Mtilde_eq_sigmaSharp_of_forall_centralizer_le`); finally the witness maximal is moved
      -- to its conjugacy representative.
      intro x hx1
      have htypeF : ∀ M' ∈ maximalSubgroups G, OddOrder.BG.Ch4.S14.IsTypeF M' := fun M' hM' =>
        (OddOrder.BG.Ch4.S16.proposition_type_classification hG hM').1.mp (hall M' hM')
      have hxsharp : x ∈ sharpSubgroup (⊤ : Subgroup G) := ⟨Subgroup.mem_top x, hx1⟩
      rw [OddOrder.BG.Ch4.S14.sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF hG
        htypeF] at hxsharp
      obtain ⟨M, hMmax, hxM⟩ := Set.mem_iUnion₂.mp hxsharp
      rw [OddOrder.Peterfalvi.S10.Mtilde_eq_sigmaSharp_of_forall_centralizer_le hG _ hMmax
        (allTypeI_centralizer_le hG hnoV hall hMmax)] at hxM
      -- `x = c * t * c⁻¹` with `t ∈ M_σ#`; move `M` to its representative `conj g • M = reps i`.
      obtain ⟨t, ht, c, hc⟩ := hxM
      obtain ⟨i, g, hgconj⟩ := data.representatives M hMmax
      refine ⟨e i, g * c⁻¹, ?_⟩
      have hreps : data.reps (e.symm (e i)) = data.reps i := by rw [Equiv.symm_apply_apply]
      have hyt : (g * c⁻¹) * x * (g * c⁻¹)⁻¹ = g * t * g⁻¹ := by rw [← hc]; group
      rw [hreps, hyt]
      -- `g t g⁻¹ ∈ (conj g • M)_σ# = (reps i)_σ# = ((reps i)_F)#`
      have hmem : g * t * g⁻¹ ∈ MulAut.conj g • OddOrder.BG.Ch4.S14.sigmaSharp M := by
        rw [show g * t * g⁻¹ = MulAut.conj g • t from by
          rw [MulAut.smul_def, MulAut.conj_apply]]
        exact Set.smul_mem_smul_set ht
      rw [OddOrder.BG.Ch4.S14.sigmaSharp_conj_smul, hgconj] at hmem
      have hσeq : OddOrder.BG.Ch4.S14.sigmaSharp (data.reps i)
          = (maxNilpotentNormalHall (data.reps i) : Set G) \ {1} := by
        rw [OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2 hG
          (data.maximal i) (Or.inl (htypeF _ (data.maximal i)))]
        rfl
      rw [← hσeq]
      exact hmem
  · -- **(8.8.b) non-type-I cover branch**: ruled out when every maximal subgroup is type I.
    -- This is the all-type-I case of the (8.8) dichotomy (`theorem88_dichotomy`); under `hall`
    -- BG Theorem E returns the type-I cover, never the two-exceptional-subgroup case (the
    -- exceptional `W` of `hNonTypeI` is the normalizer of a non-type-I maximal).  Isolating that
    -- is the BG §16 (8.8.a) residual (`not_nonTypeICovering_of_all_typeI`).
    exfalso
    obtain ⟨hcov⟩ := hNonTypeI
    exact not_nonTypeICovering_of_all_typeI hG hcov hall

/-- **Peterfalvi (12.17), non-existence half**: in a minimal simple group of odd order, not every
maximal subgroup is of type I.

*Proof.*  Assume otherwise.  The §8 covering theory (`exists_typeICovering`) provides the family of
conjugacy-class representatives `reps i` of the maximal subgroups, whose kernels `(reps i)_F` are
pairwise-coprime TI-subsets covering `G#`.  Each `reps i` is a Frobenius group with kernel
`(reps i)_F` by (12.7) (`typeI_frobenius`) and equals its own `N_G((reps i)_F)`
(`maximalSubgroup_eq_normalizer_maxNilpotentNormalHall`), so these data assemble into a Frobenius
family in the sense of (7.10) (`S09.FrobeniusFamily`).  The covering makes `G₀ = {1}`, contradicting
(7.11) (`S09.not_trivial_G0`). -/
theorem not_all_maximal_typeI (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M) :
    ¬ (∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) := by
  intro hall
  obtain ⟨cov⟩ := exists_typeICovering hG hnoV hall
  let F : OddOrder.Peterfalvi.S09.FrobeniusFamily G cov.k :=
    { L := cov.reps
      H := fun i => maxNilpotentNormalHall (cov.reps i)
      two_le := cov.two_le
      kernel_le := fun i => OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le (cov.reps i)
      isFrobenius := fun i => by
        obtain ⟨fd, -⟩ := typeI_frobenius hG hnoV (cov.reps_maximal i) (hall _ (cov.reps_maximal i))
        refine ⟨fd.complement, ?_⟩
        rw [← fd.typeI.typeF.H_eq]
        exact fd.frobenius
      normalizer_eq := fun i =>
        maximalSubgroup_eq_normalizer_maxNilpotentNormalHall hG (cov.reps_maximal i) (by
          obtain ⟨td⟩ := hall _ (cov.reps_maximal i)
          rw [← td.typeF.H_eq]
          exact td.typeF.H_nontrivial)
      isTI := cov.isTI
      coprime_kernel := cov.coprime }
  have hG0 : F.G0 = {(1 : G)} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨F.one_mem_G0, fun x hx => ?_⟩
    by_contra hx1
    obtain ⟨i, g, hg⟩ := cov.covers x hx1
    exact (F.mem_G0_iff.mp hx) i ⟨g, hg⟩
  exact OddOrder.Peterfalvi.S09.not_trivial_G0 F hG.odd hG0

end Theorem1217

/-! ## (12.17) → (8.8): the case-(b) dichotomy -/

/-- **Type-`P` ⟹ non-Type-I** (Proposition 16.1(b)(c)(d)): a type-`P` maximal subgroup of a minimal
simple group of odd order is one of the Types II–V.  Split `κ(M)` against `π(M) - σ(M)`: equal gives
`P₁`, which is Type V (`M_F = M_σ`) or Type III/IV (`M_F ≠ M_σ`); unequal gives `P₂` = Type II.  This
is the local `typeP_imp_nonI` of BG Theorem I's dichotomy proof, isolated here for
`theorem88_dichotomy`. -/
private theorem isTypeNonI_of_isTypeP [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {N : Subgroup G} (hN : N ∈ maximalSubgroups G)
    (hP : OddOrder.BG.Ch4.S14.IsTypeP N) : IsTypeNonI N := by
  obtain ⟨_, hbII, hcIII_IV, hdV, _, _⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hN
  by_cases hk : OddOrder.BG.Ch4.S14.kappa N = OddOrder.BG.Ch4.S14.sigmaComplementPrimes N
  · have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 N := ⟨hP, hk⟩
    by_cases hMF : OddOrder.BG.Ch4.S15.MF N = OddOrder.BG.Ch3.S10.Msigma N
    · exact Or.inr (Or.inr (Or.inr (hdV.mpr ⟨hP1, hMF⟩)))
    · rcases hcIII_IV.mpr ⟨hP1, hMF⟩ with hIII | hIV
      · exact Or.inr (Or.inl hIII)
      · exact Or.inr (Or.inr (Or.inl hIV))
  · exact Or.inl (hbII.mpr ⟨hP, hk⟩)

/-- **Theorem (8.8) dichotomy** (BG §16): for a minimal simple group of odd order, either every
maximal subgroup is of type I, or the case-(b) pairing data `Theorem88CaseBData` exists.

*Proof.*  If some maximal `S` is not type I, then it is type `P` (Proposition 16.1(a): `TypeI ⟺
TypeF`, and `TypeF ⟺ κ(S) = ∅`).  BG Theorem 14.7 duality (`typeP_duality`) applied to `S` with a
`κ(S)`-Hall subgroup `K` produces the complement `S = S' ⋊ K` (first conjunct), the dual maximal
`T = M*`, the cyclic factor `W = K ⊔ K*`, the type-II witness, and the `κ(M*)`-Hall `K*`.  Applying
the duality again at `M*` gives the second complement `T = T' ⋊ K*`.  The `κ`-Hall complement `K`
plays the role of the case-(b) factor `W₁` (both `K` and the type-`P` `W₁` complement `S'`, Peterfalvi
(8.8.b1)).  Cites the merged BG §16 `typeP_duality` and `proposition_type_classification`; the
remaining hard content lives in their (issue-8015) residuals. -/
theorem theorem88_dichotomy [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M) ∨
      Nonempty (OddOrder.Peterfalvi.S12.Theorem88CaseBData G) := by
  classical
  by_cases hall : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeI M
  · exact Or.inl hall
  · refine Or.inr ?_
    push Not at hall
    obtain ⟨S, hS, hSnotI⟩ := hall
    haveI : IsSolvable ↥S := hG.solvable_of_mem_maximalSubgroups hS
    -- `S` not type I ⟹ `S` type `P` (Prop 16.1(a): `TypeI ⟺ TypeF`, `TypeF ⟺ κ(S) = ∅`).
    have hSP : OddOrder.BG.Ch4.S14.IsTypeP S := by
      have hiff := (OddOrder.BG.Ch4.S16.proposition_type_classification hG hS).1
      have hnotF : ¬ OddOrder.BG.Ch4.S14.IsTypeF S := fun hF => hSnotI (hiff.mpr hF)
      rw [OddOrder.BG.Ch4.S14.IsTypeP, Set.nonempty_iff_ne_empty]
      exact fun he => hnotF he
    -- A `κ(S)`-Hall subgroup `K` of `S` (Hall's theorem in the solvable `S`).
    obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥S) (OddOrder.BG.Ch4.S14.kappa S)
    set K : Subgroup G := K'.map S.subtype with hKdef
    have hKeq : K.subgroupOf S = K' :=
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective K'
    have hK : Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa S) (K.subgroupOf S) := by
      rw [hKeq]; exact hK'
    set Kstar : Subgroup G :=
      OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G) with hKstardef
    -- BG Theorem 14.7 duality at `S`: `S = S' ⋊ K` (`hScompl`), the dual `M*`, its data.
    obtain ⟨hScompl, _, Mstar, ⟨hMstarMem, hMstarP, hSnconjMstar,
        ⟨hKstarMstar, hKstar_hall, hK_eq⟩, hcyc, _, hP2disj, _⟩, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hS hSP (Subgroup.map_subtype_le K') hK hKstardef
    -- Apply duality again at `M*` with its `κ`-Hall `K*`: `M* = (M*)' ⋊ K*` (`hTcompl`).
    obtain ⟨hTcompl, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hMstarMem hMstarP hKstarMstar hKstar_hall hK_eq
    exact ⟨{
      S := S, T := Mstar, W1 := K, W2 := Kstar, W := K ⊔ Kstar
      S_maximal := hS, T_maximal := hMstarMem
      S_ne_T := by
        intro hST
        rw [hST] at hSnconjMstar
        exact hSnconjMstar (OddOrder.BG.Ch4.S14.IsConjugateSubgroup.refl Mstar)
      W_eq := rfl, W_cyclic := hcyc
      S_nonI := isTypeNonI_of_isTypeP hG hS hSP
      T_nonI := isTypeNonI_of_isTypeP hG hMstarMem hMstarP
      one_typeII := hP2disj.imp
        (fun h => (OddOrder.BG.Ch4.S16.proposition_type_classification hG hS).2.1.mpr h)
        (fun h => (OddOrder.BG.Ch4.S16.proposition_type_classification hG hMstarMem).2.1.mpr h)
      W1_le_S := Subgroup.map_subtype_le K'
      W2_le_T := hKstarMstar
      S_compl := hScompl
      T_compl := hTcompl }⟩

/-- **Peterfalvi (12.17)**: the all-type-I case of Theorem (8.8) is impossible, so the case-(b)
data of (8.8) exists.  Immediate from the (8.8) dichotomy (`theorem88_dichotomy`) and the
non-existence half `not_all_maximal_typeI`. -/
theorem theorem88_caseB_holds [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M) :
    Nonempty (OddOrder.Peterfalvi.S12.Theorem88CaseBData G) :=
  (theorem88_dichotomy hG).resolve_left (not_all_maximal_typeI hG hnoV)

end OddOrder.Peterfalvi.S14
