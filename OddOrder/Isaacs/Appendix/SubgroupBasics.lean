/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Appendix.DirectDiamond
import OddOrder.Isaacs.Ch02_Subnormality.Theorem211Wielandt
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Index
import Mathlib.Data.Set.Card
import Mathlib.Order.SupIndep
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max

/-!
# Isaacs, *Finite Group Theory*, Appendix — elementary subgroup facts

This file collects several elementary results from the appendix ("The Basics") of
I. M. Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), used implicitly throughout the book.
It completes the appendix gaps tracked in `issues/3018-isaacs-appendix-x-gaps.md` that are not
already covered by mathlib or elsewhere in this repository.

## Main results

* **Corollary X.5** (Frattini subgroup = nongenerators):
  * `OddOrder.Isaacs.Appendix.mem_frattini_of_nongenerating` — the *converse* half of Isaacs'
    statement: if `u` has the property that adjoining it to any non-generating set keeps it
    non-generating, then `u ∈ Φ(G)`.
  * `OddOrder.Isaacs.Appendix.mem_frattini_iff_nongenerating` — the full characterization (the
    forward half is mathlib's `frattini_nongenerating`, see the note below).

* **Corollary X.11** (`OddOrder.Isaacs.Appendix.relIndex_eq_index_iff_mul_eq_univ`): for subgroups
  `H`, `K` of a finite group, `|K : H ∩ K| = |G : H|` **iff** the set product `HK` is all of `G`.
  The inequality `|K : H ∩ K| ≤ |G : H|` is mathlib's `Subgroup.relIndex_le_of_le_right`
  (see the note below); the equality clause is the content here.

* **Theorem X.22** (`OddOrder.Isaacs.Appendix.iSupIndep_iff_disjoint_biSup_lt`), the internal
  direct-product criterion: a finite family `M : ι → Subgroup G` of **normal** subgroups is
  independent (mathlib's `iSupIndep`, i.e. an internal direct product) **iff** the ordered
  *prefix* condition `(M₁ ⋯ M_{k-1}) ∩ M_k = 1` holds, written here as
  `Disjoint (⨆ j < k, M j) (M k)` for every `k`. The hard direction (prefix `⟹` independent)
  uses the modular law for normal subgroups, supplied here as
  `disjoint_sup_of_normal` (mathlib does not have `IsModularLattice (Subgroup G)` unless `G` is
  commutative). Isaacs' standing hypothesis `G = M₁ ⋯ M_r` (i.e. `⨆ i, M i = ⊤`) is orthogonal
  to this equivalence and is omitted; the family-level statement above is what carries the
  mathematical content.

## Results already covered elsewhere (documented, not re-proved)

* **X.5, first sentence** (`⟨X⟩ < G ⟹ ⟨X ∪ Φ(G)⟩ < G`) is the contrapositive of mathlib's
  `frattini_nongenerating : K ⊔ frattini G = ⊤ → K = ⊤` (with `K = ⟨X⟩ = closure X`, using
  `closure_union` to rewrite `⟨X ∪ Φ(G)⟩ = closure X ⊔ frattini G`). It is subsumed by the
  forward direction of `mem_frattini_iff_nongenerating`.

* **X.11, inequality** `|K : H ∩ K| ≤ |G : H|` is mathlib's `Subgroup.relIndex_le_of_le_right`
  applied with `L = ⊤` (recall `Subgroup.relIndex_top_right : H.relIndex ⊤ = H.index` and
  `H.relIndex K = |K : H ∩ K|`).

* **X.12** (coprime indices `⟹ HK = G` as a *set product*) is already proved in this repository
  as `OddOrder.Isaacs.Ch03.set_mul_eq_univ_of_coprime_index`
  (`OddOrder/Isaacs/Ch03_SplitExtensions/Theorem315.lean`); the weaker join form
  `H ⊔ K = ⊤` is `OddOrder.Isaacs.Ch03.sup_eq_top_of_coprime_index`. No new work is needed here.

Note on X.11: Isaacs writes the equality condition as "`HK = G`". This means the *set product*
`↑H * ↑K` equals all of `G`, which is **strictly stronger** than the join `H ⊔ K = ⊤`. (E.g. in
`S₃`, two distinct order-two subgroups `H, K` have `H ⊔ K = ⊤` but `|↑H * ↑K| = 4 ≠ 6`.) The
faithful statement therefore uses `(↑H * ↑K : Set G) = Set.univ`.

See `issues/3018-isaacs-appendix-x-gaps.md`.
-/

open scoped Pointwise

namespace OddOrder.Isaacs.Appendix

variable {G : Type*} [Group G]

/-! ### X.5 — the Frattini subgroup is the set of nongenerators -/

/-- **Isaacs, Finite Group Theory, Corollary X.5** (converse half).
If `u ∈ G` has the property that whenever a set `X` fails to generate `G` (`closure X ≠ ⊤`) the
set `X ∪ {u}` also fails to generate `G`, then `u` lies in the Frattini subgroup `Φ(G)`.

This is the nontrivial direction of Isaacs' characterization of `Φ(G)` as the set of
"nongenerators". No finiteness (or coatomicity) hypothesis is needed for this direction. -/
theorem mem_frattini_of_nongenerating (u : G)
    (hu : ∀ X : Set G, Subgroup.closure X ≠ ⊤ → Subgroup.closure (X ∪ {u}) ≠ ⊤) :
    u ∈ frattini G := by
  -- `frattini G = ⨅ (M coatom), M`, so it suffices to show `u ∈ M` for every coatom `M`.
  simp only [frattini, Order.radical, Subgroup.mem_iInf, Set.mem_setOf_eq]
  intro M hM
  by_contra hMu
  -- `closure ↑M = M ≠ ⊤`, so the hypothesis applies to `X = ↑M`.
  have hMne : Subgroup.closure (M : Set G) ≠ ⊤ := by rw [Subgroup.closure_eq]; exact hM.1
  refine hu (M : Set G) hMne ?_
  -- `closure (↑M ∪ {u}) = M ⊔ closure {u}`, and this strictly contains the coatom `M`.
  rw [Subgroup.closure_union, Subgroup.closure_eq]
  refine hM.2 _ (lt_of_le_of_ne le_sup_left ?_)
  intro heq
  exact hMu ((by rw [heq]; exact le_sup_right : Subgroup.closure {u} ≤ M)
    (Subgroup.subset_closure (Set.mem_singleton u)))

/-- **Isaacs, Finite Group Theory, Corollary X.5** (full characterization).
An element `u` of a group `G` (whose subgroup lattice is coatomic — e.g. any finite group) lies
in the Frattini subgroup `Φ(G)` **iff** it is a *nongenerator*: adjoining `u` to any set that
fails to generate `G` still fails to generate `G`.

The forward direction is a restatement of mathlib's `frattini_nongenerating`; the backward
direction is `mem_frattini_of_nongenerating`. -/
theorem mem_frattini_iff_nongenerating [IsCoatomic (Subgroup G)] (u : G) :
    u ∈ frattini G ↔
      ∀ X : Set G, Subgroup.closure X ≠ ⊤ → Subgroup.closure (X ∪ {u}) ≠ ⊤ := by
  refine ⟨fun hu X hX hXu => hX ?_, mem_frattini_of_nongenerating u⟩
  refine frattini_nongenerating (K := Subgroup.closure X) ?_
  have h1 : Subgroup.closure {u} ≤ frattini G := by
    rw [Subgroup.closure_le]; intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact hu
  have h2 : Subgroup.closure (X ∪ {u}) ≤ Subgroup.closure X ⊔ frattini G := by
    rw [Subgroup.closure_union]; exact sup_le_sup_left h1 _
  rw [hXu] at h2
  exact top_le_iff.mp h2

/-! ### X.11 — `|K : H ∩ K| ≤ |G : H|` with equality iff `HK = G` -/

/-- **Isaacs, Finite Group Theory, Corollary X.11** (equality clause).
For subgroups `H`, `K` of a finite group `G`, the relative index `|K : H ∩ K|` (written
`H.relIndex K` in mathlib) equals `|G : H|` (written `H.index`) **iff** the set product `HK`
is the whole group. The inequality `H.relIndex K ≤ H.index` is `Subgroup.relIndex_le_of_le_right`
(with `L = ⊤`); here we supply the equality condition.

Note that "`HK = G`" means the *set product* `↑H * ↑K = Set.univ`, which is strictly stronger
than `H ⊔ K = ⊤`. -/
theorem relIndex_eq_index_iff_mul_eq_univ [Finite G] (H K : Subgroup G) :
    H.relIndex K = H.index ↔ (H : Set G) * (K : Set G) = Set.univ := by
  classical
  -- Positivity of the relevant cardinalities/indices.
  have hn : 0 < Nat.card G := Nat.card_pos
  have hapos : 0 < Nat.card (H : Type _) := Nat.card_pos
  have hdpos : 0 < Nat.card ((H ⊓ K : Subgroup G) : Type _) := Nat.card_pos
  have hKpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  -- Basic index identities.
  have cB : Nat.card (K : Type _) * K.index = Nat.card G := Subgroup.card_mul_index K
  have cD : Nat.card ((H ⊓ K : Subgroup G) : Type _) * (H ⊓ K).index = Nat.card G :=
    Subgroup.card_mul_index (H ⊓ K)
  have rIV : H.relIndex K * K.index = (H ⊓ K).index := by
    rw [← Subgroup.inf_relIndex_right]; exact Subgroup.relIndex_mul_index inf_le_right
  -- `|K : H ∩ K| · |H ∩ K| = |K|`.
  have hRel : H.relIndex K * Nat.card ((H ⊓ K : Subgroup G) : Type _) = Nat.card (K : Type _) := by
    have e : Nat.card ((H ⊓ K : Subgroup G) : Type _) * (H ⊓ K).index
        = Nat.card (K : Type _) * K.index := by rw [cD, cB]
    rw [← rIV, ← mul_assoc] at e
    have := Nat.eq_of_mul_eq_mul_right hKpos e
    rw [mul_comm]; exact this
  -- Lemma X.2: `|HK| · |H ∩ K| = |H| · |K|`.
  have x2 : Nat.card ((H : Set G) * (K : Set G)) * Nat.card ((H ⊓ K : Subgroup G) : Type _)
      = Nat.card (H : Type _) * Nat.card (K : Type _) :=
    OddOrder.Isaacs.Ch02.card_set_mul_card_inf H K
  -- Hence `|K : H ∩ K| · |H| = |HK|`.
  have hP : H.relIndex K * Nat.card (H : Type _) = Nat.card ((H : Set G) * (K : Set G)) := by
    have e2 : (H.relIndex K * Nat.card (H : Type _))
          * Nat.card ((H ⊓ K : Subgroup G) : Type _)
        = Nat.card ((H : Set G) * (K : Set G))
          * Nat.card ((H ⊓ K : Subgroup G) : Type _) := by
      calc (H.relIndex K * Nat.card (H : Type _)) * Nat.card ((H ⊓ K : Subgroup G) : Type _)
          = (H.relIndex K * Nat.card ((H ⊓ K : Subgroup G) : Type _))
              * Nat.card (H : Type _) := by ring
        _ = Nat.card (K : Type _) * Nat.card (H : Type _) := by rw [hRel]
        _ = Nat.card (H : Type _) * Nat.card (K : Type _) := by ring
        _ = Nat.card ((H : Set G) * (K : Set G))
              * Nat.card ((H ⊓ K : Subgroup G) : Type _) := x2.symm
    exact Nat.eq_of_mul_eq_mul_right hdpos e2
  -- `|G : H| · |H| = |G|`.
  have hN : H.index * Nat.card (H : Type _) = Nat.card G := by
    rw [mul_comm]; exact Subgroup.card_mul_index H
  -- Cancel `|H|` to reduce to a statement about cardinalities of the product.
  have iff1 : H.relIndex K = H.index ↔ Nat.card ((H : Set G) * (K : Set G)) = Nat.card G := by
    rw [← hP, ← hN]
    exact ⟨fun h => by rw [h], fun h => Nat.eq_of_mul_eq_mul_right hapos h⟩
  -- A finite subset of `G` equals `univ` iff it has cardinality `|G|`.
  have iff2 : (H : Set G) * (K : Set G) = Set.univ ↔
      Nat.card ((H : Set G) * (K : Set G)) = Nat.card G := by
    refine ⟨fun h => by rw [h]; exact Nat.card_congr (Equiv.Set.univ G), fun h => ?_⟩
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ Set.finite_univ
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq]
    exact h.ge
  exact iff1.trans iff2.symm

/-! ### X.22 — internal direct product criterion (prefix-intersection form) -/

/-- Modular disjointness for normal subgroups: if `A ⊓ C = 1` and `B ⊓ (A ⊔ C) = 1`
(with `C` normal), then `A ⊓ (B ⊔ C) = 1`. This is the instance of the modular law needed
for the hard direction of Theorem X.22; the subgroup lattice is not modular in general, but
`C.Normal` lets us write `B ⊔ C` as the set product `↑B * ↑C`. -/
theorem disjoint_sup_of_normal {A B C : Subgroup G} [C.Normal]
    (hAC : Disjoint A C) (hB : Disjoint B (A ⊔ C)) : Disjoint A (B ⊔ C) := by
  rw [Subgroup.disjoint_def] at hAC hB ⊢
  intro x hxA hxBC
  have hxBC' : x ∈ (B : Set G) * (C : Set G) := by
    rw [← Subgroup.mul_normal B C]; exact hxBC
  obtain ⟨b, hb, c, hc, rfl⟩ := hxBC'
  have hbAC : b ∈ A ⊔ C := by
    have hbeq : b = (b * c) * c⁻¹ := by group
    rw [hbeq]
    exact mul_mem (Subgroup.mem_sup_left hxA) (Subgroup.mem_sup_right (C.inv_mem hc))
  have hb1 : b = 1 := hB hb hbAC
  have hcA : c ∈ A := by
    have h' : b * c ∈ A := hxA
    rwa [hb1, one_mul] at h'
  change b * c = 1
  rw [hb1, one_mul]
  exact hAC hcA hc

section DirectProduct

variable {ι : Type*} [LinearOrder ι]

omit [LinearOrder ι] in
/-- A `Finset.sup` of normal subgroups is normal. -/
theorem finsetSup_normal (s : Finset ι) (M : ι → Subgroup G) (hnorm : ∀ i, (M i).Normal) :
    (s.sup M).Normal := by
  refine Finset.sup_induction ?_ (fun a ha b hb => ?_) (fun i _ => hnorm i)
  · infer_instance
  · haveI := ha; haveI := hb; infer_instance

/-- **Isaacs, Finite Group Theory, Theorem X.22** (hard direction, `Finset` form).
If, for every `k ∈ s`, the subgroup `M k` meets the join of the earlier members trivially, then
the family `(M i)_{i ∈ s}` of normal subgroups is independent (`Finset.SupIndep`). Proved by
strong induction on `s`, peeling off the largest element and using `disjoint_sup_of_normal`. -/
theorem supIndep_of_prefix (M : ι → Subgroup G) (hnorm : ∀ i, (M i).Normal) (s : Finset ι) :
    (∀ k ∈ s, Disjoint ((s.filter (· < k)).sup M) (M k)) → s.SupIndep M := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro hpre
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact Finset.supIndep_empty M
    · set t := s.max' hne with ht
      have htmem : t ∈ s := Finset.max'_mem s hne
      -- Restrict the prefix hypothesis to `s.erase t`.
      have hpre' : ∀ k ∈ s.erase t, Disjoint (((s.erase t).filter (· < k)).sup M) (M k) := by
        intro k hk
        have hfeq : (s.erase t).filter (· < k) = s.filter (· < k) := by
          rw [Finset.filter_erase]
          apply Finset.erase_eq_of_notMem
          rw [Finset.mem_filter]
          rintro ⟨_, hlt⟩
          have hks : k ∈ s := Finset.mem_of_mem_erase hk
          have hle : k ≤ t := Finset.le_max' s k hks
          have hne_kt : k ≠ t := Finset.ne_of_mem_erase hk
          exact absurd hlt (not_lt.mpr (le_of_lt (lt_of_le_of_ne hle hne_kt)))
        rw [hfeq]; exact hpre k (Finset.mem_of_mem_erase hk)
      have hs' : (s.erase t).SupIndep M := ih (s.erase t) (Finset.erase_ssubset htmem) hpre'
      -- `M t` is disjoint from the join of everything below it, i.e. from `(s.erase t).sup M`.
      have hdt : Disjoint (M t) ((s.erase t).sup M) := by
        have hd := hpre t htmem
        have hfilt : s.filter (· < t) = s.erase t := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨ha, hlt⟩; exact ⟨ne_of_lt hlt, ha⟩
          · rintro ⟨hane, ha⟩; exact ⟨ha, lt_of_le_of_ne (Finset.le_max' s a ha) hane⟩
        rw [hfilt] at hd; exact hd.symm
      -- Assemble via the insertion characterization of `SupIndep`.
      rw [← Finset.insert_erase htmem, Finset.supIndep_iff_disjoint_erase]
      intro i hi
      rcases eq_or_ne i t with rfl | hit
      · rw [Finset.erase_insert (Finset.notMem_erase t s)]; exact hdt
      · have hi' : i ∈ s.erase t := (Finset.mem_insert.mp hi).resolve_left hit
        rw [Finset.erase_insert_of_ne hit.symm, Finset.sup_insert]
        have hMiR : (s.erase t).sup M
            = M i ⊔ ((s.erase t).erase i).sup M := by
          conv_lhs => rw [← Finset.insert_erase hi']
          rw [Finset.sup_insert]
        have hBt : Disjoint (M t) (M i ⊔ ((s.erase t).erase i).sup M) := by
          rw [hMiR] at hdt; exact hdt
        have hAiR : Disjoint (M i) (((s.erase t).erase i).sup M) :=
          (Finset.supIndep_iff_disjoint_erase.mp hs') i hi'
        haveI : (((s.erase t).erase i).sup M).Normal := finsetSup_normal _ M hnorm
        exact disjoint_sup_of_normal hAiR hBt

/-- **Isaacs, Finite Group Theory, Theorem X.22** (internal direct-product criterion).
A finite family `M : ι → Subgroup G` of **normal** subgroups (indexed by a finite linearly
ordered type) is independent — i.e. an internal direct product, in mathlib's sense `iSupIndep` —
**if and only if** for every `k`, the member `M k` meets the join of the strictly earlier members
trivially: `Disjoint (⨆ j < k, M j) (M k)`.

This is the ordered prefix-intersection criterion of Isaacs' Theorem X.22: writing the join of
normal subgroups as the set product `M₁ ⋯ M_{k-1}`, the condition reads `(M₁ ⋯ M_{k-1}) ∩ M_k = 1`.
The forward direction is pure lattice theory; the converse uses `disjoint_sup_of_normal`. -/
theorem iSupIndep_iff_disjoint_biSup_lt [Finite ι] (M : ι → Subgroup G)
    (hnorm : ∀ i, (M i).Normal) :
    iSupIndep M ↔ ∀ k, Disjoint (⨆ j, ⨆ _ : j < k, M j) (M k) := by
  classical
  haveI := Fintype.ofFinite ι
  constructor
  · intro h k
    have hmono : (⨆ j, ⨆ _ : j < k, M j) ≤ ⨆ j, ⨆ _ : j ≠ k, M j :=
      iSup₂_le fun j hj => le_iSup₂ (f := fun j (_ : j ≠ k) => M j) j (ne_of_lt hj)
    exact Disjoint.mono_left hmono (h k).symm
  · intro hpre
    rw [iSupIndep_iff_supIndep_univ]
    refine supIndep_of_prefix M hnorm Finset.univ (fun k _ => ?_)
    have hbridge : (Finset.univ.filter (· < k)).sup M = ⨆ j, ⨆ _ : j < k, M j := by
      simp only [Finset.sup_eq_iSup, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hbridge]; exact hpre k

end DirectProduct

end OddOrder.Isaacs.Appendix
