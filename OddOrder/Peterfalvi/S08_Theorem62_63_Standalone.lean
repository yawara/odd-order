/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S08_CoherenceCorePart1

/-!
# Peterfalvi (6.2)/(6.3): the *standalone* general (6.1) coherence theorems

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §6, (6.1)–(6.3).

The repo already proves Peterfalvi's coherence theorems (6.2)/(6.3) — but only over the Sibley–Dade
capstone setup `SibleyDadeHypothesis G L H`, where the induced-character kernel `K` *equals* the
nilpotent Frobenius complement `H` (`OddOrder.Peterfalvi.S08.six_two` / `six_three` in
`S08_CoherenceCorePart2`).  The §11/§13 maximal-subgroup analysis (Peterfalvi §11, repo
`S13_MaximalIII_IV`) needs them in their **general Hypothesis (6.1) form**, where the
induced-family kernel `K = M'` (the derived subgroup, *solvable*) is strictly larger than the
nilpotent middle group `H = HC`.  Concretely (6.3) is applied there with
`(L, K, M, H, H₁) = (M, M', 1, HC, H₀C)` and (6.2) with `(A, B, C, D) = (H₁, H₀C, HC, HC)`, so
`K ≠ H`; the Sibley `six_two`/`six_three` (with `K = H` and `H` nilpotent + Frobenius) do not apply.

This leaf supplies the **assembly that separates `K` (solvable) from `H` (nilpotent)**.  The deep
character-theoretic core of (6.2) — Peterfalvi's (5.6) quantitative coherence bound for the
(possibly *reducible*) induced members `Ind_K^L θ` of a general solvable `K` — is the one genuinely
missing ingredient; in the Sibley case `hF : IsFrobeniusGroup L H W₁` makes every member
irreducible and discharges it (`sMember_index_le_two_psi`).  Here that core is exposed as the
explicit **(6.2) index oracle** hypothesis `h62`, and everything *else* in (6.3) — the minimal-`A`
descent, the maximal-`B` step, nilpotency forcing centrality, and the `√`-arithmetic — is proved
in full,
reusing the general lattice/arithmetic lemmas of `S08_CoherenceCorePart1`.

## Contents

* `OddOrder.Peterfalvi.S07.IsCoherent.subset` — **coherence is inherited by subsets** (with a
  nonzero supported witness).  A general, reusable monotonicity lemma for the (5.1) coherence
  predicate, missing until now.
* `six_three_descent` — **Peterfalvi (6.3), general (6.1) form** (`K` solvable normal, `H ≤ K`
  nilpotent, `K ≠ H` allowed), reduced to the (6.2) index oracle `h62`.  This is the producer the
  §11/§13 consumer `S13.coherent_S_of_coherent_SH0C` cites.

The (6.2) oracle `h62` packages the Sibley-side chain `six_two_central → six_three_HH1_le`
(`S08_CoherenceCorePart2`/`S08_CoherenceCorePart1`) in its general form; its character-theoretic
discharge for reducible induced members of a solvable `K` is the remaining §6 work (entangled with
the §10–§12 `muGrid` machinery).  See `notes/peterfalvi/s06_standalone_62_63_producer.md`.
-/

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]
variable [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

namespace IsCoherent

variable {τ : IntegralCharacterMap L G} {S S' : Set (ClassFunction L ℂ)} {A : Set L}

/-- **Coherence is inherited by subsets.**  If `(S, A, τ)` is coherent and `S' ⊆ S` still admits a
nonzero `A`-supported element of `ℤ[S']`, then `(S', A, τ)` is coherent.

The *same* coherent extension works: `ℤ[S'] ≤ ℤ[S]` (`Submodule.span_mono`) so the lattice isometry
(`extension_inner_eq`) and the `ℤ[Irr G]`-codomain condition (`extension_mem_ZIrr`) restrict, and
`zSupportedSpan S' A ⊆ zSupportedSpan S A` (`zSupportedSpan_mono_left`) so agreement with `τ` on the
supported lattice (`extends_on_supported`) restricts.  Only the nondegeneracy witness `nonzero` has
to be re-supplied — it is genuinely set-dependent — hence the `hne` hypothesis.

This is the general monotonicity of Peterfalvi's (5.1) coherence predicate.  In the (6.2) coherence
dichotomy a smaller coherent set's witness `φ ∈ zSupportedSpan S(A) A` transports up by
`zSupportedSpan_mono_left`, so `hne` is always available when `S' ⊇` a known coherent set. -/
noncomputable def subset (hτ : IsCoherent τ S A) (hsub : S' ⊆ S)
    (hne : ∃ φ : ClassFunction L ℂ, φ ∈ zSupportedSpan (L := L) S' A ∧ φ ≠ 0) :
    IsCoherent τ S' A where
  nonzero := hne
  extension := hτ.extension
  extension_inner_eq := fun φ ψ hφ hψ =>
    hτ.extension_inner_eq φ ψ (Submodule.span_mono hsub hφ) (Submodule.span_mono hsub hψ)
  extends_on_supported := fun φ hφ =>
    hτ.extends_on_supported φ (zSupportedSpan_mono_left hsub hφ)
  extension_mem_ZIrr := fun φ hφ =>
    hτ.extension_mem_ZIrr φ (Submodule.span_mono hsub hφ)

end IsCoherent

end OddOrder.Peterfalvi.S07

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

/-- **Peterfalvi (6.3), general Hypothesis (6.1) form** (the minimal-`A` descent).

Let `K` be a solvable normal subgroup of `L` (the induced-family kernel `S = {Ind_K^L θ}`), and let
`M ≤ H₁ < H ≤ K` be normal subgroups with `H` nilpotent (Peterfalvi states `H/M` nilpotent; the
§11 consumer has `M = 1`, `H = HC` nilpotent).  Writing `S(·)` for the coherence functor `SOf`, if
`S(H₁)` is coherent and `|H : H₁| > 4|L:K|² + 1`, then `S(M)` is coherent.

The character-theoretic content — Peterfalvi (6.2) in index form, `|H:H₁| ≤ 4|L:K|² + 1` whenever a
proper section `B ⊆ A ⊆ H₁` has `A/B` central in `H/B`, `S(A)` coherent and `S(B)` not — is the
explicit **oracle** `h62`.  (In the Sibley case `h62` is `six_three_index_bound`; for a general
solvable `K` it bottoms out in the (5.6) bound for reducible induced members.)  Everything else is
proved here, mirroring `S08.six_three` but with `K` and `H` separated:

* the minimal coherent `A ∈ [M, H₁]` (`Set.Finite.exists_minimalFor`);
* the maximal proper normal `B` below it (`exists_maximal_normal_between`);
* `S(B)` not coherent (minimality of `A`);
* `A/B ⊆ Z(H/B)` (`normal_central_of_maximal_normal_below`, `H` nilpotent);
* `[K/A, K/A] ≠ ⊤` from `K` solvable and `A < K` (the degree-`|L:K|` anchor input of (6.2)).

This is the producer cited by `S13.coherent_S_of_coherent_SH0C` (Peterfalvi (11.3), `(6.3)` applied
with `(L,K,M,H,H₁) = (M, M', 1, HC, H₀C)`). -/
theorem six_three_descent
    {K H M H₁ : Subgroup ↥L} [Group.IsNilpotent ↥H] [IsSolvable ↥K]
    [M.Normal] [H₁.Normal] (hHnorm : H.Normal)
    (hMH₁ : M ≤ H₁) (hH₁H : H₁ < H) (hHK : H ≤ K)
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G) (A0 : Set ↥L)
    (SOf : Subgroup ↥L → Set (ClassFunction ↥L ℂ))
    (h62 : ∀ (A B : Subgroup ↥L) [A.Normal] [B.Normal], B ≤ A → A ≤ H₁ →
        _root_.commutator (↥K ⧸ A.subgroupOf K) ≠ ⊤ →
        (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≤
          Subgroup.center (↥H ⧸ B.subgroupOf H) →
        Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf A) A0) →
        ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf B) A0) →
        Nat.card (↥H ⧸ H₁.subgroupOf H) ≤ 4 * K.index ^ 2 + 1)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf H₁) A0))
    (hbound : 4 * K.index ^ 2 + 1 < Nat.card (↥H ⧸ H₁.subgroupOf H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf M) A0) := by
  classical
  haveI : Finite (Subgroup ↥L) := Finite.of_injective (fun K : Subgroup ↥L => (K : Set ↥L))
    (fun _ _ h => SetLike.coe_injective h)
  set s : Set (Subgroup ↥L) := {A | A.Normal ∧ M ≤ A ∧ A ≤ H₁ ∧
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf A) A0)} with hs_def
  have hH₁s : H₁ ∈ s := by
    simp only [hs_def, Set.mem_setOf_eq]; exact ⟨‹H₁.Normal›, hMH₁, le_refl _, hcoh⟩
  obtain ⟨A, hAmem, hAmin⟩ :=
    Set.Finite.exists_minimalFor (id : Subgroup ↥L → Subgroup ↥L) s (Set.toFinite _) ⟨H₁, hH₁s⟩
  simp only [hs_def, Set.mem_setOf_eq] at hAmem
  obtain ⟨hAnorm, hMA, hAH₁, hAcoh⟩ := hAmem
  haveI : A.Normal := hAnorm
  have hAeqM : A = M := by
    by_contra hne
    have hMltA : M < A := lt_of_le_of_ne hMA (Ne.symm hne)
    obtain ⟨B, hBnorm, hMB, hBltA, hBmaxl⟩ := exists_maximal_normal_between hMltA
    haveI : B.Normal := hBnorm
    have hAltH : A < H := lt_of_le_of_lt hAH₁ hH₁H
    have hAltK : A < K := lt_of_lt_of_le hAltH hHK
    -- `[K/A, K/A] ≠ ⊤`: `K` solvable, `K/A` nontrivial (`A < K`).
    have hAcomm : _root_.commutator (↥K ⧸ A.subgroupOf K) ≠ ⊤ := by
      haveI : (A.subgroupOf K).Normal := (‹A.Normal›).subgroupOf K
      haveI : Nontrivial (↥K ⧸ A.subgroupOf K) := by
        rw [QuotientGroup.nontrivial_iff]
        intro htop
        exact hAltK.ne' (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hAltK.le)
      exact (IsSolvable.commutator_lt_top_of_nontrivial (↥K ⧸ A.subgroupOf K)).ne
    -- `A/B ⊆ Z(H/B)`: `H` nilpotent, `B` maximal below `A`.
    have hcentral := normal_central_of_maximal_normal_below (H := H) (A := A) (B := B)
      hHnorm hAltH.le hBltA hBmaxl
    -- `S(B)` not coherent: else `B` beats the minimality of `A`.
    have hSBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf B) A0) := by
      intro hBcoh
      have hBs : B ∈ s := by
        simp only [hs_def, Set.mem_setOf_eq]
        exact ⟨hBnorm, hMB, hBltA.le.trans hAH₁, hBcoh⟩
      exact lt_irrefl _ (hBltA.trans_le (hAmin hBs hBltA.le))
    have hbnd := h62 A B hBltA.le hAH₁ hAcomm hcentral hAcoh hSBncoh
    omega
  rw [← hAeqM]; exact hAcoh

end OddOrder.Peterfalvi.S08
