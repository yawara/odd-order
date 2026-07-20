/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SolvablePrimeIndex
import OddOrder.GroupTheory.RepresentationTheory.CliffordConjugateDirectSum
import OddOrder.GroupTheory.RepresentationTheory.CliffordMultiplicityOne
import OddOrder.GroupTheory.RepresentationTheory.CliffordConjugateChar
import OddOrder.GroupTheory.RepresentationTheory.AbsolutelyIrreducible
import OddOrder.GroupTheory.RepresentationTheory.BaseChange
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Solvable
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Fong–Swan: `dim M ∣ |G|` for an absolutely irreducible solvable-group module (BG Lemma 2.3)

`OddOrder.GroupTheory.RepresentationTheory` shared module: the **capstone** of **Bender–Glauberman
Lemma 2.3** (a Fong–Swan-type statement, tracked in `issues/3008`).  For a *solvable* finite group
`G` and an absolutely irreducible finite-dimensional `FG`-module `V`, the `F`-dimension of `V`
divides `|G|`.

The proof is the elementary Clifford-theoretic induction of Bender–Glauberman (LMS LNS 188,
Lemma 2.3), **not** the modular Fong–Swan theorem via Brauer lifting:

* First reduce to an algebraically closed field by base change (`finrank`, `|G|` are unchanged).
* Then induct on `|G|`.  If `G` is trivial, irreducibility over the algebraically closed `k`
  forces `dim V = 1`.  Otherwise pick a normal subgroup `H ⊴ G` of *prime* index `p = [G:H]` with
  `G = ⟨H, x⟩` (`x ∉ H`), and a nonzero simple `k[H]`-submodule `W` of the restriction.  By
  induction `dim W ∣ |H|`, and:
    * **case (i)** `W ≅ W^x` — the whole conjugacy stabiliser is `G`, so the restriction is simple
      (`restriction_isSimpleModule`), whence `W = V_H` and `dim V = dim W ∣ |H| ∣ |G|`;
    * **case (ii)** `W ≇ W^x` — the restriction is the direct sum of the `p` conjugates of `W`
      (`finrank_eq_index_mul_finrank_of_not_linearEquiv_conj`), so
      `dim V = p · dim W ∣ p · |H| = |G|`.

## Main statements

* `finrank_dvd_card_of_isAlgClosed_of_irreducible` — the algebraically-closed core.
* `finrank_dvd_card_of_isAbsolutelyIrreducible` — **BG Lemma 2.3** itself, general field.

## References

* Bender, Glauberman, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994), Lemma 2.3.
-/

namespace OddOrder.RepresentationTheory

open Representation
open scoped MonoidAlgebra
open Module (finrank)

/-! ## A public prime-index normal subgroup lemma

**⚠ Duplication flag.** This re-proves (as a *public* declaration) the *private*
`OddOrder.BG.Ch2.S07.exists_normal_index_prime_of_solvable`
(`OddOrder/BG/Ch2_Uniqueness/S07_Hypothesis75.lean:50`).  A private lemma cannot be imported, so
the ~30-line proof is copied here.  The two should be unified into a single shared public leaf
(e.g. in `OddOrder/GroupTheory`) once the BG side is refactored. -/


/-! ## The algebraically-closed core -/

/-- **Strong-induction engine for the algebraically-closed core of BG Lemma 2.3.**  Universe-safe
version bounding `Nat.card G` by `n`; `finrank_dvd_card_of_isAlgClosed_of_irreducible` follows with
`n = Nat.card G`.  The subgroup `↥H` and the constituent's carrier stay in the same universes, so
the induction hypothesis (at a strictly smaller group) applies. -/
private theorem finrank_dvd_card_aux {k : Type*} [Field k] [IsAlgClosed k] (n : ℕ) :
    ∀ {G : Type*} [Group G] [Finite G] [IsSolvable G]
      {V : Type*} [AddCommGroup V] [Module k V]
      (ρ : Representation k G V) [ρ.IsIrreducible] [FiniteDimensional k V],
      Nat.card G ≤ n → Module.finrank k V ∣ Nat.card G := by
  induction n with
  | zero =>
      intro G _ _ _ V _ _ ρ _ _ hcard
      haveI : Nonempty G := ⟨1⟩
      have : 0 < Nat.card G := Nat.card_pos
      omega
  | succ n ih =>
      intro G _ _ _ V _ _ ρ _ _ hcard
      by_cases hntG : Nontrivial G
      · -- `G` nontrivial: reduce to a prime-index normal subgroup `H`.
        obtain ⟨H, hHnorm, hHprime⟩ :=
          GroupTheory.exists_normal_index_prime_of_solvable (Q := G) hntG
        haveI := hHnorm
        -- `|H| · [G:H] = |G|`, `[G:H]` prime, so `|H| < |G| ≤ n+1`, giving `|H| ≤ n`.
        have hcardH : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
        haveI : Nonempty G := ⟨1⟩
        haveI : Nonempty ↥H := ⟨1⟩
        have hHpos : 0 < Nat.card ↥H := Nat.card_pos
        have hGpos : 0 < Nat.card G := Nat.card_pos
        have hHdvdG : Nat.card ↥H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
        have hle : Nat.card ↥H ≤ Nat.card G := Nat.le_of_dvd hGpos hHdvdG
        have hHne : Nat.card ↥H ≠ Nat.card G := by
          intro heq
          rw [← hcardH] at heq
          have h1 : Nat.card ↥H * 1 = Nat.card ↥H * H.index := by rw [mul_one]; exact heq
          have hidx1 : (1 : ℕ) = H.index := Nat.eq_of_mul_eq_mul_left hHpos h1
          rw [← hidx1] at hHprime; exact Nat.not_prime_one hHprime
        have hlt : Nat.card ↥H < Nat.card G := lt_of_le_of_ne hle hHne
        have hHn : Nat.card ↥H ≤ n := by omega
        -- Pick `x ∉ H`; then `G = ⟨H, x⟩` because `[G:H]` is prime.
        have hHtop : H ≠ ⊤ := by
          intro h; rw [h, Subgroup.index_top] at hHprime; exact Nat.not_prime_one hHprime
        obtain ⟨x, -, hxH⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hHtop)
        have hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤ := by
          have hHleK : H ≤ Subgroup.closure ((H : Set G) ∪ {x}) := by
            intro h hh; exact Subgroup.subset_closure (Set.mem_union_left _ hh)
          have hxK : x ∈ Subgroup.closure ((H : Set G) ∪ {x}) :=
            Subgroup.subset_closure (Set.mem_union_right _ rfl)
          have hmul := Subgroup.relIndex_mul_index hHleK
          have hdvd : (Subgroup.closure ((H : Set G) ∪ {x})).index ∣ H.index :=
            ⟨H.relIndex _, by rw [Nat.mul_comm]; exact hmul.symm⟩
          rcases hHprime.eq_one_or_self_of_dvd _ hdvd with h1 | hpp
          · exact Subgroup.index_eq_one.mp h1
          · exfalso
            have hrel1 : H.relIndex (Subgroup.closure ((H : Set G) ∪ {x})) = 1 := by
              rw [hpp] at hmul
              exact Nat.eq_of_mul_eq_mul_right hHprime.pos (by rw [one_mul]; exact hmul)
            exact hxH (Subgroup.relIndex_eq_one.mp hrel1 hxK)
        -- The restriction is semisimple; extract a nonzero simple constituent `W`.
        haveI : Nontrivial V := nontrivial_of_isIrreducible ρ
        haveI : Module.Finite k V := inferInstance
        haveI : Module.Finite k (resRep ρ H).asModule := inferInstance
        haveI : IsSemisimpleModule k[↥H] (resRep ρ H).asModule :=
          isSemisimpleModule_resRep_of_isIrreducible ρ
        haveI : Nontrivial (resRep ρ H).asModule := ‹Nontrivial V›
        obtain ⟨W, hWs⟩ := IsSemisimpleModule.exists_simple_submodule k[↥H] (resRep ρ H).asModule
        haveI := hWs
        have hWne : W ≠ ⊥ := by
          rintro rfl
          haveI : Nontrivial ↥(⊥ : Submodule k[↥H] (resRep ρ H).asModule) :=
            IsSimpleModule.nontrivial k[↥H] _
          exact false_of_nontrivial_of_subsingleton ↥(⊥ : Submodule k[↥H] (resRep ρ H).asModule)
        -- Induction: `dim W ∣ |H|` (via the constituent as an `↥H`-representation).
        haveI hσirr := subRep_isIrreducible (resRep ρ H) W
        have hih : Module.finrank k (Subrepresentation.ofSubmodule' W).toRepresentation.asModule
            ∣ Nat.card ↥H :=
          @ih _ _ _ _ _ _ _ (Subrepresentation.ofSubmodule' W).toRepresentation hσirr _ hHn
        have hWdvdH : Module.finrank k ↥W ∣ Nat.card ↥H := by
          rw [((subRepAsModuleEquiv (resRep ρ H) W).restrictScalars k).finrank_eq]; exact hih
        -- Dichotomy on whether `x` stabilises the isomorphism class of `W`.
        by_cases hxstab : x ∈ conjStab ρ W
        · -- case (i): every conjugate `≅ W`, so `V_H` is simple, `W = V_H`.
          have hStabTop : conjStab ρ W = ⊤ := by
            rw [eq_top_iff, ← hgen, Subgroup.closure_le]
            rintro s (hs | hs)
            · exact le_conjStab ρ W hs
            · rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hxstab
          have hconj : ∀ g : G,
              Nonempty (↥W ≃ₗ[k[↥H]] ↥(W.map (conjSemilinearEnd (H := H) ρ g))) := fun g =>
            (mem_conjStab_iff ρ W g).mp (by rw [hStabTop]; exact Subgroup.mem_top g)
          haveI : IsSimpleModule k[↥H] (resRep ρ H).asModule :=
            restriction_isSimpleModule ρ x hgen W hWne hconj
          have hWtop : W = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W).resolve_left hWne
          have e0 : ↥W ≃ₗ[k[↥H]] (resRep ρ H).asModule :=
            (LinearEquiv.ofEq W ⊤ hWtop).trans Submodule.topEquiv
          have hfrWV : Module.finrank k ↥W = Module.finrank k V :=
            ((e0.restrictScalars k).trans (resRep ρ H).asModuleEquiv).finrank_eq
          rw [← hfrWV]; exact hWdvdH.trans hHdvdG
        · -- case (ii): `W ≇ W^x`, so `dim V = [G:H] · dim W`.
          have hnotconj : ¬ Nonempty
              (↥W ≃ₗ[k[↥H]] ↥(W.map (conjSemilinearEnd (H := H) ρ x))) := fun h =>
            hxstab ((mem_conjStab_iff ρ W x).mpr h)
          have hfrV : Module.finrank k V = H.index * Module.finrank k ↥W :=
            finrank_eq_index_mul_finrank_of_not_linearEquiv_conj ρ x hgen hHprime W hWne hnotconj
          rw [hfrV]
          have hstep : H.index * Module.finrank k ↥W ∣ H.index * Nat.card ↥H :=
            mul_dvd_mul_left H.index hWdvdH
          rwa [show H.index * Nat.card ↥H = Nat.card G by rw [mul_comm]; exact hcardH] at hstep
      · -- `G` trivial: irreducibility over an algebraically closed field forces `dim V = 1`.
        haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hntG
        haveI : Nontrivial V := nontrivial_of_isIrreducible ρ
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        let Wρ : Subrepresentation ρ :=
          { toSubmodule := Submodule.span k {v}
            apply_mem_toSubmodule := fun g w hw => by
              have hgv : (ρ g) w = w := by
                rw [Subsingleton.elim g (1 : G), map_one, Module.End.one_apply]
              rw [hgv]; exact hw }
        have hne : Wρ ≠ ⊥ := by
          intro h
          have hsp : Submodule.span k {v} = ⊥ := congrArg Subrepresentation.toSubmodule h
          rw [Submodule.span_singleton_eq_bot] at hsp
          exact hv hsp
        have htop : Wρ = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top Wρ).resolve_left hne
        have hspan : Submodule.span k {v} = ⊤ := congrArg Subrepresentation.toSubmodule htop
        have hfr1 : Module.finrank k V = 1 := by
          have e : (Submodule.span k {v}) ≃ₗ[k] V :=
            (LinearEquiv.ofEq _ _ hspan).trans Submodule.topEquiv
          rw [← e.finrank_eq, finrank_span_singleton hv]
        rw [hfr1]; exact one_dvd _

/-- **BG Lemma 2.3, algebraically-closed core.**  For a finite *solvable* group `G`, an
algebraically closed field `k`, and an irreducible finite-dimensional representation `ρ` of `G`
over `k`, the dimension of `V` divides `|G|`.

Proved by strong induction on `|G|` via `finrank_dvd_card_aux`. -/
theorem finrank_dvd_card_of_isAlgClosed_of_irreducible
    {k : Type*} [Field k] [IsAlgClosed k] {G : Type*} [Group G] [Finite G] [IsSolvable G]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] [FiniteDimensional k V] :
    Module.finrank k V ∣ Nat.card G :=
  finrank_dvd_card_aux (Nat.card G) ρ le_rfl

/-! ## BG Lemma 2.3 over a general field -/

/-- **Bender–Glauberman Lemma 2.3** (Fong–Swan, general field).  For a finite *solvable* group `G`
and an **absolutely irreducible** finite-dimensional `FG`-module `V`, the `F`-dimension of `V`
divides `|G|`.

Proof: base change to the algebraic closure `K = AlgebraicClosure F`.  The base change stays
irreducible (`IsAbsolutelyIrreducible.baseChangeRepresentation_isIrreducible`), so the
algebraically-closed core applies to `K ⊗[F] V`; and `finrank K (K ⊗[F] V) = finrank F V`
(`Module.finrank_baseChange`). -/
theorem finrank_dvd_card_of_isAbsolutelyIrreducible
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G] [IsSolvable G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) [ρ.IsIrreducible] [FiniteDimensional F V]
    (habs : IsAbsolutelyIrreducible ρ) :
    Module.finrank F V ∣ Nat.card G := by
  haveI : (baseChangeRepresentation (AlgebraicClosure F) ρ).IsIrreducible :=
    habs.baseChangeRepresentation_isIrreducible (AlgebraicClosure F)
  have hdvd := finrank_dvd_card_of_isAlgClosed_of_irreducible
    (baseChangeRepresentation (AlgebraicClosure F) ρ)
  rwa [Module.finrank_baseChange] at hdvd

end OddOrder.RepresentationTheory
