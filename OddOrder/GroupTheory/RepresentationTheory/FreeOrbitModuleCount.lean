/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.WielandtCounting
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Free-orbit module count (Peterfalvi (9.1), the kernel-FPF dimension fact (†))

The single-orbit count `WielandtCounting.finrank_eq_card_mul_finrank_invariants` handles the case
where `ρ` permutes the summands of `V = ⊕ A i` in **one** regular `G`-orbit.  For the kernel-FPF
fact (†) the Frobenius complement `E` permutes the nontrivial `U`-isotypic components of `W` in
**several** orbits, all of which are *free* (Frobenius: no nonidentity complement element fixes a
nontrivial irreducible).  This file lifts the count to that situation:

`finrank_eq_card_mul_finrank_invariants_of_free` — if `V = ⊕_{i:ι} A i` (internal), `G` acts
**freely** on the finite index set `ι` permuting the summands (`(A i).map (ρ a) = A (a • i)`), and
`|G|` is invertible, then `dim V = |G| · dim Vᴳ`.

The proof groups `ι` into `G`-orbits (each of size `|G|`, by freeness) and shows both `dim V` and
`|G|·dim Vᴳ` equal `|G| · ∑_{ω} dim (A ω.out)`.
-/

namespace OddOrder.GroupTheory.WielandtCounting

open Module Representation MulAction

variable {k : Type*} [Field k] {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MulAction G ι]

omit [Field k] [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι] in
/-- **Free action: each orbit has size `|G|`.**  A free finite action has trivial stabilisers, so
the orbit–stabiliser theorem gives `|orbit i| = |G|`. -/
theorem card_orbit_eq_card_of_free
    (hfree : ∀ (a : G) (i : ι), a • i = i → a = 1) (i : ι) :
    Nat.card (orbit G i) = Nat.card G := by
  have hstab : stabilizer G i = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    exact Subgroup.mem_bot.mpr (hfree a i (mem_stabilizer_iff.mp ha))
  calc Nat.card (orbit G i)
      = Nat.card (G ⧸ stabilizer G i) := Nat.card_congr (orbitEquivQuotientStabilizer G i)
    _ = Nat.card (G ⧸ (⊥ : Subgroup G)) := by rw [hstab]
    _ = Nat.card G := Nat.card_congr QuotientGroup.quotientBot.toEquiv

omit [Fintype ι] [DecidableEq ι] in
/-- All summands in a single `G`-orbit have the same dimension (`ρ a` carries `A i` isomorphically
onto `A (a • i)`). -/
theorem finrank_A_eq_of_mem_orbit (ρ : Representation k G V) {A : ι → Submodule k V}
    (hperm : ∀ (a : G) (i : ι), (A i).map (ρ a) = A (a • i)) {i j : ι}
    (h : j ∈ orbit G i) : finrank k ↥(A j) = finrank k ↥(A i) := by
  obtain ⟨a, rfl⟩ := h
  rw [← hperm a i, finrank_map_rho_eq]

set_option linter.unusedFintypeInType false in
/-- **Dimension half (free multi-orbit).**  `dim V = |G| · ∑_{orbits ω} dim (A ω.out)`: the
summands group into `G`-orbits, each of size `|G|` (free) with all members of equal dimension. -/
theorem finrank_eq_card_mul_sum_out (ρ : Representation k G V) [Fintype G] [FiniteDimensional k V]
    [Fintype (orbitRel.Quotient G ι)]
    {A : ι → Submodule k V} (hint : DirectSum.IsInternal A)
    (hperm : ∀ (a : G) (i : ι), (A i).map (ρ a) = A (a • i))
    (hfree : ∀ (a : G) (i : ι), a • i = i → a = 1) :
    finrank k V
      = Fintype.card G * ∑ ω : orbitRel.Quotient G ι, finrank k ↥(A ω.out) := by
  classical
  haveI : ∀ ω : orbitRel.Quotient G ι, Fintype (orbit G ω.out) := fun _ => Fintype.ofFinite _
  have h1 : finrank k V = ∑ i : ι, finrank k ↥(A i) := by
    rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hint).finrank_eq, finrank_directSum]
  -- group the summands by `G`-orbit (`selfEquivSigmaOrbits`).
  have h2 : (∑ ω : orbitRel.Quotient G ι, ∑ x : orbit G ω.out, finrank k ↥(A (x : ι)))
      = ∑ i : ι, finrank k ↥(A i) := by
    rw [Finset.sum_sigma', Finset.univ_sigma_univ]
    exact (Fintype.sum_equiv (selfEquivSigmaOrbits G ι)
      (fun i => finrank k ↥(A i)) (fun p => finrank k ↥(A (p.2 : ι))) (fun _ => rfl)).symm
  -- each orbit contributes `|G| · dim (A ω.out)` (free ⟹ size `|G|`, equal dims).
  have h3 : ∀ ω : orbitRel.Quotient G ι,
      ∑ x : orbit G ω.out, finrank k ↥(A (x : ι)) = Fintype.card G * finrank k ↥(A ω.out) := by
    intro ω
    have hcard : Fintype.card (orbit G ω.out) = Fintype.card G := by
      rw [← Nat.card_eq_fintype_card (α := orbit G ω.out), ← Nat.card_eq_fintype_card (α := G)]
      exact card_orbit_eq_card_of_free hfree ω.out
    rw [Finset.sum_congr rfl (fun x _ => finrank_A_eq_of_mem_orbit ρ hperm x.2),
      Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]
  rw [h1, ← h2, Finset.sum_congr rfl (fun ω _ => h3 ω), ← Finset.mul_sum]

end OddOrder.GroupTheory.WielandtCounting
