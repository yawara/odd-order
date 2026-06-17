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

omit [Field k] [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι] in
/-- Distinct orbit representatives lie in distinct orbits: `g • ω'.out = ω.out → ω = ω'`. -/
theorem orbit_out_eq (g : G) {ω ω' : orbitRel.Quotient G ι} (h : g • ω'.out = ω.out) : ω = ω' := by
  have hmem : ω.out ∈ orbit G ω'.out := ⟨g, h⟩
  have : (Quotient.mk'' ω.out : orbitRel.Quotient G ι) = Quotient.mk'' ω'.out :=
    Quotient.sound' hmem
  rwa [Quotient.out_eq', Quotient.out_eq'] at this

set_option linter.unusedFintypeInType false in
/-- **Invariants half (free multi-orbit).**  `dim Vᴳ = ∑_{orbits ω} dim (A ω.out)`: an invariant is
*freely* determined by its components at the orbit representatives.  Both inequalities use the
rep-component map `v ↦ (e.symm v ω.out)` into `Π ω, A ω.out`, with the averaging section. -/
theorem finrank_invariants_eq_sum_out (ρ : Representation k G V) [Fintype G]
    [Invertible (Fintype.card G : k)] [FiniteDimensional k V]
    [Fintype (orbitRel.Quotient G ι)]
    {A : ι → Submodule k V} (hint : DirectSum.IsInternal A)
    (hperm : ∀ (a : G) (i : ι), (A i).map (ρ a) = A (a • i))
    (hfree : ∀ (a : G) (i : ι), a • i = i → a = 1) :
    finrank k ↥(invariants ρ) = ∑ ω : orbitRel.Quotient G ι, finrank k ↥(A ω.out) := by
  classical
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hint with he
  have hmem : ∀ (g : G) (h : ι) (x : V), x ∈ A h → ρ g x ∈ A (g • h) := fun g h x hx =>
    hperm g h ▸ Submodule.mem_map_of_mem hx
  have hcs : ∀ (j : ι) (x : V) (hx : x ∈ A j), e.symm x j = ⟨x, hx⟩ := fun j x hx => by
    rw [he]; exact hint.ofBijective_coeLinearMap_of_mem hx
  have hcn : ∀ (i j : ι) (x : V), x ∈ A i → i ≠ j → e.symm x j = 0 := fun i j x hx hij => by
    rw [he]; exact hint.ofBijective_coeLinearMap_of_mem_ne hij hx
  have hdecomp : ∀ v : V, ∑ i : ι, ((e.symm v i : ↥(A i)) : V) = v := fun v => by
    have key : ∑ i : ι, ((e.symm v i : ↥(A i)) : V) = DirectSum.coeLinearMap A (e.symm v) := by
      conv_rhs => rw [← DirectSum.sum_univ_of (e.symm v), map_sum]
      exact Finset.sum_congr rfl (fun i _ => (DirectSum.coeLinearMap_of A i _).symm)
    rw [key]; exact e.apply_symm_apply v
  have hpi : finrank k (∀ ω : orbitRel.Quotient G ι, ↥(A ω.out))
      = ∑ ω : orbitRel.Quotient G ι, finrank k ↥(A ω.out) := Module.finrank_pi_fintype k
  rw [← hpi]
  refine le_antisymm ?_ ?_
  · -- `dim Vᴳ ≤ dim (Π ω, A ω.out)`: the rep-component map `v ↦ (e.symm v ω.out)` is injective.
    let π : ↥(invariants ρ) →ₗ[k] (∀ ω : orbitRel.Quotient G ι, ↥(A ω.out)) :=
      { toFun := fun v ω => e.symm (v : V) ω.out
        map_add' := fun x y => by funext ω; simp [map_add, DirectSum.add_apply]
        map_smul' := fun c x => by funext ω; simp [map_smul, DirectSum.smul_apply] }
    refine LinearMap.finrank_le_finrank_of_injective (f := π) (fun x y hxy => ?_)
    -- an invariant's component at `g • r` is `ρ g` of its component at `r`.
    have hrel : ∀ v ∈ invariants ρ, ∀ (g : G) (r : ι),
        (e.symm v (g • r) : V) = ρ g ((e.symm v r : ↥(A r)) : V) := by
      intro v hv g r
      have hexp : ρ g v = ∑ h : ι, ρ g ((e.symm v h : ↥(A h)) : V) := by
        conv_lhs => rw [← hdecomp v]
        rw [map_sum]
      have key : (e.symm (ρ g v) (g • r) : V) = ρ g ((e.symm v r : ↥(A r)) : V) := by
        rw [hexp, map_sum, DirectSum.sum_apply, Finset.sum_eq_single r]
        · have hm : ρ g ((e.symm v r : ↥(A r)) : V) ∈ A (g • r) := by
            simpa using hmem g r _ (e.symm v r).2
          rw [hcs (g • r) _ hm]
        · intro h _ hhr
          have hm : ρ g ((e.symm v h : ↥(A h)) : V) ∈ A (g • h) := hmem g h _ (e.symm v h).2
          exact hcn (g • h) (g • r) _ hm (fun hc => hhr (MulAction.injective g hc))
        · intro h; exact absurd (Finset.mem_univ r) h
      rwa [hv g] at key
    -- the rep components of `x - y` all vanish (from `π x = π y`).
    have hrepzero : ∀ ω : orbitRel.Quotient G ι,
        e.symm ((x : V) - y) ω.out = (0 : ↥(A ω.out)) := fun ω => by
      have h : e.symm (x : V) ω.out = e.symm (y : V) ω.out := congrFun hxy ω
      rw [map_sub, DirectSum.sub_apply, h, sub_self]
    -- hence every component of `x - y` vanishes (free: `i = g • ⟦i⟧.out`), so `x = y`.
    have hsub : (x : V) - y = 0 := by
      rw [← hdecomp ((x : V) - y)]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hxyinv : (x : V) - y ∈ invariants ρ := (invariants ρ).sub_mem x.2 y.2
      obtain ⟨g, hg⟩ : ∃ g : G, g • (Quotient.mk'' i : orbitRel.Quotient G ι).out = i := by
        have hmem : i ∈ orbitRel.Quotient.orbit (Quotient.mk'' i : orbitRel.Quotient G ι) :=
          orbitRel.Quotient.mem_orbit.mpr rfl
        rw [orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'] at hmem
        exact hmem
      have hkey := hrel _ hxyinv g (Quotient.mk'' i : orbitRel.Quotient G ι).out
      rw [hg, hrepzero (Quotient.mk'' i)] at hkey
      simp only [ZeroMemClass.coe_zero, map_zero] at hkey
      exact hkey
    exact Subtype.ext (sub_eq_zero.mp hsub)
  · -- `dim (Π ω, A ω.out) ≤ dim Vᴳ`: the averaging section is injective.
    set L : (∀ ω : orbitRel.Quotient G ι, ↥(A ω.out)) →ₗ[k] V :=
      ∑ ω : orbitRel.Quotient G ι, (averageMap ρ) ∘ₗ (A ω.out).subtype ∘ₗ LinearMap.proj ω with hL
    have hLval : ∀ a, L a = ∑ ω, averageMap ρ ((a ω : ↥(A ω.out)) : V) := fun a => by
      rw [hL, LinearMap.sum_apply]; rfl
    let ψ : (∀ ω : orbitRel.Quotient G ι, ↥(A ω.out)) →ₗ[k] ↥(invariants ρ) :=
      LinearMap.codRestrict (invariants ρ) L
        (fun a => by rw [hLval]; exact Submodule.sum_mem _ (fun ω _ => averageMap_invariant ρ _))
    refine LinearMap.finrank_le_finrank_of_injective (f := ψ) (fun a b hab => ?_)
    -- the `ω.out`-component of `ψ a` reads off `⅟|G| • (a ω)`.
    have hcomp : ∀ (a : ∀ ω : orbitRel.Quotient G ι, ↥(A ω.out))
        (ω : orbitRel.Quotient G ι),
        e.symm ((ψ a : ↥(invariants ρ)) : V) ω.out = ⅟(Fintype.card G : k) • a ω := by
      intro a ω
      change e.symm (L a) ω.out = _
      rw [hLval]
      rw [map_sum, DirectSum.sum_apply, Finset.sum_eq_single ω]
      · -- the `ω`-term: `e.symm (averageMap (a ω)) ω.out = ⅟|G| • a ω`.
        rw [averageMap_apply, map_smul, DirectSum.smul_apply, map_sum, DirectSum.sum_apply,
          Finset.sum_eq_single (1 : G)]
        · rw [map_one, Module.End.one_apply, hcs ω.out _ (a ω).2]
        · intro g _ hg1
          refine hcn (g • ω.out) ω.out _ (hmem g ω.out _ (a ω).2) (fun hc => hg1 ?_)
          exact hfree g ω.out hc
        · intro h; exact absurd (Finset.mem_univ (1 : G)) h
      · intro ω' _ hω'
        rw [averageMap_apply, map_smul, DirectSum.smul_apply, map_sum, DirectSum.sum_apply]
        rw [show (∑ g : G, e.symm (ρ g ((a ω' : ↥(A ω'.out)) : V)) ω.out) = 0 from ?_, smul_zero]
        refine Finset.sum_eq_zero (fun g _ => ?_)
        refine hcn (g • ω'.out) ω.out _ (hmem g ω'.out _ (a ω').2) (fun hc => hω' ?_)
        exact (orbit_out_eq g hc).symm
      · intro h; exact absurd (Finset.mem_univ ω) h
    funext ω
    have key : ⅟(Fintype.card G : k) • a ω = ⅟(Fintype.card G : k) • b ω := by
      rw [← hcomp a ω, ← hcomp b ω, hab]
    have := congrArg (fun z => (Fintype.card G : k) • z) key
    simpa [smul_smul, mul_invOf_self] using this

set_option linter.unusedFintypeInType false in
/-- **Free multi-orbit fixed-space count** (the Brauer-free engine of (†)).  If `V = ⊕_{i:ι} A i`
(internal) and `G` acts **freely** on the finite index set `ι`, permuting the summands
(`(A i).map (ρ a) = A (a • i)`), with `|G|` invertible, then `dim V = |G| · dim Vᴳ`.

Applied with `W = [V,U]` (so `W^U = 0`), `ι` = the nontrivial `U`-isotypic components, `G = E`
permuting them freely (3d.3c), this is the kernel-FPF dimension fact (†) `dim W = |E|·dim Wᴱ`. -/
theorem finrank_eq_card_mul_finrank_invariants_of_free (ρ : Representation k G V)
    [Fintype G] [Invertible (Fintype.card G : k)] [FiniteDimensional k V]
    [Fintype (orbitRel.Quotient G ι)]
    {A : ι → Submodule k V} (hint : DirectSum.IsInternal A)
    (hperm : ∀ (a : G) (i : ι), (A i).map (ρ a) = A (a • i))
    (hfree : ∀ (a : G) (i : ι), a • i = i → a = 1) :
    finrank k V = Fintype.card G * finrank k ↥(invariants ρ) := by
  rw [finrank_eq_card_mul_sum_out ρ hint hperm hfree,
    finrank_invariants_eq_sum_out ρ hint hperm hfree]

end OddOrder.GroupTheory.WielandtCounting
