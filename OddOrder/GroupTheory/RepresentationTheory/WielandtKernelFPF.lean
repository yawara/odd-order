/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CenterOrbitFree
import OddOrder.GroupTheory.RepresentationTheory.CenterProjConjugation
import OddOrder.GroupTheory.RepresentationTheory.FreeOrbitModuleCount

/-!
# Peterfalvi (9.1): the kernel-FPF dimension fact (†) over an algebraically closed field

This file assembles the **kernel fixed-point-free dimension fact (†)** of Peterfalvi (9.1):
for a finite group `Γ` acting through `ψ : Γ →* MulAut G` on a `p′`-group `G` (split over an
algebraically closed field `k`) so that every nonidentity `ψ γ` is fixed-point-free, the dimension
identity `dim W = |Γ| · dim Wᴳ` holds for any finite-dimensional `k[Γ ⋉ G]`-module `W` with no
`G`-invariants (`Wᴳ = 0`).

The two completed engines it stitches together are:

* `CenterOrbitFree.gamma_free_off_trivial_simple` (3d.3c): `Γ` acts on the simples `Fin N` with a
  unique fixed point `i₀` (the trivial simple) and freely off it;
* `WielandtCounting.finrank_eq_card_mul_finrank_invariants_of_free`: the Brauer-free free-orbit
  dimension count, fed the isotypic decomposition `W = ⊕ᵢ range (centerProj φ ρ i)`
  (`CenterModuleDecomp.isInternal_centerProj`) with the permutation supplied by
  `CenterProjConjugation.map_range_centerProj` (item 0).

## Main results (growing bottom-up)

* `exists_fixed_simple_free_of_fpf` (item 1) — packages 3d.3c with the *canonical* induced actions
  (`Γ` on `ConjClasses G` through `ψ`, `Γ` on `Fin N` through `simplesAction φ ∘ ψ`): there is a
  simple `i₀` fixed by all of `Γ`, and `Γ` acts freely off it (`i ≠ i₀ ∧ simplesAction φ (ψ γ) i = i
  ⟹ γ = 1`).

`notes/peterfalvi/s11_wielandt_91_design.md` (NEXT — carrier-level, items 1–2), issue 2014.
-/

namespace OddOrder.GroupTheory.WielandtKernelFPF

open OddOrder.GroupTheory.CenterSimplesOrbit (simplesAction)
open OddOrder.GroupTheory.CenterOrbitFree (gamma_free_off_trivial_simple)
open MulAction

variable {G : Type*} [Group G] [Finite G]

/-- **Peterfalvi (9.1), item 1 — the free `Γ`-action on the nontrivial simples.**
Fix a splitting `φ : Z(k[G]) ≃ₐ[k] (Fin N → k)` and let a finite group `Γ` act through
`ψ : Γ →* MulAut G` so that every nonidentity `ψ γ` is fixed-point-free (`hfpf`) with `⟨ψ γ⟩`
coprime to `|G|` (`hcop`).  Then on the simples `Fin N` (acted on by `simplesAction φ ∘ ψ`) there is
a simple `i₀` — the trivial one — fixed by all of `Γ`, and `Γ` acts **freely off it**: for `i ≠ i₀`,
any `γ` fixing `i` is the identity.

This is `gamma_free_off_trivial_simple` (3d.3c) packaged with the canonical induced `Γ`-actions
(`Γ` on `ConjClasses G` via `ψ`, `Γ` on `Fin N` via `simplesAction φ ∘ ψ`), with the orbit-size
statement converted to triviality of the point stabilisers off `i₀`. -/
theorem exists_fixed_simple_free_of_fpf
    {k : Type*} [Field k] {N : ℕ}
    (φ : Subalgebra.center k (MonoidAlgebra k G) ≃ₐ[k] (Fin N → k))
    {Γ : Type*} [Group Γ] [Finite Γ] (ψ : Γ →* MulAut G)
    (hd : 1 < Nat.card Γ)
    (hcop : ∀ γ : Γ, γ ≠ 1 → Nat.Coprime (Nat.card ↥(Subgroup.zpowers (ψ γ))) (Nat.card G))
    (hfpf : ∀ γ : Γ, γ ≠ 1 → ∀ x : G, ψ γ x = x → x = 1) :
    ∃ i₀ : Fin N,
      (∀ γ : Γ, simplesAction φ (ψ γ) i₀ = i₀) ∧
      (∀ (i : Fin N) (γ : Γ), i ≠ i₀ → simplesAction φ (ψ γ) i = i → γ = 1) := by
  classical
  haveI : Fintype G := Fintype.ofFinite _
  haveI : Finite (ConjClasses G) := Finite.of_surjective _ ConjClasses.mk_surjective
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  -- The canonical induced `Γ`-actions, through which 3d.3c applies (`hcl`/`hsi` are then `rfl`).
  letI mulCl : MulAction Γ (ConjClasses G) := MulAction.compHom (ConjClasses G) ψ
  letI mulSi : MulAction Γ (Fin N) := MulAction.compHom (Fin N) ((simplesAction φ).comp ψ)
  have hcl : ∀ (γ : Γ) (C : ConjClasses G), γ • C = ψ γ • C := fun _ _ => rfl
  have hsi : ∀ (γ : Γ) (i : Fin N), γ • i = simplesAction φ (ψ γ) i := fun _ _ => rfl
  obtain ⟨i₀, hi₀fix, hi₀uniq, hi₀free⟩ :=
    gamma_free_off_trivial_simple φ ψ hcl hsi hd hcop hfpf
  refine ⟨i₀, fun γ => ?_, fun i γ hi hfix => ?_⟩
  · -- `i₀` is fixed by every `γ`: read `mem_fixedPoints` through `hsi`.
    have := mem_fixedPoints.mp hi₀fix γ
    rwa [hsi] at this
  · -- `i ≠ i₀ ⟹ i ∉ fixedPoints` (uniqueness) ⟹ `|orbit i| = |Γ|` ⟹ trivial stabiliser.
    have hi_nf : i ∉ fixedPoints Γ (Fin N) := fun hc => hi (hi₀uniq i hc)
    have horb : Nat.card (orbit Γ i) = Nat.card Γ := hi₀free i hi_nf
    -- orbit–stabiliser: `|Γ| = |orbit i| · |stab i|`, so `|stab i| = 1`, hence `stab i = ⊥`.
    have hqs : Nat.card (Γ ⧸ stabilizer Γ i) = Nat.card Γ := by
      rw [← Nat.card_congr (orbitEquivQuotientStabilizer Γ i), horb]
    have hstab1 : Nat.card ↥(stabilizer Γ i) = 1 := by
      have hmul := Subgroup.card_mul_index (stabilizer Γ i)
      rw [Subgroup.index_eq_card, hqs] at hmul
      have hpos : 0 < Nat.card Γ := Nat.card_pos
      have h1 : Nat.card ↥(stabilizer Γ i) * Nat.card Γ = 1 * Nat.card Γ := by
        rw [one_mul]; exact hmul
      exact Nat.eq_of_mul_eq_mul_right hpos h1
    have hstabbot : stabilizer Γ i = ⊥ := Subgroup.card_eq_one.mp hstab1
    have hγstab : γ ∈ stabilizer Γ i := by
      rw [mem_stabilizer_iff, hsi]; exact hfix
    rw [hstabbot, Subgroup.mem_bot] at hγstab
    exact hγstab

end OddOrder.GroupTheory.WielandtKernelFPF
