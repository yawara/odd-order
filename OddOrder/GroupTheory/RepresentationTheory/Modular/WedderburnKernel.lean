/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CharacterInvolution
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryBasis

/-!
# The kernel of an ordinary irreducible, and Navarro's objective

Navarro states the goal of the `Q₈` case of Brauer–Suzuki as

> our objective is to find a nontrivial character in the principal block of `G` which contains `t`
> in its kernel

(p. 139), the point being that the kernel of such a character is a **proper normal subgroup
containing `t`** — exactly what the induction on `|G|` in `BrauerSuzukiQ8` consumes.

This file turns the character-theoretic conclusion into that subgroup:

* the kernel of a representation is a normal subgroup (`representationKernel`);
* for an **involution** `t`, `χ(t) = χ(1)` puts `t` in it — the `−1`-eigenspace of `σ t` has
  dimension `(χ(1) − χ(t))/2`, so it vanishes exactly when the two values agree;
* the kernel of a *non-trivial* Wedderburn component is proper, because a component acting
  trivially would have a constant character, and the character table is invertible.

## Main definitions

* `OddOrder.RepresentationTheory.representationKernel`

## Main results

* `OddOrder.RepresentationTheory.mem_representationKernel_of_character_eq` — `t ∈ ker χ`
* `OddOrder.RepresentationTheory.Modular.representationKernel_ne_top` — a component other than the
  trivial one has proper kernel
* `OddOrder.RepresentationTheory.Modular.exists_proper_normal_of_character_eq` — Navarro's
  objective, packaged as the subgroup
-/

namespace OddOrder.RepresentationTheory

open Module

/-! ### The kernel of a representation -/

section Kernel

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

/-- **The kernel of a representation**, as a subgroup of `G`.  `Module.End K V` is only a monoid,
so this is not `MonoidHom.ker`; but `σ g` is invertible for every `g`, which is what makes the
inverse-closure work. -/
def representationKernel (σ : Representation K G V) : Subgroup G where
  carrier := {g : G | σ g = 1}
  one_mem' := σ.map_one
  mul_mem' {g h} hg hh := by
    change σ (g * h) = 1
    rw [map_mul, show σ g = 1 from hg, show σ h = 1 from hh, one_mul]
  inv_mem' {g} hg := by
    change σ g⁻¹ = 1
    have h := σ.map_mul g⁻¹ g
    rw [inv_mul_cancel, map_one, show σ g = 1 from hg, mul_one] at h
    exact h.symm

@[simp]
theorem mem_representationKernel {σ : Representation K G V} {g : G} :
    g ∈ representationKernel σ ↔ σ g = 1 := Iff.rfl

instance representationKernel_normal (σ : Representation K G V) :
    (representationKernel σ).Normal where
  conj_mem g hg h := by
    change σ (h * g * h⁻¹) = 1
    have hinv : σ h * σ h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [map_mul, map_mul, show σ g = 1 from hg, mul_one, hinv]

variable [FiniteDimensional K V]

/-- **`χ(t) = χ(1)` puts an involution `t` in the kernel.**  `χ(t) = 2 dim V₊ − dim V` and
`χ(1) = dim V`, so the two agree exactly when `V₊` is everything, i.e. when `σ t` is the
identity. -/
theorem mem_representationKernel_of_character_eq (σ : Representation K G V) [CharZero K] {t : G}
    (ht : t * t = 1) (h : σ.character t = σ.character 1) : t ∈ representationKernel σ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  rw [character_eq_of_mul_self_eq_one σ h2 ht, σ.char_one] at h
  have hrank : (finrank K (LinearMap.range (involutionProj σ t)) : K) = (finrank K V : K) := by
    linear_combination h / 2
  have htop : LinearMap.range (involutionProj σ t) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (Nat.cast_injective hrank)
  have hid : ∀ v : V, involutionProj σ t v = v := by
    intro v
    have hv : v ∈ LinearMap.range (involutionProj σ t) := htop ▸ Submodule.mem_top
    obtain ⟨w, rfl⟩ := hv
    exact congrFun (congrArg DFunLike.coe (isIdempotentElem_involutionProj σ h2 ht)) w
  change σ t = 1
  refine LinearMap.ext fun v => ?_
  have hp : (2 : K)⁻¹ • (v + σ t v) = v := by
    simpa [involutionProj] using hid v
  have h2v : v + σ t v = v + v := by
    have hh := congrArg (fun x => (2 : K) • x) hp
    simp only [smul_smul, mul_inv_cancel₀ h2, one_smul] at hh
    rw [hh, two_smul]
  simpa using add_left_cancel h2v

end Kernel

/-! ### A non-trivial Wedderburn component has proper kernel -/

namespace Modular

open Matrix MonoidAlgebra

variable {K G : Type*} [Field K] [Group G] [Fintype G] [Fintype (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι'] [Invertible (Nat.card G : K)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)

set_option linter.unusedFintypeInType false in
/-- **The kernel of a Wedderburn component other than the trivial one is proper.**  A component
acting trivially has a constant character, so it would be a multiple of the trivial character; the
character table is invertible (`eq_ordinaryCoeff`), so its coordinates cannot be both `Pi.single k`
and supported at `i₀ ≠ k`. -/
theorem representationKernel_ne_top {k i₀ : ι'} (hk : k ≠ i₀)
    (hi₀ : ∀ g : G, (wedderburnRepresentation e i₀).character g = 1) :
    representationKernel (wedderburnRepresentation e k) ≠ ⊤ := by
  classical
  intro htop
  have hconst : ∀ g : G, (wedderburnRepresentation e k).character g
      = (wedderburnRepresentation e k).character 1 := by
    intro g
    have hg : (wedderburnRepresentation e k) g = 1 :=
      (mem_representationKernel).mp (htop ▸ Subgroup.mem_top g)
    have hone : (wedderburnRepresentation e k) (1 : G) = 1 := map_one _
    rw [Representation.character, Representation.character, hg, hone]
  have hχ : ∀ g h : G, IsConj g h → (wedderburnRepresentation e k).character g
      = (wedderburnRepresentation e k).character h :=
    fun _ _ hgh => character_eq_of_isConj _ hgh
  -- two expansions of the same class function
  have h1 : (fun i => if i = i₀ then (wedderburnRepresentation e k).character 1 else 0)
      = ordinaryCoeff e (wedderburnRepresentation e k).character hχ := by
    refine eq_ordinaryCoeff e _ hχ fun g => ?_
    rw [Finset.sum_eq_single i₀ (fun b _ hb => by rw [if_neg hb, zero_mul])
        (fun hb => absurd (Finset.mem_univ i₀) hb), if_pos rfl, hi₀ g, mul_one]
    exact (hconst g).symm
  have h2 : (fun i => if i = k then (1 : K) else 0)
      = ordinaryCoeff e (wedderburnRepresentation e k).character hχ := by
    refine eq_ordinaryCoeff e _ hχ fun g => ?_
    rw [Finset.sum_eq_single k (fun b _ hb => by rw [if_neg hb, zero_mul])
        (fun hb => absurd (Finset.mem_univ k) hb), if_pos rfl, one_mul]
  have hk' := congrFun (h2.trans h1.symm) k
  rw [if_pos rfl, if_neg hk] at hk'
  exact one_ne_zero hk'

set_option linter.unusedFintypeInType false in
/-- **Navarro's objective on p. 139, as a subgroup.**  A Wedderburn component `k` other than the
trivial one with `χ_k(t) = χ_k(1)` at an involution `t` has a kernel which is a proper normal
subgroup of `G` containing `t`. -/
theorem exists_proper_normal_of_character_eq [CharZero K] {k i₀ : ι'} (hk : k ≠ i₀)
    (hi₀ : ∀ g : G, (wedderburnRepresentation e i₀).character g = 1) {t : G} (ht : t * t = 1)
    (hchar : (wedderburnRepresentation e k).character t
      = (wedderburnRepresentation e k).character 1) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ t ∈ N :=
  ⟨representationKernel (wedderburnRepresentation e k), inferInstance,
    representationKernel_ne_top e hk hi₀,
    mem_representationKernel_of_character_eq _ ht hchar⟩

end Modular

end OddOrder.RepresentationTheory
