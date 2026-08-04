/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.GroupAlgebraConjugation

/-!
# The sum of a subgroup in the group algebra

`N̂ = ∑_{n ∈ N} n ∈ R[G]` for a finite subgroup `N ≤ G`.  It absorbs multiplication by `N` on
either side (`single_mul_subgroupSum`), is conjugation-invariant — hence central — when `N` is
normal (`conj_smul_subgroupSum`), and when `|N|` is invertible `|N|⁻¹ N̂` is the idempotent
projecting a module onto its `N`-fixed points.

The point of the file is the following criterion, which is what detects the **kernel of a block**
(Navarro (6.10)): a representation `ρ` kills `N` exactly when `ρ(N̂) = |N|·1`.  One direction is
trivial; the other is the absorption `n · N̂ = N̂`, which after applying `ρ` gives
`|N| · ρ(n) = |N| · 1`, and `|N|` is invertible.

Both directions are stated over an arbitrary commutative base ring and for an arbitrary target
algebra — no semisimplicity, no characteristic assumption, and the invertibility of `|N|` is
needed only for the direction that uses it.

## Main definitions

* `OddOrder.GroupAlgebra.subgroupSum` — `N̂ = ∑_{n ∈ N} n`

## Main results

* `OddOrder.GroupAlgebra.single_mul_subgroupSum`, `subgroupSum_mul_single` — absorption
* `OddOrder.GroupAlgebra.conj_smul_subgroupSum` — `N̂` is conjugation-invariant for `N ⊴ G`
* `OddOrder.GroupAlgebra.subgroupSum_mul_subgroupSum` — `N̂² = |N| · N̂`
* `OddOrder.GroupAlgebra.coeff_subgroupSum_one` — the coefficient at `1` is `1`
* `OddOrder.GroupAlgebra.mapRingHom_subgroupSum` — `N̂` survives a coefficient change
* `OddOrder.GroupAlgebra.subgroupSum_mem_center` — `N̂ ∈ Z(R[G])` for `N ⊴ G`
* `OddOrder.GroupAlgebra.map_subgroupSum_of_forall_map_single_eq_one`
* `OddOrder.GroupAlgebra.map_single_eq_one_of_isUnit_map_subgroupSum` — the kernel criterion
* `OddOrder.GroupAlgebra.map_single_eq_one_of_map_subgroupSum` — its `|N| · 1` form
-/

namespace OddOrder.GroupAlgebra

open MonoidAlgebra

open scoped OddOrder.Conjugation

section Basic

variable (R : Type*) [Semiring R] {G : Type*} [Group G] [Finite G]

/-- **The sum of a subgroup** `N̂ = ∑_{n ∈ N} n` in the group algebra. -/
noncomputable def subgroupSum (N : Subgroup G) : MonoidAlgebra R G :=
  letI := Fintype.ofFinite ↥N
  ∑ n : ↥N, single (n : G) (1 : R)

variable {R}

/-- **`n · N̂ = N̂`** for `n ∈ N`: left translation permutes `N`. -/
theorem single_mul_subgroupSum {N : Subgroup G} {n : G} (hn : n ∈ N) :
    single n (1 : R) * subgroupSum R N = subgroupSum R N := by
  letI := Fintype.ofFinite ↥N
  change single n (1 : R) * (∑ m : ↥N, single (m : G) (1 : R))
    = ∑ m : ↥N, single (m : G) (1 : R)
  rw [Finset.mul_sum]
  refine Fintype.sum_bijective (fun m : ↥N => ⟨n, hn⟩ * m)
    (Group.mulLeft_bijective _) _ _ fun m => ?_
  rw [single_mul_single, one_mul]
  rfl

/-- **`N̂ · n = N̂`** for `n ∈ N`. -/
theorem subgroupSum_mul_single {N : Subgroup G} {n : G} (hn : n ∈ N) :
    subgroupSum R N * single n (1 : R) = subgroupSum R N := by
  letI := Fintype.ofFinite ↥N
  change (∑ m : ↥N, single (m : G) (1 : R)) * single n (1 : R)
    = ∑ m : ↥N, single (m : G) (1 : R)
  rw [Finset.sum_mul]
  refine Fintype.sum_bijective (fun m : ↥N => m * ⟨n, hn⟩)
    (Group.mulRight_bijective _) _ _ fun m => ?_
  rw [single_mul_single, one_mul]
  rfl

/-- **`N̂` is conjugation-invariant when `N` is normal**, hence central in `R[G]`. -/
theorem conj_smul_subgroupSum {N : Subgroup G} (hN : N.Normal) (g : G) :
    g • subgroupSum R N = subgroupSum R N := by
  letI := Fintype.ofFinite ↥N
  change g • (∑ m : ↥N, single (m : G) (1 : R)) = ∑ m : ↥N, single (m : G) (1 : R)
  rw [Finset.smul_sum]
  have hconj : ∀ m : ↥N, g * (m : G) * g⁻¹ ∈ N := fun m => hN.conj_mem _ m.2 g
  refine Fintype.sum_bijective (fun m : ↥N => (⟨g * (m : G) * g⁻¹, hconj m⟩ : ↥N)) ?_ _ _
    fun m => conj_smul_single g (m : G) 1
  constructor
  · intro a b hab
    have h : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  · intro b
    have hb : g⁻¹ * (b : G) * g ∈ N := by simpa using hN.conj_mem _ b.2 g⁻¹
    exact ⟨⟨g⁻¹ * (b : G) * g, hb⟩, Subtype.ext (by group)⟩

/-- **`N̂² = |N| · N̂`.**  Each of the `|N|` left translates of `N̂` is `N̂` again. -/
theorem subgroupSum_mul_subgroupSum (N : Subgroup G) :
    subgroupSum R N * subgroupSum R N = (Nat.card ↥N : ℕ) • subgroupSum R N := by
  letI := Fintype.ofFinite ↥N
  have hL : subgroupSum R N * subgroupSum R N
      = (∑ n : ↥N, single (n : G) (1 : R)) * subgroupSum R N := rfl
  rw [hL, Finset.sum_mul,
    Finset.sum_congr rfl fun (n : ↥N) _ => single_mul_subgroupSum n.2,
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]

/-- **The coefficient of `N̂` at `1` is `1`.** -/
theorem coeff_subgroupSum_one (N : Subgroup G) :
    (subgroupSum R N).coeff 1 = 1 := by
  classical
  letI := Fintype.ofFinite ↥N
  have hL : (subgroupSum R N).coeff 1
      = ∑ n : ↥N, (single (n : G) (1 : R)).coeff 1 := by
    change ((∑ n : ↥N, single (n : G) (1 : R)) : MonoidAlgebra R G).coeff 1 = _
    simp
  rw [hL, Finset.sum_eq_single (1 : ↥N)]
  · simp
  · intro b _ hb
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]
    exact fun h => hb (Subtype.ext (by simpa using h))
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **`N̂` is transported by a coefficient change**: it has coefficients `0` and `1` only. -/
theorem mapRingHom_subgroupSum {S : Type*} [Semiring S] (f : R →+* S) (N : Subgroup G) :
    MonoidAlgebra.mapRingHom G f (subgroupSum R N) = subgroupSum S N := by
  letI := Fintype.ofFinite ↥N
  change MonoidAlgebra.mapRingHom G f (∑ n : ↥N, single (n : G) (1 : R))
    = ∑ n : ↥N, single (n : G) (1 : S)
  rw [map_sum]
  exact Finset.sum_congr rfl fun n _ => by rw [MonoidAlgebra.mapRingHom_single, map_one]

end Basic

section Center

variable {R : Type*} [CommSemiring R] {G : Type*} [Group G] [Finite G]

/-- **`N̂` is central for `N ⊴ G`.**  This is what lets `N̂` be fed to a central character. -/
theorem subgroupSum_mem_center {N : Subgroup G} (hN : N.Normal) :
    subgroupSum R N ∈ Subalgebra.center R (MonoidAlgebra R G) :=
  Subalgebra.mem_center_iff.mpr fun y =>
    (forall_smul_eq_iff_mem_center.mp (fun g => conj_smul_subgroupSum hN g) y).symm

end Center

section AlgHom

variable {R : Type*} [CommSemiring R] {G : Type*} [Group G] [Finite G] {A : Type*} [Semiring A]
  [Algebra R A]

/-- If `ρ` kills `N`, then `ρ(N̂) = |N| · 1`. -/
theorem map_subgroupSum_of_forall_map_single_eq_one
    (ρ : MonoidAlgebra R G →ₐ[R] A) {N : Subgroup G}
    (h : ∀ n ∈ N, ρ (single n (1 : R)) = 1) :
    ρ (subgroupSum R N) = (Nat.card ↥N : ℕ) • (1 : A) := by
  letI := Fintype.ofFinite ↥N
  change ρ (∑ m : ↥N, single (m : G) (1 : R)) = _
  rw [map_sum]
  rw [Finset.sum_congr rfl fun (m : ↥N) _ => h (m : G) m.2]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]

/-- **The kernel criterion.**  If `ρ(N̂)` is a unit then `ρ` kills `N`.

This is what identifies `ker(B)` in Navarro (6.10): for an absolutely irreducible representation
`ρ` in the block `B`, the central element `N̂` acts by the scalar `ω(N̂)`, and that scalar being a
unit forces `N ≤ ker ρ`.  The only input is the absorption `n · N̂ = N̂`. -/
theorem map_single_eq_one_of_isUnit_map_subgroupSum
    (ρ : MonoidAlgebra R G →ₐ[R] A) {N : Subgroup G}
    (hinv : IsUnit (ρ (subgroupSum R N)))
    {n : G} (hn : n ∈ N) : ρ (single n (1 : R)) = 1 := by
  have key : ρ (single n (1 : R)) * ρ (subgroupSum R N) = ρ (subgroupSum R N) := by
    rw [← map_mul, single_mul_subgroupSum hn]
  obtain ⟨u, hu⟩ := hinv
  have h2 : ρ (single n (1 : R)) * (u : A) = 1 * (u : A) := by rw [one_mul, hu, key]
  simpa using congrArg (· * (↑u⁻¹ : A)) h2

/-- **The kernel criterion** in the form Navarro states it: `ρ(N̂) = |N| · 1` with `|N|`
invertible. -/
theorem map_single_eq_one_of_map_subgroupSum
    (ρ : MonoidAlgebra R G →ₐ[R] A) {N : Subgroup G}
    (hinv : IsUnit ((Nat.card ↥N : ℕ) • (1 : A)))
    (h : ρ (subgroupSum R N) = (Nat.card ↥N : ℕ) • (1 : A))
    {n : G} (hn : n ∈ N) : ρ (single n (1 : R)) = 1 :=
  map_single_eq_one_of_isUnit_map_subgroupSum ρ (h ▸ hinv) hn

end AlgHom

end OddOrder.GroupAlgebra
