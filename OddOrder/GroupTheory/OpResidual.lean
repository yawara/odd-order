/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.Data.SetLike.Fintype
import OddOrder.Isaacs.Ch01_Sylow.Main

/-!
# O_π(G): the π-residual / largest normal π-subgroup (definitional skeleton)

For a set of primes `π` and a finite group `G`, `Subgroup.opPi G π` denotes the
largest normal `π`-subgroup of `G`.

## Main definitions

* `Subgroup.IsPiSubgroup π N` — `N` is a `π`-subgroup: all primes dividing `|N|`
  lie in `π`.
* `Subgroup.opPi G π` — the supremum of all normal `π`-subgroups of `G`.

## BG / Isaacs context

BG §1 Prop 1.4 (`A` coprime auto faithful on `F(G)`) and §6 (Thm 6.4) rely on
the `O_π` machinery generalizing the single-prime `OddOrder.Isaacs.Ch01.opCore p`.

mathlib v4.29.1 does not define `O_π` for prime sets; this file adds the
foundational definitions.  Stronger lemmas (Sylow decomposition of `opPi`,
disjointness with `opPi πᶜ`, etc.) are deferred to follow-up commits.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- A subgroup is a `π`-subgroup if every prime dividing its order lies in `π`. -/
def IsPiSubgroup (π : Set ℕ) (N : Subgroup G) : Prop :=
  ∀ p ∈ (Nat.card N).primeFactors, p ∈ π

namespace IsPiSubgroup

variable {π : Set ℕ} {N M : Subgroup G}

@[simp] theorem bot : (⊥ : Subgroup G).IsPiSubgroup π := by
  intro p hp
  simp at hp

theorem mono {π₁ π₂ : Set ℕ} (h : π₁ ⊆ π₂) (hN : N.IsPiSubgroup π₁) :
    N.IsPiSubgroup π₂ :=
  fun p hp => h (hN p hp)

end IsPiSubgroup

/-- A `p`-group is a `π`-subgroup whenever `p ∈ π` (its order is a power of `p`, so `p` is
the only prime dividing it). -/
theorem isPiSubgroup_of_isPGroup_of_mem {G : Type*} [Group G] [Finite G] {π : Set ℕ} {p : ℕ}
    [Fact p.Prime] {X : Subgroup G} (hX : IsPGroup p ↥X) (hp : p ∈ π) : X.IsPiSubgroup π := by
  intro q hq
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  rw [hk] at hq
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqp : q = p :=
    (Nat.prime_dvd_prime_iff_eq hq_prime Fact.out).mp
      (hq_prime.dvd_of_dvd_pow (Nat.mem_primeFactors.mp hq).2.1)
  rwa [hqp]

variable (G) in
/-- The supremum of all normal `π`-subgroups of `G`.  For finite `G`, this is the
largest normal `π`-subgroup. -/
noncomputable def opPi (π : Set ℕ) [Finite G] : Subgroup G :=
  ⨆ N : { N : Subgroup G // N.Normal ∧ N.IsPiSubgroup π }, (N : Subgroup G)

/-- Any normal `π`-subgroup is contained in `opPi G π`. -/
theorem self_le_opPi (π : Set ℕ) [Finite G] {N : Subgroup G}
    [hN_normal : N.Normal] (hN_pi : N.IsPiSubgroup π) :
    N ≤ opPi G π :=
  le_iSup_of_le ⟨N, hN_normal, hN_pi⟩ le_rfl

/-- `opPi` is monotone in `π`: enlarging the allowed prime set enlarges the residual. -/
theorem opPi_mono {π₁ π₂ : Set ℕ} (h : π₁ ⊆ π₂) [Finite G] :
    opPi G π₁ ≤ opPi G π₂ := by
  refine iSup_le ?_
  rintro ⟨N, hN_normal, hN_pi⟩
  haveI := hN_normal
  exact self_le_opPi π₂ (hN_pi.mono h)

/-- The bottom subgroup is in the indexing family for `opPi`. -/
theorem bot_le_opPi (π : Set ℕ) [Finite G] : (⊥ : Subgroup G) ≤ opPi G π :=
  self_le_opPi π IsPiSubgroup.bot

end Subgroup
