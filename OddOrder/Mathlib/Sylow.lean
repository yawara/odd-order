import Mathlib.GroupTheory.Sylow

/-!
# Sylow subgroups: `p`-elements of the normalizer

Extracted from `OddOrder/GroupTheory/RepresentationTheory/ClassSumCongruence.lean` (issue 0106):
generic material relocated to a light-import leaf so downstream consumers need not pull the
class-sum congruence machinery (rep theory + complex analysis + integral closure).  Declarations
keep their original `OddOrder.RepresentationTheory` namespace so existing call sites are unchanged.
-/

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **A `p`-element normalizing a Sylow `p`-subgroup lies in it.** If `P` is a Sylow `p`-subgroup
of `G` and `u ∈ N_G(P)` generates a `p`-group `⟨u⟩` (i.e. `u` is a `p`-element), then `u ∈ P`.

This is the "`y` is a `p`-element of `L`, and so `y ∈ P`" step of Peterfalvi (6.7.1): in
`L = N_G(P)` the Sylow `p`-subgroup `P` is normal, hence the unique one, so every `p`-element of `L`
lies in `P`.  Proof: `P ⊔ ⟨u⟩` is a `p`-group (both factors are `p`-groups and `⟨u⟩ ≤ N_G(P)`,
`IsPGroup.to_sup_of_normal_left'`); since `P` is a *maximal* `p`-subgroup (`Sylow.is_maximal'`) and
`P ≤ P ⊔ ⟨u⟩`, this forces `P ⊔ ⟨u⟩ = P`, whence `u ∈ P`. -/
theorem mem_sylow_of_mem_normalizer_of_isPGroup {p : ℕ} [Fact p.Prime] (P : Sylow p G) {u : G}
    (hu : u ∈ Subgroup.normalizer (P : Subgroup G)) (hup : IsPGroup p (Subgroup.zpowers u)) :
    u ∈ (P : Subgroup G) := by
  -- `⟨u⟩ ≤ N_G(P)`, so `P ⊔ ⟨u⟩` is a `p`-group.
  have hzle : Subgroup.zpowers u ≤ Subgroup.normalizer (P : Subgroup G) :=
    Subgroup.zpowers_le.mpr hu
  have hsup : IsPGroup p ((P : Subgroup G) ⊔ Subgroup.zpowers u : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' P.2 hup hzle
  -- `P` is maximal among `p`-subgroups, and `P ≤ P ⊔ ⟨u⟩`, so the join collapses to `P`.
  have heq : ((P : Subgroup G) ⊔ Subgroup.zpowers u : Subgroup G) = (P : Subgroup G) :=
    P.3 hsup le_sup_left
  -- `u ∈ ⟨u⟩ ≤ P ⊔ ⟨u⟩ = P`.
  have humem : u ∈ ((P : Subgroup G) ⊔ Subgroup.zpowers u : Subgroup G) :=
    (le_sup_right : Subgroup.zpowers u ≤ _) (Subgroup.mem_zpowers u)
  rwa [heq] at humem


end OddOrder.RepresentationTheory
