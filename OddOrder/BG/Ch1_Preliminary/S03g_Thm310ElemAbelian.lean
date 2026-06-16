import OddOrder.BG.Ch1_Preliminary.S03g_Thm310General
import OddOrder.BG.Ch1_Preliminary.S03e_Thm35

/-!
# BG Theorem 3.10 for elementary abelian `M` — the reducible-module induction (issue 8013, piece 5)

`prime_card_and_finrank_of_frobenius_general` (piece 3) proves BG Theorem 3.10 (a)+(b) in the
**irreducible**-module case for a general Frobenius kernel.  The §15.2 application (issue 8012 step 4)
acts on `M = Q̄`, an elementary abelian group that may be **reducible** as a module for the Frobenius
group `KD`.  BG handles this by Case 1 of the Theorem 3.10 proof (mmd L1287-1317): an induction on
the module, splitting a reducible `M` along a proper `G`-invariant submodule and combining the two
pieces.

This file carries out that induction over **subrepresentations of the fixed `ρ`** (no
type-polymorphism: `V`, `G`, `K`, `R` stay fixed, only the subrepresentation `W` varies), with the
conclusion phrased in ambient `finrank`s.  The irreducible leaves call piece 3; reducible `W` split
via Maschke (`W = W₀ ⊕ W₁`, both subreps) and combine `finrank` additively.

**Status (issue 8013 piece 5)**: building the bridging infrastructure (invariants of a
subrepresentation vs. ambient `C_V(H) ⊓ W`); the induction follows.
-/

namespace OddOrder.BG.Ch1.S03

open Module

variable {F : Type*} [Field F] {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module F V]

/-- **Bridging lemma: invariants of a subrepresentation, as an ambient `finrank`** (issue 8013
piece 5).  For a subrepresentation `W ≤ ρ` and a subgroup `H ≤ G`, the `H`-invariants of the
restricted representation `W.toRepresentation` (a submodule of `↥W.toSubmodule`) have the same
`finrank` as the ambient intersection `C_V(H) ⊓ W = invariants(ρ.comp H) ⊓ W.toSubmodule`
(a submodule of `V`).

This lets the reducible-module induction phrase every conclusion in ambient `finrank`s (so the
recursion stays over subrepresentations of the *fixed* `ρ`), while the irreducible leaves still
feed `prime_card_and_finrank_of_frobenius_general` through `W.toRepresentation`. -/
theorem invariants_toRepresentation_map_eq (ρ : Representation F G V) (W : Subrepresentation ρ)
    (H : Subgroup G) :
    (Representation.invariants (W.toRepresentation.comp H.subtype)).map W.toSubmodule.subtype
      = Representation.invariants (ρ.comp H.subtype) ⊓ W.toSubmodule := by
  ext v
  constructor
  · rintro ⟨⟨w, hw⟩, hinv, rfl⟩
    have hinv' := (Representation.mem_invariants (W.toRepresentation.comp H.subtype) ⟨w, hw⟩).mp hinv
    refine Submodule.mem_inf.mpr
      ⟨(Representation.mem_invariants (ρ.comp H.subtype) w).mpr fun g => ?_, hw⟩
    have hg := congrArg Subtype.val (hinv' g)
    simpa [Subrepresentation.toRepresentation, LinearMap.restrict_coe_apply] using hg
  · intro hv
    obtain ⟨hfix, hw⟩ := Submodule.mem_inf.mp hv
    have hfix' := (Representation.mem_invariants (ρ.comp H.subtype) v).mp hfix
    refine ⟨⟨v, hw⟩, (Representation.mem_invariants (W.toRepresentation.comp H.subtype)
      ⟨v, hw⟩).mpr fun g => ?_, rfl⟩
    apply Subtype.ext
    simpa [Subrepresentation.toRepresentation, LinearMap.restrict_coe_apply] using hfix' g

theorem finrank_invariants_toRepresentation_inf (ρ : Representation F G V)
    (W : Subrepresentation ρ) (H : Subgroup G) :
    finrank F (Representation.invariants (W.toRepresentation.comp H.subtype))
      = finrank F ↥(Representation.invariants (ρ.comp H.subtype) ⊓ W.toSubmodule) := by
  rw [← Submodule.finrank_map_subtype_eq W.toSubmodule
    (Representation.invariants (W.toRepresentation.comp H.subtype)),
    invariants_toRepresentation_map_eq]

/-- **Hypothesis restriction: trivial invariants pass to a subrepresentation** (issue 8013 piece 5).
If `C_V(H) ⊓ W = ⊥` then the `H`-invariants of `W.toRepresentation` are `⊥`.  Used to transfer
`C_V(K) = ⊥` to the pieces `U, U'` of a Maschke split. -/
theorem invariants_toRepresentation_eq_bot (ρ : Representation F G V) (W : Subrepresentation ρ)
    (H : Subgroup G) (h : Representation.invariants (ρ.comp H.subtype) ⊓ W.toSubmodule = ⊥) :
    Representation.invariants (W.toRepresentation.comp H.subtype) = ⊥ := by
  have hmap := invariants_toRepresentation_map_eq ρ W H
  rw [h] at hmap
  apply Submodule.map_injective_of_injective (Submodule.injective_subtype W.toSubmodule)
  rw [Submodule.map_bot]
  exact hmap

/-- **Hypothesis restriction: the prime-manner equality passes to a subrepresentation** (issue 8013
piece 5).  If `C_V(H₁) ⊓ W = C_V(H₂) ⊓ W` then the `H₁`- and `H₂`-invariants of `W.toRepresentation`
agree.  Used to transfer the subspace-form prime-manner hypothesis `C_V(x) = C_V(R)` to `U, U'`. -/
theorem invariants_toRepresentation_eq_of_inf_eq (ρ : Representation F G V) (W : Subrepresentation ρ)
    (H₁ H₂ : Subgroup G)
    (h : Representation.invariants (ρ.comp H₁.subtype) ⊓ W.toSubmodule
      = Representation.invariants (ρ.comp H₂.subtype) ⊓ W.toSubmodule) :
    Representation.invariants (W.toRepresentation.comp H₁.subtype)
      = Representation.invariants (W.toRepresentation.comp H₂.subtype) := by
  apply Submodule.map_injective_of_injective (Submodule.injective_subtype W.toSubmodule)
  rw [invariants_toRepresentation_map_eq, invariants_toRepresentation_map_eq, h]

/-- **Invariants distribute over an internal direct sum of subrepresentations** (issue 8013 piece 5).
For two subrepresentations `W₀, W₁ ≤ ρ` that meet trivially (`W₀ ⊓ W₁ = ⊥`), the `H`-invariants of
their sum split: `C_V(H) ⊓ (W₀ ⊔ W₁) = (C_V(H) ⊓ W₀) ⊔ (C_V(H) ⊓ W₁)`.  This is NOT general lattice
distributivity (which fails for submodules); it uses that `W₀, W₁` are `H`-stable, so an `H`-fixed
vector's (unique, by disjointness) decomposition has `H`-fixed components.  Hence the `finrank`s add,
which drives the additive step of the reducible-module induction. -/
theorem finrank_inf_invariants_sup_of_disjoint (ρ : Representation F G V) [FiniteDimensional F V]
    (W₀ W₁ : Subrepresentation ρ) (H : Subgroup G)
    (hdisj : W₀.toSubmodule ⊓ W₁.toSubmodule = ⊥) :
    finrank F ↥(Representation.invariants (ρ.comp H.subtype) ⊓ (W₀.toSubmodule ⊔ W₁.toSubmodule))
      = finrank F ↥(Representation.invariants (ρ.comp H.subtype) ⊓ W₀.toSubmodule)
        + finrank F ↥(Representation.invariants (ρ.comp H.subtype) ⊓ W₁.toSubmodule) := by
  set C := Representation.invariants (ρ.comp H.subtype) with hC
  -- The key `H`-equivariant distributivity.
  have hdistrib : C ⊓ (W₀.toSubmodule ⊔ W₁.toSubmodule)
      = (C ⊓ W₀.toSubmodule) ⊔ (C ⊓ W₁.toSubmodule) := by
    refine le_antisymm (fun v hv => ?_) (sup_le (inf_le_inf_left C le_sup_left)
      (inf_le_inf_left C le_sup_right))
    obtain ⟨hvC, hvW⟩ := Submodule.mem_inf.mp hv
    obtain ⟨v₀, hv₀, v₁, hv₁, rfl⟩ := Submodule.mem_sup.mp hvW
    have hfix := (Representation.mem_invariants (ρ.comp H.subtype) (v₀ + v₁)).mp hvC
    -- Each component is `H`-fixed: `ρ h v₀ - v₀ ∈ W₀ ⊓ W₁ = ⊥`.
    have hcomp : ∀ h : ↥H, ρ (H.subtype h) v₀ = v₀ ∧ ρ (H.subtype h) v₁ = v₁ := by
      intro h
      have hadd : ρ (H.subtype h) v₀ + ρ (H.subtype h) v₁ = v₀ + v₁ := by
        have := hfix h; rwa [MonoidHom.comp_apply, map_add] at this
      have hdiff : ρ (H.subtype h) v₀ - v₀ = v₁ - ρ (H.subtype h) v₁ := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm v₁ v₀]; exact hadd
      have hin0 : ρ (H.subtype h) v₀ - v₀ ∈ W₀.toSubmodule :=
        W₀.toSubmodule.sub_mem (W₀.apply_mem_toSubmodule _ hv₀) hv₀
      have hin1 : ρ (H.subtype h) v₀ - v₀ ∈ W₁.toSubmodule :=
        hdiff ▸ W₁.toSubmodule.sub_mem hv₁ (W₁.apply_mem_toSubmodule _ hv₁)
      have hz : ρ (H.subtype h) v₀ - v₀ = 0 := by
        have : ρ (H.subtype h) v₀ - v₀ ∈ W₀.toSubmodule ⊓ W₁.toSubmodule := ⟨hin0, hin1⟩
        rwa [hdisj, Submodule.mem_bot] at this
      refine ⟨sub_eq_zero.mp hz, ?_⟩
      have := hadd; rw [sub_eq_zero.mp hz] at this; exact (add_right_inj v₀).mp this
    refine Submodule.mem_sup.mpr ⟨v₀, ⟨?_, hv₀⟩, v₁, ⟨?_, hv₁⟩, rfl⟩
    · exact (Representation.mem_invariants (ρ.comp H.subtype) v₀).mpr fun h => by
        rw [MonoidHom.comp_apply]; exact (hcomp h).1
    · exact (Representation.mem_invariants (ρ.comp H.subtype) v₁).mpr fun h => by
        rw [MonoidHom.comp_apply]; exact (hcomp h).2
  have hdisj' : (C ⊓ W₀.toSubmodule) ⊓ (C ⊓ W₁.toSubmodule) = ⊥ := by
    refine le_antisymm (le_trans ?_ hdisj.le) bot_le
    exact le_inf (le_trans inf_le_left inf_le_right) (le_trans inf_le_right inf_le_right)
  have hkey := Submodule.finrank_sup_add_finrank_inf_eq (C ⊓ W₀.toSubmodule) (C ⊓ W₁.toSubmodule)
  rw [hdisj', finrank_bot, add_zero] at hkey
  rw [hdistrib, hkey]

end OddOrder.BG.Ch1.S03
