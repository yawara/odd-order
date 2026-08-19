/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import OddOrder.Algebra.RelativeTrace

/-!
# Defect groups

Let a finite group `G` act on a ring `A` by ring automorphisms.  A **defect group** of a
`G`-fixed element `b` is a subgroup `D` that is minimal subject to `b ∈ A^G_D = Tr^G_D(A^D)`.

For `A = 𝒪G` acting by conjugation and `b = e_B` a block idempotent this is Brauer's notion of
the defect group of the block `B`.

Two basic facts are proved here, and they use nothing beyond the relative-trace API:

* defect groups exist — because `A^G_G = A^G` puts `G` itself in the (finite) set of candidates,
  and the candidates decrease under `relTraceIdeal_mono`;
* defect groups are `p`-groups whenever the indices prime to `p` are invertible — because a
  Sylow `p`-subgroup `Q ≤ D` has `[D : Q]` invertible, so `A^D_Q = A^D` and therefore
  `A^G_Q = A^G_D ∋ b`; minimality forces `Q = D`.

## Main definitions

* `OddOrder.GAlgebra.IsDefectGroup`

## Main results

* `OddOrder.GAlgebra.exists_isDefectGroup`
* `OddOrder.GAlgebra.isPGroup_of_isDefectGroup`
-/

namespace OddOrder.GAlgebra

variable {G : Type*} [Group G] [Finite G] {A : Type*} [Ring A] [MulSemiringAction G A]

/-- `D` is a **defect group** of `b` when `b` is a relative trace from `D` and from no proper
subgroup of `D`. -/
structure IsDefectGroup (b : A) (D : Subgroup G) : Prop where
  /-- `b` lies in the relative trace ideal `A^G_D`. -/
  mem : b ∈ relTraceIdeal D ⊤
  /-- No proper subgroup of `D` does. -/
  minimal : ∀ E : Subgroup G, E < D → b ∉ relTraceIdeal E ⊤

/-- **Defect groups exist.**  Every `G`-fixed element has one, because `G` itself is a candidate
(`A^G_G = A^G`) and the subgroup lattice of a finite group is well-founded. -/
theorem exists_isDefectGroup {b : A} (hb : ∀ g : G, g • b = b) :
    ∃ D : Subgroup G, IsDefectGroup b D := by
  have htop : b ∈ relTraceIdeal (⊤ : Subgroup G) ⊤ :=
    mem_relTraceIdeal_self.mpr fun g _ => hb g
  obtain ⟨D, hD, hmin⟩ :=
    (IsWellFounded.wf (r := (· < · : Subgroup G → Subgroup G → Prop))).has_min
      {D : Subgroup G | b ∈ relTraceIdeal D ⊤} ⟨⊤, htop⟩
  exact ⟨D, hD, fun E hE hEmem => hmin E hEmem hE⟩

variable {p : ℕ}

/-- **Defect groups are `p`-groups**, provided every index prime to `p` is invertible in `A` by a
`G`-fixed element (which holds for an algebra over a field of characteristic `p`).

Indeed a Sylow `p`-subgroup `Q` of `D` has `[D : Q]` prime to `p`, hence `A^D_Q = A^D`; composing
with `Tr^G_D` gives `A^G_Q = A^G_D`, so `b ∈ A^G_Q` and minimality forces `Q = D`. -/
theorem isPGroup_of_isDefectGroup (hp : p.Prime)
    (hinv : ∀ n : ℕ, ¬ p ∣ n → ∃ v : A, (∀ g : G, g • v = v) ∧ (n • (1 : A)) * v = 1)
    {b : A} {D : Subgroup G} (hD : IsDefectGroup b D) : IsPGroup p ↥D := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥D) := inferInstance
  set Q' : Subgroup G := Q.1.map D.subtype with hQ'
  have hQ'D : Q' ≤ D := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hsub : (Q' : Subgroup G).subgroupOf D = Q.1 := by
    rw [hQ', Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
  have hindex : ¬ p ∣ Q'.relIndex D := by
    rw [Subgroup.relIndex, hsub]
    exact Q.not_dvd_index
  obtain ⟨v, hv, hvinv⟩ := hinv _ hindex
  -- Pull the trace from `D` down to `Q'`.
  obtain ⟨a, ha, hab⟩ := hD.mem
  have haQ : a ∈ relTraceIdeal Q' D :=
    mem_relTraceIdeal_of_index_inv hQ'D ha (fun g _ => hv g) hvinv
  obtain ⟨a', ha', ha'D⟩ := haQ
  have hbQ : b ∈ relTraceIdeal Q' ⊤ := by
    refine ⟨a', ha', ?_⟩
    rw [← hab, ← ha'D]
    exact (relTrace_trans hQ'D le_top ha').symm
  -- Minimality forces `Q' = D`.
  have hQ'eq : Q' = D := by
    by_contra hne
    exact hD.minimal Q' (lt_of_le_of_ne hQ'D hne) hbQ
  -- Hence `Q = ⊤` inside `D`, so `D` is a `p`-group.
  have htop : Q.1 = (⊤ : Subgroup ↥D) := by
    refine Subgroup.map_injective D.subtype_injective ?_
    rw [← hQ', hQ'eq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have := Q.isPGroup'
  rw [htop] at this
  exact this.of_equiv Subgroup.topEquiv

end OddOrder.GAlgebra
