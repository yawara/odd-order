/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S08_CoherenceTheorems

/-!
# Peterfalvi §10–16: the coherence-wiring bridge to (6.8)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000).

The Pf §10–16 maximal-subgroup spine repeatedly asserts that a maximal-subgroup character
family `S` is **coherent** (Peterfalvi (9.11), (10.4), (13.2.d), …).  In the textbook these
are all one and the same fact — the Sibley coherence theorem (6.8) — applied to the Dade
setup attached to the maximal subgroup.  In the formalization the §10–16 spine was written
**before** §8 exposed a citeable interface, so each such rider currently stands as a free
`sorry` over an opaque integral character map / family / support.

This file supplies the **single reusable bridge** that turns any such rider into a *cite* of
the (6.8) capstone `S08.sibleySetup_is_coherent`:

> `coherent_of_sibley` — given a `SibleyDadeHypothesis` for the maximal subgroup (as the
> ambient `L`) together with the identifications matching its Dade map / base family /
> `H^#`-support to the spine's opaque `τ` / `S` / `A₀`, the family is coherent.

The proof is a one-line cite of (6.8) after substituting the three identifications, so it is
**`sorry`-free**.  Its only mathematical input is the `SibleyDadeHypothesis` witness, which is
where the genuine maximal-subgroup structure theory (Pf §14, currently in progress) lands.
This realizes the FT-path "signature 先行整備" decoupling
(`notes/meta/ft_path_policy.md` §4, endpoint **A**):

* downstream (§10–16 owner) cites this bridge with a structure witness — the (6.8) dependency
  is now **explicit**, not a free `sorry`;
* upstream (lane B) fills the (6.8) proof body of `sibleySetup_is_coherent` independently —
  every cite of this bridge then becomes unconditional automatically, with no rewiring.

Reference notes: `notes/meta/ft_path_policy.md`, `notes/peterfalvi/s10_13_maximal_structure.md`.
-/

namespace OddOrder.Peterfalvi.CoherenceWiring

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **Peterfalvi (6.8) coherence-wiring bridge.**

Let `L` be a maximal subgroup (used here as the ambient group of the character theory) and
`H ◁ L` the kernel of its Sibley Dade setup.  Given a faithful Sibley hypothesis `sib`
(`S08.SibleyDadeHypothesis`) for `(G, L, H)` and identifications

* `htau : sib.tau = τ`   — its §4 Dade isometry is the spine's integral character map,
* `hS   : sib.S = S`      — its base family `{Ind_H^L θ}` is the spine's family,
* `hA0  : H^#(supported in L) = A₀` — its `H^#`-support is the spine's `A₀`,

the family `S` is coherent for `τ` on `A₀`.

The proof is the (6.8) capstone `S08.sibleySetup_is_coherent` transported along the three
identifications; it carries no `sorry`.  All the maximal-subgroup content is concentrated in
the `sib` witness (the §14 structure theory), exactly as in Peterfalvi's text, where (13.2.d)
etc. read off "(6.8) applies". -/
noncomputable def coherent_of_sibley {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card L : ℂ)] {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]
    (sib : S08.SibleyDadeHypothesis G L H)
    {τ : S07.IntegralCharacterMap ↥L G} {S : Set (ClassFunction ↥L ℂ)} {A0 : Set ↥L}
    (htau : sib.tau = τ) (hS : sib.S = S)
    (hA0 : S04.supportInSubgroup (S08.sharpImage H) L = A0) :
    S07.IsCoherent τ S A0 := by
  subst htau; subst hS; subst hA0
  exact S08.sibleySetup_is_coherent sib

/-- `Nonempty`-wrapped form of `coherent_of_sibley`, for the spine riders phrased as
`Nonempty (S07.IsCoherent …)` (e.g. Peterfalvi (10.4), (13.2.d)). -/
theorem nonempty_coherent_of_sibley {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card L : ℂ)] {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]
    (sib : S08.SibleyDadeHypothesis G L H)
    {τ : S07.IntegralCharacterMap ↥L G} {S : Set (ClassFunction ↥L ℂ)} {A0 : Set ↥L}
    (htau : sib.tau = τ) (hS : sib.S = S)
    (hA0 : S04.supportInSubgroup (S08.sharpImage H) L = A0) :
    Nonempty (S07.IsCoherent τ S A0) :=
  ⟨coherent_of_sibley sib htau hS hA0⟩

/-- **A Sibley witness for an opaque coherence target `(τ, S, A₀)`.**

This is the single piece of data a §10–16 spine rider needs in order to discharge its
`Nonempty (S07.IsCoherent τ S A₀)` obligation through (6.8): a normal subgroup `H` of the
maximal subgroup `L`, a faithful Sibley Dade hypothesis `sib` for `(G, L, H)`, and the three
identifications matching `sib`'s Dade map / base family / `H^#`-support to the spine's opaque
`τ` / `S` / `A₀`.

Constructing one is exactly the maximal-subgroup structure obligation of Peterfalvi §14 (e.g.
the proof of (13.2.d) reads off "(6.8) applies to `S`"); it is *not* part of this wiring layer.
Once a `SibleyTarget` is available, `coherent_of_sibleyTarget` discharges the rider with no
further input — and B's (6.8) proof flows through automatically. -/
structure SibleyTarget {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    (τ : S07.IntegralCharacterMap ↥L G) (S : Set (ClassFunction ↥L ℂ)) (A0 : Set ↥L) where
  /-- The kernel of the Sibley Dade setup, a normal subgroup of the maximal subgroup `L`. -/
  H : Subgroup ↥L
  /-- `|H|` is invertible in `ℂ` (automatic for finite `H`, carried for convenience). -/
  invH : Invertible (Nat.card ↥H : ℂ)
  /-- The faithful Sibley Dade hypothesis (6.8)(a)/(b)/(c) for `(G, L, H)`. -/
  sib : @S08.SibleyDadeHypothesis G _ _ _ L _ _ H invH
  /-- `sib`'s §4 Dade isometry is the spine's integral character map. -/
  tau_eq : sib.tau = τ
  /-- `sib`'s base family `{Ind_H^L θ}` is the spine's family. -/
  S_eq : sib.S = S
  /-- `sib`'s `H^#`-support is the spine's `A₀`. -/
  A0_eq : S04.supportInSubgroup (S08.sharpImage H) L = A0

/-- Discharge an opaque coherence rider `Nonempty (S07.IsCoherent τ S A₀)` from a
`SibleyTarget` witness, via (6.8).  `sorry`-free. -/
theorem coherent_of_sibleyTarget {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card L : ℂ)] {τ : S07.IntegralCharacterMap ↥L G}
    {S : Set (ClassFunction ↥L ℂ)} {A0 : Set ↥L} (w : SibleyTarget τ S A0) :
    Nonempty (S07.IsCoherent τ S A0) :=
  letI := w.invH
  nonempty_coherent_of_sibley w.sib w.tau_eq w.S_eq w.A0_eq

/-- Unwrapped form of `coherent_of_sibleyTarget`, returning the `S07.IsCoherent` datum
directly for callers phrased as `S07.IsCoherent …` rather than `Nonempty (…)`.  This generic
helper is `sorry`-free, but applies only when its `SibleyTarget` input is honestly constructible;
it does not justify a (6.8) reduction when the required TI/support hypotheses fail. -/
noncomputable def cohereOfSibleyTarget {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card L : ℂ)] {τ : S07.IntegralCharacterMap ↥L G}
    {S : Set (ClassFunction ↥L ℂ)} {A0 : Set ↥L} (w : SibleyTarget τ S A0) :
    S07.IsCoherent τ S A0 :=
  letI := w.invH
  coherent_of_sibley w.sib w.tau_eq w.S_eq w.A0_eq

end OddOrder.Peterfalvi.CoherenceWiring
