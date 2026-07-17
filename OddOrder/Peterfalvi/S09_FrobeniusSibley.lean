/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S09_FrobeniusHypothesis76
import OddOrder.Peterfalvi.S08_CoherenceTheorems

/-!
# Peterfalvi (6.8) coherence for a Frobenius family — wiring the Sibley datum

The (6.8) coherence capstone `S08.sibleySetup_is_coherent` (sorry-free) produces the coherent
extension `ν` (an `IsCoherent`) for the induced family `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` from a
`S08.SibleyDadeHypothesis`.  Its Frobenius case (c1) is the intended Peterfalvi (7.10) producer.  This
leaf wires the `FrobeniusFamily` (7.10) hypothesis to a `SibleyDadeHypothesis`, unlocking `ν` for the
(7.8.b)/(7.9) character estimates of `card_G0_lower_bound` (issue 0044).

Foundational coordinate lemma first: the Sibley kernel `(H_i).subgroupOf L_i : Subgroup ↥L_i` has
`sharpImage` equal to `(H_i)^# = sharp (H_i)`, matching the `of_isTISubset` Dade support.
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **The Sibley kernel's sharp image is the Frobenius kernel's sharp set.**  For the `i`-th member,
`sharpImage ((H_i).subgroupOf L_i) = (H_i)^#`: since `H_i ≤ L_i`, mapping `(H_i).subgroupOf L_i` back
through `L_i.subtype` recovers `H_i`, and `sharpImage`/`sharp` both remove the identity.  This aligns
the `SibleyDadeHypothesis` support coordinate (a subgroup of `↥L_i`) with the `of_isTISubset` /
`hypothesis71` support `sharp (H_i)` (a subset of `G`). -/
lemma sharpImage_subgroupOf_eq (F : FrobeniusFamily G k) (i : Fin k) :
    OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))
      = OddOrder.Peterfalvi.S04.sharp (F.H i : Set G) := by
  have hmap : Subgroup.map (F.L i).subtype ((F.H i).subgroupOf (F.L i)) = F.H i := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (F.kernel_le i)]
  rw [OddOrder.Peterfalvi.S08.sharpImage, hmap]
  rfl

/-- **The (7.1) datum in the sharpImage coordinate.**  `Hypothesis71 G (sharpImage ((H_i).subgroupOf L_i)) L_i`
— the same TI-subset Dade datum as `hypothesis71`, but with the support written in the
`SibleyDadeHypothesis`/coherence coordinate (`sharpImage H = (H_i)^#` via `sharpImage_subgroupOf_eq`).
Its Dade map `τ` is the real Dade map the (6.8) coherence `coherence` is coherent for, so it is the
`Hypothesis71` to feed `hypothesis78OfDade` alongside `ν = coherence.extension`. -/
noncomputable def sibleyHypothesis71 [Fintype G] (F : FrobeniusFamily G k) (i : Fin k) :
    Hypothesis71 G (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) :=
  Hypothesis71.of_isTISubset
    (by
      rw [sharpImage_subgroupOf_eq]
      intro x hx
      exact OddOrder.Peterfalvi.S04.mem_sharp.mpr
        ⟨Set.mem_univ x, (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).2⟩)
    (by
      rw [sharpImage_subgroupOf_eq]
      intro x hx
      exact F.kernel_le i (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).1)
    (by
      rw [sharpImage_subgroupOf_eq]
      intro l a ha
      exact (F.mem_kernel_sharp_conj_iff_of_mem_L i l.2).mpr ha)
    (by
      rw [sharpImage_subgroupOf_eq]
      exact F.isTI i)

open scoped Classical in
/-- **The Peterfalvi (6.8) Sibley datum for the `i`-th Frobenius member** (case c1).  Assembles a
`SibleyDadeHypothesis G L_i ((H_i).subgroupOf L_i)` from the Frobenius structure `hFrob`
(`isNormal`/`isComplement`/`ne_bot_*`), the TI/Dade datum of `H_i^#` (`of_isTISubset`, whose local
subgroups are trivial), and the kernel-nilpotency `hnilp` (available from `frobeniusKernelIsNilpotent`
for the solvable `L_i` in the FT spine).  Feeding this to `sibleySetup_is_coherent` yields the
coherent extension `ν` for `S = {Ind_{H_i}^{L_i} θ | θ ≠ 1}` (issue 0044). -/
noncomputable def sibleyDadeHypothesis_of_frobenius [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    OddOrder.Peterfalvi.S08.SibleyDadeHypothesis G (F.L i) ((F.H i).subgroupOf (F.L i)) :=
  letI dade0 : OddOrder.Peterfalvi.S04.Hypothesis G
      (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) :=
    OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset
      (by
        rw [sharpImage_subgroupOf_eq]
        intro x hx
        exact OddOrder.Peterfalvi.S04.mem_sharp.mpr
          ⟨Set.mem_univ x, (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).2⟩)
      (by
        rw [sharpImage_subgroupOf_eq]
        intro x hx
        exact F.kernel_le i (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).1)
      (by
        rw [sharpImage_subgroupOf_eq]
        intro l a ha
        exact (F.mem_kernel_sharp_conj_iff_of_mem_L i l.2).mpr ha)
      (by
        rw [sharpImage_subgroupOf_eq]
        exact F.isTI i)
  { W1 := C
    H_ne_bot := hFrob.ne_bot_kernel
    H_normal := hFrob.isNormal
    H_nilpotent := hnilp
    split := hFrob.isComplement
    W1_nontrivial := hFrob.ne_bot_complement
    card_L_odd := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (F.L i))
    H_sharp_ti := by rw [sharpImage_subgroupOf_eq]; exact F.isTI i
    dade := dade0
    hconj := OddOrder.Peterfalvi.S04.Hypothesis.HConjInvariant.of_forall_H_eq_bot dade0 (fun _ => rfl)
    dade_H_eq_bot := fun _ => rfl
    S := {φ : ClassFunction ↥(F.L i) ℂ | ∃ θ : IrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)),
      θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)) ∧
      φ = OddOrder.RepresentationTheory.ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (θ : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ)}
    S_eq := rfl
    cases := Or.inl hFrob }

/-- **The Peterfalvi (6.8) coherence for the `i`-th Frobenius member** — the coherent extension `ν`.
Applies the sorry-free (6.8) capstone `sibleySetup_is_coherent` to
`sibleyDadeHypothesis_of_frobenius`, producing an `IsCoherent` for the induced family
`S = {Ind_{H_i}^{L_i} θ | θ ≠ 1}` relative to the real Dade map.  Its `.extension` is Peterfalvi's
`ν`; `extension_inner_eq` gives the isometry and `extends_on_supported` the Dade agreement — the
inputs the (7.8.b)/(7.9) estimates of `card_G0_lower_bound` consume. -/
noncomputable def coherence [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).CoherenceTarget :=
  OddOrder.Peterfalvi.S08.sibleySetup_is_coherent
    (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob)

/-- **Peterfalvi's coherent extension `ν`** for the `i`-th Frobenius member, as the `ℤ`-linear map
`CF(L_i) →ₗ[ℤ] CF(G)` (`IntegralCharacterMap L_i G` unfolds to exactly this).  This is `.extension`
of the (6.8) `coherence`; it is the `ν` argument of `hypothesis78OfDade`, with `hnu_isometry` supplied
by `coherence.extension_inner_eq` on the induced family `S` and `hagree` by
`coherence.extends_on_supported` on the degree-matched differences `ζ_i − d_i ζ_0`. -/
noncomputable def nu [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    ClassFunction ↥(F.L i) ℂ →ₗ[ℤ] ClassFunction G ℂ :=
  (F.coherence i hodd hnilp C hFrob).extension

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
