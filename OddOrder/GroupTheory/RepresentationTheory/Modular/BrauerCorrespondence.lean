/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.ClassSumOffCentralizer
import OddOrder.GroupTheory.RepresentationTheory.Modular.TruncClassSum

/-!
# The induced central character is the Brauer homomorphism — Navarro (4.14), first part

**Navarro (4.14).**  Let `P` be a `p`-subgroup of `G` and let `H` satisfy
`P C_G(P) ≤ H ≤ N_G(P)`.  Then for every block `b` of `H` the induced central character is
`λ_b^G = λ_b ∘ Br_P`; in particular it is an algebra homomorphism, so the induced block `b^G` is
always defined.

This file proves the identity that carries the mathematical content:

`λ_b( ∑_{x ∈ K ∩ H} x ) = λ_b( ∑_{x ∈ K ∩ H ∩ C_G(P)} x )`   for every `K ∈ cl(G)`,

and the second sum is `Br_P(K̂)` once `C_G(P) ≤ H`.

Navarro's argument writes `K ∩ H` as `(K ∩ C_G(P)) ⊔ (rest)`, observes that the rest is a union
of `H`-classes missing `C_H(O_p(H))`, and kills each of them with Lemma (4.7).  Since `P ⊴ H`
here, the same orbit count applies to `P` directly: the elements of `K ∩ H` off `C_G(P)` are
exactly the ones whose `P`-conjugation orbit has length `> 1`, so
`OddOrder.GroupAlgebra.pi_sum_ite_single_eq_zero` disposes of them in one step, with no need to
decompose into `H`-classes or to introduce `O_p(H)`.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.centralizerTruncClassSum` — `∑_{x ∈ K ∩ H ∩ C_G(P)} x`

## Main results

* `OddOrder.RepresentationTheory.Modular.mem_centralizer_conj_iff` — `N_G(P)` preserves `C_G(P)`
* `OddOrder.RepresentationTheory.Modular.pi_truncClassSum_eq_centralizerTrunc`
* `OddOrder.RepresentationTheory.Modular.blockCharacter_truncClassSumCenter_eq`
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra OddOrder.MatrixModule OddOrder.GroupAlgebra
open OddOrder.GroupTheory.CenterClassSum

/-! ### Conjugation, the normaliser and the centraliser of `P` -/

section Normalizer

variable {G : Type*} [Group G] {P : Subgroup G}

/-- An element of `N_G(P)` conjugates `C_G(P)` into itself. -/
theorem mem_centralizer_conj_of_mem_normalizer {u : G}
    (hu : u ∈ Subgroup.normalizer (P : Set G)) {x : G}
    (hx : x ∈ Subgroup.centralizer (P : Set G)) :
    u * x * u⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzP : z ∈ P := hz
  have hw : u⁻¹ * z * u ∈ P := by
    have h := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (P : Set G)).inv_mem hu) z).mp hzP
    simpa using h
  have hxw : (u⁻¹ * z * u) * x = x * (u⁻¹ * z * u) :=
    (Subgroup.mem_centralizer_iff.mp hx) _ hw
  calc z * (u * x * u⁻¹) = u * ((u⁻¹ * z * u) * x) * u⁻¹ := by group
    _ = u * (x * (u⁻¹ * z * u)) * u⁻¹ := by rw [hxw]
    _ = (u * x * u⁻¹) * z := by group

/-- Conjugation by an element of `N_G(P)` preserves `C_G(P)`, both ways. -/
theorem mem_centralizer_conj_iff {u : G} (hu : u ∈ Subgroup.normalizer (P : Set G)) (x : G) :
    u * x * u⁻¹ ∈ Subgroup.centralizer (P : Set G) ↔ x ∈ Subgroup.centralizer (P : Set G) := by
  refine ⟨fun h => ?_, mem_centralizer_conj_of_mem_normalizer hu⟩
  have := mem_centralizer_conj_of_mem_normalizer (P := P)
    ((Subgroup.normalizer (P : Set G)).inv_mem hu) h
  simpa [mul_assoc] using this

variable {H : Subgroup G}

/-- Conjugating inside `H` does not move the `G`-class. -/
theorem conjClasses_mk_coe_conj (u x : ↥H) :
    ConjClasses.mk ((u * x * u⁻¹ : ↥H) : G) = ConjClasses.mk (x : G) := by
  have hcoe : ((u * x * u⁻¹ : ↥H) : G) = (u : G) * (x : G) * (u : G)⁻¹ := by push_cast; rfl
  rw [hcoe]
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨(u : G)⁻¹, by group⟩)

/-- Conjugating inside `H ≤ N_G(P)` does not move membership in `C_G(P)`. -/
theorem mem_centralizer_coe_conj_iff (hHN : H ≤ Subgroup.normalizer (P : Set G)) (u x : ↥H) :
    ((u * x * u⁻¹ : ↥H) : G) ∈ Subgroup.centralizer (P : Set G)
      ↔ (x : G) ∈ Subgroup.centralizer (P : Set G) := by
  have hcoe : ((u * x * u⁻¹ : ↥H) : G) = (u : G) * (x : G) * (u : G)⁻¹ := by push_cast; rfl
  rw [hcoe]
  exact mem_centralizer_conj_iff (hHN u.2) (x : G)

end Normalizer

/-! ### The `C_G(P)`-part of `K ∩ H` -/

variable {k G : Type*} [Field k] [Group G] [DecidableEq (ConjClasses G)]
variable (P H : Subgroup G) [Fintype H]
  [DecidablePred fun g : G => g ∈ Subgroup.centralizer (P : Set G)]

/-- **`Br_P(K̂)`, seen inside `k[H]`**: the sum of the elements of the `G`-class `K` that lie in
`H` *and* centralise `P`.  When `C_G(P) ≤ H` the condition `x ∈ H` is automatic, so this is
literally `∑_{x ∈ K ∩ C_G(P)} x`. -/
noncomputable def centralizerTruncClassSum (C : ConjClasses G) : MonoidAlgebra k ↥H :=
  ∑ h : ↥H, if ConjClasses.mk (h : G) = C ∧ (h : G) ∈ Subgroup.centralizer (P : Set G)
    then MonoidAlgebra.of k ↥H h else 0

variable {P H}

/-- The `C_G(P)`-part of `K ∩ H` is central in `k[H]`: `H` normalises `P`, hence `C_G(P)`. -/
theorem centralizerTruncClassSum_mem_center (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (C : ConjClasses G) :
    centralizerTruncClassSum (k := k) P H C ∈ Subalgebra.center k (MonoidAlgebra k ↥H) :=
  sum_ite_mem_center _ fun u x => by
    rw [conjClasses_mk_coe_conj, mem_centralizer_coe_conj_iff hHN]

/-- The `C_G(P)`-part of `K ∩ H`, bundled into the centre of `k[H]`. -/
noncomputable def centralizerTruncClassSumCenter (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (C : ConjClasses G) :
    ↥(Subalgebra.center k (MonoidAlgebra k ↥H)) :=
  ⟨centralizerTruncClassSum P H C, centralizerTruncClassSum_mem_center hHN C⟩

/-! ### Navarro (4.14), first part -/

variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [∀ i, Nonempty (nn i)]
variable (πH : MonoidAlgebra k ↥H →+* ∀ j, Matrix (nn j) (nn j) k)

/-- **Navarro (4.14), first part.**  For `P ≤ H ≤ N_G(P)` with `P` a `p`-group and `char k = p`,
the trace of a `G`-class on `H` and its `C_G(P)`-part have the same image under any splitting of
`k[H]`: the difference is supported on the elements whose `P`-conjugation orbit has length
divisible by `p`. -/
theorem pi_truncClassSum_eq_centralizerTrunc {p : ℕ} [Fact p.Prime] [CharP k p]
    (hπ : Function.Surjective πH)
    (hlin : ∀ (c : k) (a : MonoidAlgebra k ↥H), πH (c • a) = c • πH a)
    (hP : IsPGroup p ↥P) (hPH : P ≤ H) (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (C : ConjClasses G) :
    πH (truncClassSum H C) = πH (centralizerTruncClassSum P H C) := by
  classical
  -- `P`, viewed inside `H`, is a normal `p`-subgroup.
  set Q : Subgroup ↥H := P.subgroupOf H with hQ
  have hmemQ : ∀ y : ↥H, y ∈ Q ↔ (y : G) ∈ P := fun _ => Iff.rfl
  haveI hQnormal : Q.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hmemQ] at hn ⊢
    have hcoe : ((g * n * g⁻¹ : ↥H) : G) = (g : G) * (n : G) * (g : G)⁻¹ := by push_cast; rfl
    rw [hcoe]
    exact (Subgroup.mem_normalizer_iff.mp (hHN g.2) (n : G)).mp hn
  have hQp : IsPGroup p ↥Q := hP.comap_of_injective H.subtype Subtype.val_injective
  -- The part of `K ∩ H` off `C_G(P)` is killed: those are exactly the points of `K ∩ H` whose
  -- `P`-orbit is longer than one.
  have hoff : πH (∑ h : ↥H, if ConjClasses.mk (h : G) = C ∧
      (h : G) ∉ Subgroup.centralizer (P : Set G) then single h (1 : k) else 0) = 0 := by
    refine pi_sum_ite_single_eq_zero πH hπ hlin hQp _ (fun u _ x => ?_) (fun x hx hmem => ?_)
    · rw [conjClasses_mk_coe_conj, mem_centralizer_coe_conj_iff hHN]
    · -- an element of `C_H(Q)` centralises `P`
      refine hx.2 ?_
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzH : z ∈ H := hPH hz
      have hzQ : (⟨z, hzH⟩ : ↥H) ∈ Q := hz
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hmem) (⟨z, hzH⟩ : ↥H) hzQ)
  -- `K ∩ H = (K ∩ H ∩ C_G(P)) ⊔ (rest)`.
  have hsplit : (truncClassSum H C : MonoidAlgebra k ↥H)
      = centralizerTruncClassSum P H C
        + ∑ h : ↥H, if ConjClasses.mk (h : G) = C ∧
            (h : G) ∉ Subgroup.centralizer (P : Set G) then single h (1 : k) else 0 := by
    rw [truncClassSum, centralizerTruncClassSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    by_cases hclass : ConjClasses.mk (h : G) = C
    · by_cases hcent : (h : G) ∈ Subgroup.centralizer (P : Set G)
      · rw [if_pos hclass, if_pos ⟨hclass, hcent⟩, if_neg (by tauto), add_zero, of_apply]
      · rw [if_pos hclass, if_neg (by tauto), if_pos ⟨hclass, hcent⟩, zero_add, of_apply]
    · rw [if_neg hclass, if_neg (by tauto), if_neg (by tauto), add_zero]
  rw [hsplit, map_add, hoff, add_zero]

/-- **Navarro (4.14), first part**, in terms of central characters: `λ_b^G(K̂) = λ_b(Br_P(K̂))`. -/
theorem blockCharacter_truncClassSumCenter_eq [Finite ι] {p : ℕ} [Fact p.Prime] [CharP k p]
    (hπ : Function.Surjective πH)
    (hlin : ∀ (c : k) (a : MonoidAlgebra k ↥H), πH (c • a) = c • πH a)
    (hP : IsPGroup p ↥P) (hPH : P ≤ H) (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (b : Block πH hπ hlin) (C : ConjClasses G) :
    blockCharacter πH hπ hlin b (truncClassSumCenter (k := k) H C)
      = blockCharacter πH hπ hlin b (centralizerTruncClassSumCenter hHN C) := by
  have hz : blockCharacterPi πH hπ hlin
      (truncClassSumCenter (k := k) H C - centralizerTruncClassSumCenter hHN C) = 0 := by
    refine (blockCharacterPi_eq_zero_iff πH hπ hlin).mpr ?_
    rw [show ((truncClassSumCenter (k := k) H C - centralizerTruncClassSumCenter hHN C :
        ↥(Subalgebra.center k (MonoidAlgebra k ↥H))) : MonoidAlgebra k ↥H)
        = truncClassSum H C - centralizerTruncClassSum P H C from rfl, map_sub,
      pi_truncClassSum_eq_centralizerTrunc πH hπ hlin hP hPH hHN C, sub_self]
  have := congrFun hz b
  rw [blockCharacterPi_apply, map_sub, Pi.zero_apply, sub_eq_zero] at this
  exact this

end OddOrder.RepresentationTheory.Modular
