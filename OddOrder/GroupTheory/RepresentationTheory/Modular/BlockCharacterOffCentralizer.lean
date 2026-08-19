/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CenterClassSumBasis
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerCorrespondence

/-!
# A central character of `H` only sees the coefficients on `C_G(P)`

**Navarro (4.14), first part, in `H`-class form.**  `pi_truncClassSum_eq_centralizerTrunc`
compares a *`G`*-class trace on `H` with its `C_G(P)`-part, which is what the Brauer
correspondence `Z(kG) → Z(kH)` needs.  For the third main theorem with a general intermediate
subgroup one needs the same statement one `H`-class at a time:

`π_H(L̂) = 0`  for every `H`-class `L` disjoint from `C_G(P)`,

which is just Navarro (4.7) (`OddOrder.GroupAlgebra.pi_classSum_eq_zero_of_notMem_centralizer`)
applied inside `H` to the normal `p`-subgroup `P.subgroupOf H`, once the hypothesis is restated
with the centraliser taken in `G`.

The consequence used downstream is that a block character of `H` is determined by the
coefficients on `C_G(P)`:

`λ_b(z) = λ_b(w)`  whenever `z, w ∈ Z(kH)` agree on `C_G(P)`.

## Main results

* `OddOrder.RepresentationTheory.Modular.pi_classSum_subgroup_eq_zero_of_notMem_centralizer`
* `OddOrder.RepresentationTheory.Modular.blockCharacter_eq_of_coeff_eq_on_centralizer`
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra OddOrder.MatrixModule OddOrder.GroupAlgebra
open OddOrder.GroupTheory.CenterClassSum

variable {k G : Type*} [Field k] [Group G] [Fintype G]
variable {P H : Subgroup G} [Fintype ↥H] [DecidableEq (ConjClasses ↥H)]
  [Fintype (ConjClasses ↥H)]
variable {ι : Type*} [Finite ι] {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [∀ i, Nonempty (nn i)]
variable {πH : MonoidAlgebra k ↥H →+* ∀ j, Matrix (nn j) (nn j) k}

omit [Fintype G] [Fintype (ConjClasses ↥H)] [Finite ι] in
open scoped Classical in
/-- **`π_H` kills the class sum of an `H`-class disjoint from `C_G(P)`.**

This is Navarro (4.7) (`OddOrder.GroupAlgebra.pi_classSum_eq_zero_of_notMem_centralizer`) read
inside `H`: `P.subgroupOf H` is a normal `p`-subgroup of `H` (this is where `P ≤ H ≤ N_G(P)` is
used), and an element of `C_H(P.subgroupOf H)` centralises `P` in `G`, so the hypothesis stated
with `C_G(P)` is the one (4.7) wants. -/
theorem pi_classSum_subgroup_eq_zero_of_notMem_centralizer {p : ℕ} [Fact p.Prime] [CharP k p]
    (hπ : Function.Surjective πH)
    (hlin : ∀ (c : k) (a : MonoidAlgebra k ↥H), πH (c • a) = c • πH a)
    (hP : IsPGroup p ↥P) (hPH : P ≤ H) (hHN : H ≤ Subgroup.normalizer (P : Set G))
    {L : ConjClasses ↥H}
    (hL : ∀ h : ↥H, ConjClasses.mk h = L → (h : G) ∉ Subgroup.centralizer (P : Set G)) :
    πH (classSum (k := k) L) = 0 := by
  classical
  set Q : Subgroup ↥H := P.subgroupOf H with hQ
  have hmemQ : ∀ y : ↥H, y ∈ Q ↔ (y : G) ∈ P := fun _ => Iff.rfl
  have hQnormal : Q.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hmemQ] at hn ⊢
    have hcoe : ((g * n * g⁻¹ : ↥H) : G) = (g : G) * (n : G) * (g : G)⁻¹ := by push_cast; rfl
    rw [hcoe]
    exact (Subgroup.mem_normalizer_iff.mp (hHN g.2) (n : G)).mp hn
  have hQp : IsPGroup p ↥Q := hP.comap_of_injective H.subtype Subtype.val_injective
  refine OddOrder.GroupAlgebra.pi_classSum_eq_zero_of_notMem_centralizer πH hπ hlin hQp
    fun x hx hmem => hL x hx ?_
  -- an element of `C_H(P.subgroupOf H)` centralises `P` in `G`
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzH : z ∈ H := hPH hz
  have hzQ : (⟨z, hzH⟩ : ↥H) ∈ Q := hz
  exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hmem) (⟨z, hzH⟩ : ↥H) hzQ)

omit [Fintype G] [Finite ι] in
-- The class-sum expansion of the centre needs the finiteness and decidability of `cl(H)`, which
-- the statement itself does not mention.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
/-- **A block character of `H` is determined by the coefficients on `C_G(P)`.**

The difference of two central elements agreeing on `C_G(P)` expands over the `H`-classes, and in
that expansion every class meeting `C_G(P)` has coefficient `0` (central coefficients are
class-constant) while every class missing it has `π_H`-image `0`. -/
theorem blockCharacter_eq_of_coeff_eq_on_centralizer {p : ℕ} [Fact p.Prime] [CharP k p]
    (hπ : Function.Surjective πH)
    (hlin : ∀ (c : k) (a : MonoidAlgebra k ↥H), πH (c • a) = c • πH a)
    (hP : IsPGroup p ↥P) (hPH : P ≤ H) (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (b : Block πH hπ hlin) {z w : Subalgebra.center k (MonoidAlgebra k ↥H)}
    (hzw : ∀ h : ↥H, (h : G) ∈ Subgroup.centralizer (P : Set G) →
      (z : MonoidAlgebra k ↥H).coeff h = (w : MonoidAlgebra k ↥H).coeff h) :
    blockCharacter πH hπ hlin b z = blockCharacter πH hπ hlin b w := by
  classical
  have hd : blockCharacterPi πH hπ hlin (z - w) = 0 := by
    refine (blockCharacterPi_eq_zero_iff πH hπ hlin).mpr ?_
    set d : MonoidAlgebra k ↥H := (z : MonoidAlgebra k ↥H) - (w : MonoidAlgebra k ↥H) with hdef
    have hdc : d ∈ Subalgebra.center k (MonoidAlgebra k ↥H) := Subalgebra.sub_mem _ z.2 w.2
    have hzero : ∀ h : ↥H, (h : G) ∈ Subgroup.centralizer (P : Set G) → d.coeff h = 0 := by
      intro h hh
      have hsub : d.coeff h
          = (z : MonoidAlgebra k ↥H).coeff h - (w : MonoidAlgebra k ↥H).coeff h := rfl
      rw [hsub, hzw h hh, sub_self]
    change πH ((z - w : Subalgebra.center k (MonoidAlgebra k ↥H)) : MonoidAlgebra k ↥H) = 0
    rw [show ((z - w : Subalgebra.center k (MonoidAlgebra k ↥H)) : MonoidAlgebra k ↥H) = d from rfl,
      center_eq_sum_classSum hdc, map_sum]
    refine Finset.sum_eq_zero fun L _ => ?_
    by_cases hmeet : ∃ h : ↥H, ConjClasses.mk h = L ∧
        (h : G) ∈ Subgroup.centralizer (P : Set G)
    · obtain ⟨h, hhL, hhC⟩ := hmeet
      have hout : d.coeff L.out = 0 := by
        rw [coeff_center_of_mk_eq hdc (a := L.out) (b := h)
          (by rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq, hhL]), hzero h hhC]
      rw [hout, zero_smul, map_zero]
    · push Not at hmeet
      rw [hlin, pi_classSum_subgroup_eq_zero_of_notMem_centralizer hπ hlin hP hPH hHN
        (fun h hh => hmeet h hh), smul_zero]
  have := congrFun hd b
  rw [blockCharacterPi_apply, map_sub, Pi.zero_apply, sub_eq_zero] at this
  exact this

end OddOrder.RepresentationTheory.Modular
