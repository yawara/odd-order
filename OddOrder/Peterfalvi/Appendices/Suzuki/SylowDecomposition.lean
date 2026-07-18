/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.QStructure
import OddOrder.Isaacs.Ch05_Transfer.NilpotentPComplement
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Peterfalvi Part II, Ch. I §2: the decomposition `Q = S × Q₁`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §2, p. 103.

Immediately after §2 Proposition 1, Peterfalvi writes

`Q = S × Q₁`, where `S` is the Sylow `2`-subgroup of `Q`.

This file constructs `Q₁`; it is not additional structure on `Hypothesis`.
The already-proved nilpotence of `Q` supplies a normal `2`-complement, and
uniqueness makes that complement characteristic. We retain both its internal
form `Q1Subgroup ≤ Q` and its ambient image `Q1 ≤ G`. For every Sylow
`2`-subgroup `S` of `Q`, multiplication gives the exact direct-product
isomorphism `S × Q1Subgroup ≃* Q`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

private theorem exists_normalTwoComplement_Q :
    ∃ N : Subgroup ↥hyp.Q, N.Normal ∧
      ∀ S : Sylow 2 ↥hyp.Q,
        Subgroup.IsComplement' N (S : Subgroup ↥hyp.Q) := by
  letI : Group.IsNilpotent ↥hyp.Q := hyp.isNilpotent_Q
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact OddOrder.Isaacs.Ch05.hasNormalPComplement_of_isNilpotent

/-- Peterfalvi's `Q₁`, first in its intrinsic form as the unique normal
`2`-complement of `Q`. This is chosen from the nilpotence theorem for `Q`;
it is not a free field of the standing hypothesis. -/
noncomputable def Q1Subgroup : Subgroup ↥hyp.Q :=
  Classical.choose (exists_normalTwoComplement_Q hyp)

private theorem Q1Subgroup_spec :
    hyp.Q1Subgroup.Normal ∧
      ∀ S : Sylow 2 ↥hyp.Q,
        Subgroup.IsComplement' hyp.Q1Subgroup (S : Subgroup ↥hyp.Q) :=
  Classical.choose_spec (exists_normalTwoComplement_Q hyp)

instance Q1Subgroup_normal : hyp.Q1Subgroup.Normal :=
  (Q1Subgroup_spec hyp).1

/-- The constructed `Q₁` complements every Sylow `2`-subgroup of `Q`.
The orientation here is the one returned by the normal-complement theorem. -/
theorem Q1Subgroup_isComplement'_sylowTwo (S : Sylow 2 ↥hyp.Q) :
    Subgroup.IsComplement' hyp.Q1Subgroup (S : Subgroup ↥hyp.Q) :=
  (Q1Subgroup_spec hyp).2 S

/-- The source-order complement statement `Q = S Q₁`. -/
theorem sylowTwo_isComplement'_Q1Subgroup (S : Sylow 2 ↥hyp.Q) :
    Subgroup.IsComplement' (S : Subgroup ↥hyp.Q) hyp.Q1Subgroup :=
  (hyp.Q1Subgroup_isComplement'_sylowTwo S).symm

/-- `Q₁` is characteristic in `Q`, by uniqueness of the normal
`2`-complement. -/
instance Q1Subgroup_characteristic : hyp.Q1Subgroup.Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro ψ
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact OddOrder.Isaacs.Ch05.map_mulAut_of_normal_pcomplement
    (hyp.Q1Subgroup_isComplement'_sylowTwo (default : Sylow 2 ↥hyp.Q)) ψ

/-- `Q₁` has odd order, in the exact `2'` form used later in §3
Proposition 1(c). -/
theorem two_not_dvd_card_Q1Subgroup : ¬ 2 ∣ Nat.card hyp.Q1Subgroup := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact OddOrder.Isaacs.Ch05.not_dvd_card_of_isComplement'_sylow
    (default : Sylow 2 ↥hyp.Q)
    (hyp.Q1Subgroup_isComplement'_sylowTwo (default : Sylow 2 ↥hyp.Q))

/-- The ambient subgroup denoted `Q₁` in Peterfalvi. -/
noncomputable def Q1 : Subgroup G :=
  hyp.Q1Subgroup.map hyp.Q.subtype

lemma Q1_le_Q : hyp.Q1 ≤ hyp.Q := by
  rintro x ⟨q, hq, rfl⟩
  exact q.2

/-- Mapping `Q₁ ≤ Q` into `G` does not change its order. -/
lemma card_Q1 : Nat.card hyp.Q1 = Nat.card hyp.Q1Subgroup :=
  (Nat.card_congr
    (Subgroup.equivMapOfInjective hyp.Q1Subgroup hyp.Q.subtype
      hyp.Q.subtype_injective).toEquiv).symm

/-- The two factors have trivial intersection. -/
theorem sylowTwo_inf_Q1Subgroup_eq_bot (S : Sylow 2 ↥hyp.Q) :
    (S : Subgroup ↥hyp.Q) ⊓ hyp.Q1Subgroup = ⊥ :=
  disjoint_iff.mp (hyp.sylowTwo_isComplement'_Q1Subgroup S).disjoint

/-- The two factors generate all of `Q`. -/
theorem sylowTwo_sup_Q1Subgroup_eq_top (S : Sylow 2 ↥hyp.Q) :
    (S : Subgroup ↥hyp.Q) ⊔ hyp.Q1Subgroup = ⊤ :=
  (hyp.sylowTwo_isComplement'_Q1Subgroup S).sup_eq_top

/-- Elements of the two normal factors commute. -/
theorem sylowTwo_commute_Q1Subgroup (S : Sylow 2 ↥hyp.Q)
    (s : ↥(S : Subgroup ↥hyp.Q)) (q₁ : ↥hyp.Q1Subgroup) :
    Commute (s : ↥hyp.Q) (q₁ : ↥hyp.Q) := by
  letI : Group.IsNilpotent ↥hyp.Q := hyp.isNilpotent_Q
  have hSnormal : (S : Subgroup ↥hyp.Q).Normal := inferInstance
  exact Subgroup.commute_of_normal_of_disjoint
    (S : Subgroup ↥hyp.Q) hyp.Q1Subgroup hSnormal inferInstance
    (hyp.sylowTwo_isComplement'_Q1Subgroup S).disjoint
    s q₁ s.2 q₁.2

/-- The exact internal direct-product form of Peterfalvi's notation
`Q = S × Q₁`: multiplication is a group isomorphism. -/
noncomputable def sylowTwoProdQ1MulEquiv (S : Sylow 2 ↥hyp.Q) :
    ↥(S : Subgroup ↥hyp.Q) × ↥hyp.Q1Subgroup ≃* ↥hyp.Q := by
  let comm : ∀ (s : ↥(S : Subgroup ↥hyp.Q)) (q₁ : ↥hyp.Q1Subgroup),
      Commute ((S : Subgroup ↥hyp.Q).subtype s) (hyp.Q1Subgroup.subtype q₁) :=
    fun s q₁ => hyp.sylowTwo_commute_Q1Subgroup S s q₁
  let f : ↥(S : Subgroup ↥hyp.Q) × ↥hyp.Q1Subgroup →* ↥hyp.Q :=
    (S : Subgroup ↥hyp.Q).subtype.noncommCoprod hyp.Q1Subgroup.subtype comm
  apply MulEquiv.ofBijective f
  constructor
  · dsimp only [f]
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨(S : Subgroup ↥hyp.Q).subtype_injective,
      hyp.Q1Subgroup.subtype_injective, ?_⟩
    simpa only [Subgroup.range_subtype] using
      (hyp.sylowTwo_isComplement'_Q1Subgroup S).disjoint
  · dsimp only [f]
    rw [← MonoidHom.range_eq_top, MonoidHom.noncommCoprod_range]
    simpa only [Subgroup.range_subtype] using
      hyp.sylowTwo_sup_Q1Subgroup_eq_top S

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
