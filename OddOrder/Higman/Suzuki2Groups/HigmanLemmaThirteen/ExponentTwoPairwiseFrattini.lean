/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoCommutingFactors

/-!
# Higman's Lemma 13: Frattini subgroup of a pairwise join

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

For two exponent-two type-A factors, the Frattini subgroup of their join is
the ambient Frattini subgroup. The forward inclusion uses the finite
2-group identity `Φ = ℧¹`: every square in the join is an ambient square and
hence lies in `Φ(P)`. Conversely, every nonidentity element of `Φ(P)` is an
ambient involution and actor transitivity supplies a square root inside either
type-A factor.

This equality is the bridge which lets the prescribed-factor coordinate
version of Higman's Lemma 12 retain the actual two factors of Lemma 13.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

section /- Higman Lemma 13 (p. 93) -/

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03

universe uP uF

variable {P : Type uP} [Group P]

/-- **Higman Lemma 13 (p. 93), pairwise Frattini equality.**

Inside the join of two exponent-two factors, the ambient Frattini subgroup
is exactly the intrinsic Frattini subgroup. -/
theorem frattini_sup_eq_ambientFrattini_subgroupOf
    [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hxi : IsXiActor Y)
    (htwo : ∀ z : frattini P, z ^ 2 = 1)
    {R S : Subgroup P}
    (hRinv : IsAInvariant Y.subtype R)
    (hPhiR : frattini P < R)
    (dataR : XiLengthTwoTypeAData.{uP, uF} R) :
    frattini ↥(R ⊔ S) =
      (frattini P).subgroupOf (R ⊔ S) := by
  let J : Subgroup P := R ⊔ S
  have hPhiJ : frattini P ≤ J :=
    hPhiR.le.trans (le_sup_left : R ≤ R ⊔ S)
  have hFrattiniAgemo :
      frattini J = Agemo J 2 1 := by
    have hstandard :=
      OddOrder.BG.Ch1.S01.commutator_sup_pow_closure_eq_frattini
        (hP.to_subgroup J)
    rw [← hstandard]
    have hsquares :
        Subgroup.closure (Set.range (fun x : J => x ^ 2)) =
          Agemo J 2 1 := by
      rw [Agemo]
      congr 1
      ext x
      simp only [Nat.pow_one]
      constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, rfl⟩
    rw [hsquares, sup_eq_right.mpr (commutator_le_agemo_two_one J)]
  apply Subgroup.map_injective J.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hPhiJ, hFrattiniAgemo]
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, Agemo, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    change (x : P) ^ (2 ^ 1) ∈ frattini P
    simpa using OddOrder.GroupTheory.IsPGroup.pow_mem_frattini hP (x : P)
  · intro z hz
    by_cases hzOne : z = 1
    · rw [hzOne]
      exact (Agemo J 2 1).map J.subtype |>.one_mem
    have hzSq : z ^ 2 = 1 := by
      simpa using congrArg Subtype.val (htwo ⟨z, hz⟩)
    have hzInv : z ∈ involutions P := ⟨hzSq, hzOne⟩
    obtain ⟨x, hx⟩ :=
      XiLengthTwoTypeAData.exists_sq_eq_of_mem_ambient_involutions
        hxi hRinv dataR hzInv
    let xJ : J :=
      ⟨x, (le_sup_left : R ≤ R ⊔ S) x.property⟩
    apply Subgroup.mem_map.mpr
    refine ⟨xJ ^ (2 ^ 1), Agemo.mem_of_eq_pow xJ, ?_⟩
    simpa [xJ, J] using hx

end

end OddOrder.Higman.Suzuki2Groups
