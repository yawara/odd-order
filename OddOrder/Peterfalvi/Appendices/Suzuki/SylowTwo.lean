/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.KCyclic
import OddOrder.GroupTheory.SpecificGroups.Suzuki2Group.Basic

/-!
# Peterfalvi Part II, Ch. I §2 Corollary: Sylow 2-subgroups of Q

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §2, p. 103.

For a Sylow `2`-subgroup `S` of `Q`, nilpotence of `Q` makes `S`
characteristic.  The cyclic subgroup `K` therefore acts on `S` by
conjugation.  Section 1 Proposition 3 identifies the nonidentity
involutions of `S` with `H ∩ I` and proves that this action is regular.
Thus `S` is either commutative or a Suzuki `2`-group in the honest sense
of Appendix III, Definition 1.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open scoped IsMulCommutative

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- Conjugation by the constructed `K` on `Q`. -/
def conjQByK : ↥hyp.K →* MulAut ↥hyp.Q where
  toFun k :=
    { toFun := fun x => ⟨(k : G) * x * (k : G)⁻¹,
        hyp.Q_normal_in_H k (hyp.D_le_H (hyp.K_le_D k.2)) x x.2⟩
      invFun := fun x => ⟨(k : G)⁻¹ * x * (k : G), by
        simpa using hyp.Q_normal_in_H (k : G)⁻¹
          (inv_mem (hyp.D_le_H (hyp.K_le_D k.2))) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by
        change (k : G) * ((x : G) * (y : G)) * (k : G)⁻¹ =
          ((k : G) * x * (k : G)⁻¹) * ((k : G) * y * (k : G)⁻¹)
        group) }
  map_one' := by
    ext x
    change ((1 : ↥hyp.K) : G) * (x : G) * ((1 : ↥hyp.K) : G)⁻¹ = (x : G)
    simp
  map_mul' k l := by
    ext x
    change (((k : G) * (l : G)) * (x : G) * (((k : G) * (l : G))⁻¹)) =
      (k : G) * ((l : G) * (x : G) * (l : G)⁻¹) * (k : G)⁻¹
    group

@[simp] lemma conjQByK_apply_val (k : ↥hyp.K) (x : ↥hyp.Q) :
    ((hyp.conjQByK k x : ↥hyp.Q) : G) = (k : G) * (x : G) * (k : G)⁻¹ := rfl

/-- **Peterfalvi Part II, Ch. I §2, Corollary** (p. 103): every Sylow
`2`-subgroup of `Q` is either commutative or a Suzuki `2`-group. -/
theorem sylowTwo_isMulCommutative_or_isSuzuki2Group (S : Sylow 2 ↥hyp.Q) :
    IsMulCommutative ↥(S : Subgroup ↥hyp.Q) ∨
      OddOrder.GroupTheory.Suzuki2Group.IsSuzuki2Group ↥(S : Subgroup ↥hyp.Q) := by
  letI : Group.IsNilpotent ↥hyp.Q := hyp.isNilpotent_Q
  letI hSnorm : (S : Subgroup ↥hyp.Q).Normal := inferInstance
  letI : (S : Subgroup ↥hyp.Q).Characteristic :=
    Sylow.characteristic_of_normal S hSnorm
  have involution_mem_S {x : ↥hyp.Q} (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
      x ∈ (S : Subgroup ↥hyp.Q) := by
    have hzp : IsPGroup 2 ↥(Subgroup.zpowers x) :=
      IsPGroup.of_card (by
        rw [Nat.card_zpowers, orderOf_eq_prime hx2 hx1, pow_one])
    obtain ⟨T, hle⟩ := hzp.exists_le_sylow
    haveI : Unique (Sylow 2 ↥hyp.Q) := Sylow.unique_of_normal S hSnorm
    have hTS : T = S := Subsingleton.elim _ _
    rw [← hTS]
    exact hle (Subgroup.mem_zpowers x)
  by_cases hcomm : IsMulCommutative ↥(S : Subgroup ↥hyp.Q)
  · exact Or.inl hcomm
  · right
    let hSinv : OddOrder.Isaacs.Ch03.IsAInvariant hyp.conjQByK (S : Subgroup ↥hyp.Q) :=
      OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic hyp.conjQByK
    let φ : ↥hyp.K →* MulAut ↥(S : Subgroup ↥hyp.Q) := hSinv.restrict
    let A : Subgroup (MulAut ↥(S : Subgroup ↥hyp.Q)) := φ.range
    have hφval (l : ↥hyp.K) (z : ↥(S : Subgroup ↥hyp.Q)) :
        (((φ l z : ↥(S : Subgroup ↥hyp.Q)) : ↥hyp.Q) : G) =
          (l : G) * ((z : ↥hyp.Q) : G) * (l : G)⁻¹ := by
      change (((hSinv.restrict l z : ↥(S : Subgroup ↥hyp.Q)) : ↥hyp.Q) : G) = _
      rw [OddOrder.Isaacs.Ch03.IsAInvariant.restrict_apply_val hSinv]
      exact hyp.conjQByK_apply_val l (z : ↥hyp.Q)
    have hAcyc : IsCyclic ↥A := by
      exact isCyclic_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    refine ⟨S.isPGroup', hcomm, ?_, A, hAcyc, ?_⟩
    · obtain ⟨k, hkK, hk1⟩ := hyp.exists_ne_one_mem_KSet
      let sG : G := hyp.distinguishedInvolution
      have hsQmem : sG ∈ hyp.Q := hyp.mem_Q_of_sq_eq_one_of_mem_H
        hyp.distinguishedInvolution_mem_H hyp.distinguishedInvolution_sq
      let sQ : ↥hyp.Q := ⟨sG, hsQmem⟩
      have hsQ2 : sQ ^ 2 = 1 := Subtype.ext hyp.distinguishedInvolution_sq
      have hsQ1 : sQ ≠ 1 := fun h => hyp.distinguishedInvolution_ne_one
        (congrArg Subtype.val h)
      let s : ↥(S : Subgroup ↥hyp.Q) := ⟨sQ, involution_mem_S hsQ2 hsQ1⟩
      let uG : G := k⁻¹ * sG * k
      have hkH : k ∈ hyp.H := hyp.D_le_H hkK.1
      have huH : uG ∈ hyp.H := mul_mem (mul_mem (inv_mem hkH)
        hyp.distinguishedInvolution_mem_H) hkH
      have hu2 : uG ^ 2 = 1 := by
        dsimp [uG, sG]
        rw [sq]
        calc k⁻¹ * hyp.distinguishedInvolution * k *
              (k⁻¹ * hyp.distinguishedInvolution * k) =
              k⁻¹ * (hyp.distinguishedInvolution * hyp.distinguishedInvolution) * k := by group
          _ = 1 := by rw [← sq, hyp.distinguishedInvolution_sq]; group
      have hu1 : uG ≠ 1 := by
        intro hu
        apply hyp.distinguishedInvolution_ne_one
        have := congrArg (fun z : G => k * z * k⁻¹) hu
        simpa [uG, sG, mul_assoc] using this
      let uQ : ↥hyp.Q := ⟨uG, hyp.mem_Q_of_sq_eq_one_of_mem_H huH hu2⟩
      have huQ2 : uQ ^ 2 = 1 := Subtype.ext hu2
      have huQ1 : uQ ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
      let u : ↥(S : Subgroup ↥hyp.Q) := ⟨uQ, involution_mem_S huQ2 huQ1⟩
      refine ⟨s, u, ⟨Subtype.ext hsQ2, ?_⟩, ⟨Subtype.ext huQ2, ?_⟩, ?_⟩
      · exact fun h => hsQ1 (congrArg Subtype.val h)
      · exact fun h => huQ1 (congrArg Subtype.val h)
      · intro hsu
        have hsuG : sG = uG := congrArg (fun z : ↥(S : Subgroup ↥hyp.Q) =>
          (((z : ↥hyp.Q) : G))) hsu
        have hk_eq_one := hyp.injOn_conj_KSet
          hyp.distinguishedInvolution_mem_H hyp.distinguishedInvolution_sq
          hyp.distinguishedInvolution_ne_one hkK hyp.one_mem_KSet (by
            simpa [uG, sG] using hsuG.symm)
        exact hk1 hk_eq_one
    · rintro x ⟨hx2, hx1⟩ y ⟨hy2, hy1⟩
      have hx2Q : (x : ↥hyp.Q) ^ 2 = 1 := congrArg Subtype.val hx2
      have hy2Q : (y : ↥hyp.Q) ^ 2 = 1 := congrArg Subtype.val hy2
      have hx1Q : (x : ↥hyp.Q) ≠ 1 := fun h => hx1 (Subtype.ext h)
      have hy1Q : (y : ↥hyp.Q) ≠ 1 := fun h => hy1 (Subtype.ext h)
      have hx2G : (((x : ↥hyp.Q) : G) ^ 2) = 1 := congrArg Subtype.val hx2Q
      have hy2G : (((y : ↥hyp.Q) : G) ^ 2) = 1 := congrArg Subtype.val hy2Q
      have hx1G : ((x : ↥hyp.Q) : G) ≠ 1 := fun h => hx1Q (Subtype.ext h)
      have hy1G : ((y : ↥hyp.Q) : G) ≠ 1 := fun h => hy1Q (Subtype.ext h)
      have hxH : ((x : ↥hyp.Q) : G) ∈ hyp.H := hyp.Q_le_H (x : ↥hyp.Q).2
      have hyH : ((y : ↥hyp.Q) : G) ∈ hyp.H := hyp.Q_le_H (y : ↥hyp.Q).2
      have himg := hyp.image_conj_KSet_eq_involutions_H hxH hx2G hx1G
      have hymem : ((y : ↥hyp.Q) : G) ∈
          {z : G | z ^ 2 = 1 ∧ z ≠ 1 ∧ z ∈ hyp.H} := ⟨hy2G, hy1G, hyH⟩
      rw [← himg] at hymem
      obtain ⟨k, hkK, hky⟩ := hymem
      have hkiK : k⁻¹ ∈ hyp.K := by
        change k⁻¹ ∈ (hyp.K : Set G)
        rw [hyp.coe_K]
        exact hyp.inv_mem_KSet hkK
      let j : ↥hyp.K := ⟨k⁻¹, hkiK⟩
      let a : ↥A := ⟨φ j, ⟨j, rfl⟩⟩
      refine ⟨a, ?_, ?_⟩
      · apply Subtype.ext
        apply Subtype.ext
        rw [hφval]
        change k⁻¹ * ((x : ↥hyp.Q) : G) * (k⁻¹)⁻¹ = ((y : ↥hyp.Q) : G)
        rw [inv_inv]
        exact hky
      · intro b hb
        obtain ⟨l, hl⟩ := b.2
        have hlaction : φ l x = y := by
          rw [hl]
          exact hb
        have hlG : (l : G) * ((x : ↥hyp.Q) : G) * (l : G)⁻¹ =
            ((y : ↥hyp.Q) : G) := by
          have hs := congrArg (fun z : ↥(S : Subgroup ↥hyp.Q) =>
            (((z : ↥hyp.Q) : G))) hlaction
          rw [hφval] at hs
          exact hs
        have hjG : (j : G) * ((x : ↥hyp.Q) : G) * (j : G)⁻¹ =
            ((y : ↥hyp.Q) : G) := by
          change k⁻¹ * ((x : ↥hyp.Q) : G) * (k⁻¹)⁻¹ = _
          rw [inv_inv]
          exact hky
        have hliK : (l : G)⁻¹ ∈ hyp.KSet := by
          apply hyp.inv_mem_KSet
          rw [← hyp.coe_K]
          exact l.2
        have hjiK : (j : G)⁻¹ ∈ hyp.KSet := by
          apply hyp.inv_mem_KSet
          rw [← hyp.coe_K]
          exact j.2
        have hinv_eq : (l : G)⁻¹ = (j : G)⁻¹ :=
          hyp.injOn_conj_KSet hxH hx2G hx1G hliK hjiK (by
            simpa only [inv_inv] using hlG.trans hjG.symm)
        have hlj : l = j := Subtype.ext (inv_injective hinv_eq)
        apply Subtype.ext
        change (b : MulAut ↥(S : Subgroup ↥hyp.Q)) = φ j
        rw [← hl, hlj]
end Hypothesis
end OddOrder.Peterfalvi.Appendices.Suzuki
