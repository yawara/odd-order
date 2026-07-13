/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7B2_NormalJ_PComplement

/-!
# Isaacs FGT Ch.7 — §7C Thompson normal p-complement (pp. 215–219)

This leaf contains the quotient identifications and the minimum-counterexample
assembly for Thompson's normal `p`-complement theorem (Isaacs Theorem 7.1).
-/

namespace OddOrder.Isaacs.Ch07

variable {G : Type*} [Group G]

section QuotientCenter

/-- **Isaacs Theorem 7.1, Step 3 (center identification).**

If `N ⊴ G` is a normal `p′`-subgroup and `P` is a `p`-subgroup, then the ambient
image of `Z(P)` is carried to the ambient image of `Z(P̄)` under `G → G/N`.
The quotient map is injective on `P` because `P ∩ N = 1`; this is the center
analogue of `thompsonJ_map_of_coprime_kernel`. -/
theorem center_map_subtype_map_of_coprime_kernel
    [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_pgroup : IsPGroup p P) :
    (Subgroup.center ↥(P.map (QuotientGroup.mk' N))).map
        (P.map (QuotientGroup.mk' N)).subtype =
      ((Subgroup.center ↥P).map P.subtype).map (QuotientGroup.mk' N) := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let qP : ↥P →* G ⧸ N := q.comp P.subtype
  obtain ⟨k, hP_card⟩ : ∃ k, Nat.card ↥P = p ^ k := IsPGroup.iff_card.mp hP_pgroup
  have hp_prime : p.Prime := Fact.out
  have h_coprime_PN : Nat.Coprime (Nat.card ↥P) (Nat.card ↥N) := by
    rw [hP_card]
    exact Nat.Coprime.pow_left _ (hp_prime.coprime_iff_not_dvd.mpr hp_coprime)
  have hP_inf_N : P ⊓ N = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard h_coprime_PN).eq_bot
  have hqP_inj : Function.Injective qP := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx_N : (x : G) ∈ N := by
      have hx' : (x : G) ∈ (QuotientGroup.mk' N).ker := hx
      rwa [QuotientGroup.ker_mk'] at hx'
    have hx_inf : (x : G) ∈ P ⊓ N := ⟨x.property, hx_N⟩
    rw [hP_inf_N, Subgroup.mem_bot] at hx_inf
    exact Subtype.ext hx_inf
  ext x
  constructor
  · intro hx
    have hx_center := Subgroup.mem_center_map_subtype_iff.mp hx
    obtain ⟨z, hzP, hzx⟩ := hx_center.1
    refine ⟨z, Subgroup.mem_center_map_subtype_iff.mpr ⟨hzP, ?_⟩, hzx⟩
    intro w hw
    have hcomm_q := hx_center.2 (q w) ⟨w, hw, rfl⟩
    rw [← hzx] at hcomm_q
    have hsub :
        qP (⟨w, hw⟩ * ⟨z, hzP⟩) = qP (⟨z, hzP⟩ * ⟨w, hw⟩) := by
      change q (w * z) = q (z * w)
      simpa only [map_mul] using hcomm_q
    exact congrArg Subtype.val (hqP_inj hsub)
  · rintro ⟨z, hz, rfl⟩
    have hz_center := Subgroup.mem_center_map_subtype_iff.mp hz
    apply Subgroup.mem_center_map_subtype_iff.mpr
    refine ⟨⟨z, hz_center.1, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    simpa only [map_mul] using congrArg q (hz_center.2 w hw)

end QuotientCenter

end OddOrder.Isaacs.Ch07
