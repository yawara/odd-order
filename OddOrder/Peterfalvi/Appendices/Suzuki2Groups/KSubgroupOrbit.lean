/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.FreeActionOrbitCount
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03

/-!
# Peterfalvi Appendix III: the free orbit of K-subgroups

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. I §3, Lemma 5, p. 107, using Appendix III.

In the proof of Lemma 5, an odd-order group `W` acts on the `q + 1`
`K`-subgroups of order `q²` in a Suzuki `2`-group.  Each such subgroup has a
distinguished `q`-element square fiber, which is a coset of `Q₀`.  If a
nonidentity `w` fixed the subgroup, then that coset would be fixed by `⟨w⟩`.
Coprime fixed-point lifting supplies an actual `w`-fixed representative in the
coset, contradicting `C_Q(w) = Q₀`.

The theorem below isolates exactly this argument.  Merely knowing that the
fiber has `2`-power cardinality would not suffice for an arbitrary odd-order
permutation; the invariant normal coset is the essential group-theoretic
input.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.Isaacs.Ch03

universe uA uP uB

section KSubgroupOrbit

variable {A : Type uA} {P : Type uP} {B : Type uB}
  [Group A] [Finite A] [Group P] [Finite P] [Finite B]
  [MulAction A B]

omit [Finite B] in
/-- The fixed-coset obstruction used in Peterfalvi Part II, Ch. I §3,
Lemma 5.

The points `b : B` are represented by nontrivial cosets `representative b * N`
in `P / N`, equivariantly for an odd-order operator group `A`.  The subgroup
`N` has `2`-power order.  If every fixed point in `P` of a nonidentity operator
lies in `N`, no such operator can fix a point of `B`.

In the source application, `P = Q`, `N = Q₀`, `B` is the family of
`K`-subgroups of order `q²`, and `representative b * N` is the square fiber
inside `b`. -/
theorem no_nontrivial_fixed_of_equivariant_cosetRepresentatives
    (phi : A →* MulAut P) (N : Subgroup P) [N.Normal]
    (hN : IsAInvariant phi N) (representative : B → P)
    (hodd : Odd (Nat.card A)) (n : ℕ) (hcardN : Nat.card N = 2 ^ n)
    (hrepresentative : ∀ b : B, representative b ∉ N)
    (hequivariant : ∀ (a : A) (b : B),
      ∃ z ∈ N, phi a (representative b) = representative (a • b) * z)
    (hfixed : ∀ (a : A), a ≠ 1 → ∀ x : P, phi a x = x → x ∈ N) :
    ∀ (a : A), a ≠ 1 → ∀ b : B, a • b ≠ b := by
  intro a ha b hab
  let C : Subgroup A := Subgroup.zpowers a
  let psi : C →* MulAut P := phi.comp C.subtype
  have hCodd : Odd (Nat.card C) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card C)
  have hcop : Nat.Coprime (Nat.card C) (Nat.card N) := by
    rw [hcardN]
    exact (Nat.coprime_two_right.mpr hCodd).pow_right n
  have hNpsi : IsAInvariant psi N := fun c => hN c
  have hCfix : ∀ c : C, (c : A) • b = b := by
    intro c
    have ha_stabilizer : a ∈ MulAction.stabilizer A b := by
      rw [MulAction.mem_stabilizer_iff]
      exact hab
    have hC_stabilizer : C ≤ MulAction.stabilizer A b := by
      rw [show C = Subgroup.zpowers a from rfl, Subgroup.zpowers_le]
      exact ha_stabilizer
    rw [← MulAction.mem_stabilizer_iff]
    exact hC_stabilizer c.2
  have hcoset : ∀ c : C, ∃ z ∈ N,
      psi c (representative b) = representative b * z := by
    intro c
    obtain ⟨z, hzN, hz⟩ := hequivariant c b
    refine ⟨z, hzN, ?_⟩
    simpa only [psi, MonoidHom.comp_apply, Subgroup.coe_subtype, hCfix c] using hz
  haveI : IsSolvable C :=
    isSolvable_of_comm fun c d => mul_comm' c d
  obtain ⟨x, hxfix, z, hzN, hx⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal
      (φ := psi) hcop (Or.inl (inferInstance : IsSolvable C)) hNpsi hcoset
  let aC : C := ⟨a, Subgroup.mem_zpowers a⟩
  have hfixa : phi a x = x := by
    simpa only [psi, aC, MonoidHom.comp_apply, Subgroup.coe_subtype] using hxfix aC
  have hxN : x ∈ N := hfixed a ha x hfixa
  apply hrepresentative b
  have hx' : representative b = x * z⁻¹ := by
    rw [hx]
    group
  rw [hx']
  exact N.mul_mem hxN (N.inv_mem hzN)

/-- Under the fixed-coset hypotheses of Lemma 5, the odd-order operator group
acts freely and hence its order divides the number of `K`-subgroups. -/
theorem card_dvd_of_equivariant_cosetRepresentatives
    (phi : A →* MulAut P) (N : Subgroup P) [N.Normal]
    (hN : IsAInvariant phi N) (representative : B → P)
    (hodd : Odd (Nat.card A)) (n : ℕ) (hcardN : Nat.card N = 2 ^ n)
    (hrepresentative : ∀ b : B, representative b ∉ N)
    (hequivariant : ∀ (a : A) (b : B),
      ∃ z ∈ N, phi a (representative b) = representative (a • b) * z)
    (hfixed : ∀ (a : A), a ≠ 1 → ∀ x : P, phi a x = x → x ∈ N) :
    Nat.card A ∣ Nat.card B := by
  apply OddOrder.RepresentationTheory.card_dvd_of_no_nontrivial_fixed
  exact no_nontrivial_fixed_of_equivariant_cosetRepresentatives
    phi N hN representative hodd n hcardN hrepresentative hequivariant hfixed

end KSubgroupOrbit

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
