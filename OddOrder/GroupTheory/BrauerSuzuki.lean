import Mathlib.GroupTheory.Transfer
import OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

/-!
# Brauer–Suzuki theorem — statement layer and the cyclic case

**Brauer–Suzuki theorem** (Gorenstein, *Finite Groups*, Ch. 12, Theorem 1.1; cited by
Peterfalvi, *Character Theory for the Odd Order Theorem*, Appendix C, Proposition 1):
if a Sylow `2`-subgroup `S` of a finite group `G` is cyclic or generalized quaternion
and `u` is an involution of `G`, then `G = O_{2'}(G) · C_G(u)` — equivalently
`O_{2'}(G) ⊔ C_G(u) = ⊤`, since `O_{2'}(G)` is normal.

This file provides the **cyclic case** (`brauerSuzuki_of_isCyclic_sylowTwo`), which is
elementary: a cyclic Sylow `2`-subgroup is a Sylow subgroup for the *smallest* prime
divisor of `|G|` (the group has even order because it contains an involution), so
Burnside's transfer theorem (`IsCyclic.isComplement'`) yields a normal `2`-complement
`K`.  Any Sylow `2`-subgroup `S'` containing `u` is abelian, so `S' ≤ C_G(u)`, and
`G = K·S'` with `K ≤ O_{2'}(G)` gives the conclusion.

The generalized quaternion case (Gorenstein Ch. 12, via exceptional character theory
for `|S| ≥ 16`; the `Q₈` case needs a separate route) is issue 9318's main campaign
and lives in sibling leaves.

The odd core `O_{2'}(G)` is `oPiCore {p | p ≠ 2} G`
(`OddOrder.Isaacs.Ch03.oPiCore`, the largest normal `π`-subgroup).
-/

namespace OddOrder.GroupTheory

open Subgroup OddOrder.Isaacs.Ch03

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

/-- **Brauer–Suzuki theorem, cyclic Sylow `2`-subgroup case**: if some (equivalently,
every) Sylow `2`-subgroup of the finite group `G` is cyclic and `u ∈ G` is an
involution, then `G = O_{2'}(G) · C_G(u)`, stated as
`oPiCore {p | p ≠ 2} G ⊔ C_G(u) = ⊤` (the product form follows from normality of the
odd core).

Burnside: `2` is the smallest prime divisor of `|G|` (even since `orderOf u = 2`), so
the cyclic Sylow `2`-subgroup has a normal complement `K` of odd order
(`IsCyclic.isComplement'`); then `K ≤ O_{2'}(G)`, and any Sylow `2`-subgroup `S'`
containing `u` is cyclic hence abelian, so `S' ≤ C_G(u)` and
`⊤ = K ⊔ S' ≤ O_{2'}(G) ⊔ C_G(u)`. -/
theorem brauerSuzuki_of_isCyclic_sylowTwo (S : Sylow 2 G)
    (hcyc : IsCyclic (S : Subgroup G)) (u : G) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    oPiCore {p | p ≠ 2} G ⊔ centralizer {u} = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `|G|` is even with smallest prime factor `2`.
  have hord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have h2dvd : 2 ∣ Nat.card G := hord ▸ orderOf_dvd_natCard u
  have hG1 : Nat.card G ≠ 1 := by
    intro h; rw [h] at h2dvd; norm_num at h2dvd
  have hminFac : (Nat.card G).minFac = 2 :=
    le_antisymm (Nat.minFac_le_of_dvd le_rfl h2dvd) (Nat.minFac_prime hG1).two_le
  -- Burnside's normal `2`-complement `K` for the cyclic Sylow `S`.
  have hcompl := IsCyclic.isComplement' hminFac hcyc
  set K := (MonoidHom.transferSylow S (hcyc.normalizer_le_centralizer hminFac)).ker with hK
  -- `K` has odd order (its cardinality is the index of the Sylow `2`-subgroup).
  have hcardK : Nat.card K = (S : Subgroup G).index := hcompl.index_eq_card.symm
  have hKodd : ¬(2 ∣ Nat.card K) := by rw [hcardK]; exact S.not_dvd_index
  have hKpi : Subgroup.IsPiGroup {p | p ≠ 2} K := by
    intro p hp
    rintro rfl
    exact hKodd (Nat.dvd_of_mem_primeFactors hp)
  have hKle : K ≤ oPiCore {p | p ≠ 2} G := hKpi.le_oPiCore
  -- a Sylow `2`-subgroup `S'` containing `u`.
  have hu_pgroup : IsPGroup 2 (Subgroup.zpowers u) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers, hord, pow_one]
  obtain ⟨S', hS'⟩ := hu_pgroup.exists_le_sylow
  have huS' : u ∈ (S' : Subgroup G) := hS' (Subgroup.mem_zpowers u)
  -- `S'` is cyclic: it is conjugate to `S`.
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
  have hcoe : MulAut.conj g • (S : Subgroup G) = (S' : Subgroup G) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  haveI hS'cyc : IsCyclic (S' : Subgroup G) := by
    rw [← hcoe]
    exact isCyclic_of_surjective
      (Subgroup.equivSMul (MulAut.conj g) (S : Subgroup G)).toMonoidHom
      (Subgroup.equivSMul _ _).surjective
  -- `S'` is abelian, so it centralizes `u`.
  have hS'le : (S' : Subgroup G) ≤ centralizer {u} := by
    intro s hs
    rw [mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    letI := hS'cyc.commGroup
    have hcomm := mul_comm (⟨u, huS'⟩ : (S' : Subgroup G)) ⟨s, hs⟩
    simpa using congrArg Subtype.val hcomm
  -- `G = K ⊔ S'` (coprime cardinalities multiply to `|G|`).
  have hcardS' : Nat.card (S' : Subgroup G) = Nat.card (S : Subgroup G) := by
    rw [← hcoe]
    exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) (S : Subgroup G)).toEquiv).symm
  have hcardmul : Nat.card K * Nat.card (S' : Subgroup G) = Nat.card G := by
    rw [hcardS']; exact hcompl.card_mul
  have hcop : Nat.Coprime (Nat.card K) (Nat.card (S' : Subgroup G)) := by
    obtain ⟨m, hm⟩ := S'.isPGroup'.exists_card_eq
    rw [hm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hKodd |>.symm.pow_right m
  have hsup : K ⊔ (S' : Subgroup G) = ⊤ :=
    (Subgroup.isComplement'_of_coprime hcardmul hcop).sup_eq_top
  -- assemble.
  rw [eq_top_iff, ← hsup]
  exact sup_le (hKle.trans le_sup_left) (hS'le.trans le_sup_right)

end OddOrder.GroupTheory
