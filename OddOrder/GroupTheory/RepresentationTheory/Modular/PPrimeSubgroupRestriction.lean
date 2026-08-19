/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockIntegralCombination
import OddOrder.GroupTheory.RepresentationTheory.Modular.PPrimeOrderBrauerOrdinary
import OddOrder.GroupTheory.RepresentationTheory.Modular.PPrimeOrderSemisimple

/-!
# Restricting an irreducible Brauer character to a `p'`-subgroup

`brauerCharacter_mem_virtualCharacters_of_not_dvd_card` says that every Brauer character of a
`p'`-group is a virtual character — but it says it *at* that group, so using it for a subgroup
`Q ≤ G` needs a splitting datum for `Q`, which the ambient datum for `G` does not provide.  This
file constructs one and draws the conclusion Navarro (3.16) consumes:

`(φ_μ)|_Q ∈ ch(Q)` for every `p'`-subgroup `Q ≤ G`.

Two points make the construction short.

* Over an algebraically closed field the group algebra of a `p'`-group is *already* semisimple
  (Maschke), so Artin–Wedderburn applies to `k[Q]` itself — no Jacobson quotient is involved and
  the splitting is an **algebra** isomorphism.  That is what supplies the linearity hypothesis
  `hlin`, which `exists_surjective_blocks_card_eq` (built through `k[G] ⧸ J(k[G])`) drops.  The
  same argument over `K` gives the ordinary splitting `e_Q`.
* The roots of unity are inherited rather than reconstructed: `|Q|_{p'} ∣ |G|_{p'}`, so
  `ω ^ (|G|_{p'} / |Q|_{p'})` is a primitive `|Q|_{p'}`-th root of unity, and likewise on the
  residue field.

The restriction itself needs no lemma: `brauerCharacter n (ρ.comp Q.subtype) x` and
`brauerCharacter n ρ ↑x` are the same sum of eigenvalue multiplicities, because `ρ.comp Q.subtype`
sends `x` to the very operator `ρ ↑x`.  Only the *exponent* has to be tracked, and
`brauerCharacter_mem_virtualCharacters_of_not_dvd_card` was stated at an arbitrary admissible
exponent precisely for this.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_algEquiv_pi_matrix_monoidAlgebra` — Wedderburn
  for a semisimple group algebra over an algebraically closed field
* `OddOrder.RepresentationTheory.Modular.restrict_irreducibleBrauerCharacter_mem_virtualCharacters`

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (2.12), (3.16).
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.RepresentationTheory

/-! ### Wedderburn splitting of a semisimple group algebra -/

section Splitting

variable (k : Type*) (Q : Type*) [Field k] [IsAlgClosed k] [Group Q] [Finite Q]

/-- **Artin–Wedderburn for a semisimple group algebra** over an algebraically closed field:
`k[Q] ≅ ∏_j M_{d_j}(k)` as `k`-algebras.

Unlike `exists_surjective_blocks_card_eq`, which has to pass through `k[G] ⧸ J(k[G])` and comes
out as a bare ring homomorphism, the map here is an algebra isomorphism of `k[Q]` itself — so it
carries the `k`-linearity that the Brauer-character API asks for. -/
theorem exists_algEquiv_pi_matrix_monoidAlgebra [IsSemisimpleRing (MonoidAlgebra k Q)] :
    ∃ (n : ℕ) (d : Fin n → ℕ) (_ : ∀ i, NeZero (d i)),
      Nonempty (MonoidAlgebra k Q ≃ₐ[k] ∀ i, Matrix (Fin (d i)) (Fin (d i)) k) := by
  have : Fintype Q := Fintype.ofFinite Q
  have : FiniteDimensional k (MonoidAlgebra k Q) :=
    Module.Finite.of_basis (MonoidAlgebra.basis Q k)
  obtain ⟨n, d, hd, he⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k (MonoidAlgebra k Q)
  exact ⟨n, d, hd, he⟩

variable {k Q}

/-- The splitting of `k[Q]` for a `p'`-group `Q`, in the shape the modular API consumes: a
surjective ring map with kernel `J(k[Q]) = ⊥` that is `k`-linear. -/
theorem exists_splitting_of_not_dvd_card {p : ℕ} (hp : p.Prime) (hk : (p : k) = 0)
    (hQ : ¬ p ∣ Nat.card Q) :
    ∃ (n : ℕ) (d : Fin n → ℕ) (_ : ∀ i, NeZero (d i))
      (π : MonoidAlgebra k Q →+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) k),
      Function.Surjective π ∧
        (∀ (c : k) (a : MonoidAlgebra k Q), π (c • a) = c • π a) ∧
        RingHom.ker π = Ring.jacobson (MonoidAlgebra k Q) := by
  have := isSemisimpleRing_monoidAlgebra_of_not_dvd_card hp hk hQ
  obtain ⟨n, d, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_monoidAlgebra k Q
  refine ⟨n, d, hd, e.toRingEquiv.toRingHom, e.surjective,
    fun c a => e.toLinearEquiv.map_smul c a, ?_⟩
  rw [jacobson_monoidAlgebra_eq_bot hp hk hQ]
  exact (RingHom.injective_iff_ker_eq_bot _).mp e.injective

end Splitting

/-! ### The restriction -/

section Restriction

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]

omit [Finite G] in
/-- The `p'`-part of `|Q|` divides that of `|G|` for a subgroup `Q ≤ G`, by Lagrange. -/
theorem pRegularExponent_subgroup_dvd (Q : Subgroup G) :
    pRegularExponent p ↥Q ∣ pRegularExponent p G :=
  Nat.ordCompl_dvd_ordCompl_of_dvd (Subgroup.card_subgroup_dvd_card Q) p

omit [Finite G] in
/-- `|G|` invertible in `K` makes `|Q|` nonzero — hence invertible — for every subgroup
`Q ≤ G`. -/
theorem natCard_subgroup_ne_zero [Invertible (Nat.card G : K)] (Q : Subgroup G) :
    (Nat.card ↥Q : K) ≠ 0 := by
  obtain ⟨c, hc⟩ := Subgroup.card_subgroup_dvd_card Q
  refine fun h0 => Invertible.ne_zero (Nat.card G : K) ?_
  rw [hc, Nat.cast_mul, h0, zero_mul]

set_option maxHeartbeats 400000 in
-- Two splitting data plus the whole Brauer-character chain elaborate inside this one proof.
/-- **The restriction of an irreducible Brauer character to a `p'`-subgroup is a virtual
character.**  This is the hypothesis `hsub` of
`exists_int_block_sum_eq_irreducibleBrauerCharacter` (Navarro (3.16)).

The Brauer character of `Q` on the restricted module is the restriction of the Brauer character of
`G` — literally the same sum of eigenvalue multiplicities, since `ρ.comp Q.subtype` sends `x` to
`ρ ↑x` — taken at the exponent `|G|_{p'}` rather than `|Q|_{p'}`.  That is admissible because
`|Q|_{p'} ∣ |G|_{p'}`, and `brauerCharacter_mem_virtualCharacters_of_not_dvd_card` allows any such
exponent. -/
theorem restrict_irreducibleBrauerCharacter_mem_virtualCharacters
    [IsAlgClosed (ResidueField 𝒪)] [IsAlgClosed K] [Invertible (Nat.card G : K)]
    (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
    (π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪))
    (μ₀ : ι) {Q : Subgroup G} (hQ : ¬ p ∣ Nat.card ↥Q) :
    (fun g => algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀ g)) ∘ Q.subtype
      ∈ virtualCharacters K ↥Q := by
  classical
  have : Fintype ↥Q := Fintype.ofFinite _
  have : NeZero (Nat.card ↥Q : K) := ⟨natCard_subgroup_ne_zero (K := K) Q⟩
  have : Invertible (Nat.card ↥Q : K) := invertibleOfNonzero (natCard_subgroup_ne_zero (K := K) Q)
  have hkres : ((p : ℕ) : ResidueField 𝒪) = 0 := CharP.cast_eq_zero (ResidueField 𝒪) p
  -- the two splitting data for `Q`
  obtain ⟨n, d, hd, πQ, hπQ, hlinQ, hkerQ⟩ := exists_splitting_of_not_dvd_card hp hkres hQ
  have : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, Nat.pos_of_ne_zero (hd i).out⟩⟩
  obtain ⟨n', d', hd', ⟨eQ⟩⟩ := exists_algEquiv_pi_matrix_monoidAlgebra K ↥Q
  have : ∀ i, Nonempty (Fin (d' i)) := fun i => ⟨⟨0, Nat.pos_of_ne_zero (hd' i).out⟩⟩
  -- the roots of unity, inherited from `G`
  have hdvd : pRegularExponent p ↥Q ∣ pRegularExponent p G := pRegularExponent_subgroup_dvd Q
  have hprod : pRegularExponent p G
      = (pRegularExponent p G / pRegularExponent p ↥Q) * pRegularExponent p ↥Q :=
    (Nat.div_mul_cancel hdvd).symm
  have hωQ := hω.pow (pRegularExponent_pos (p := p) (G := G)) hprod
  have hω'Q := hω'.pow (pRegularExponent_pos (p := p) (G := G)) hprod
  -- and the Brauer character of the restricted block, at the exponent of `G`
  have := brauerCharacter_mem_virtualCharacters_of_not_dvd_card (𝒪 := 𝒪) (K := K) (ι' := Fin n')
    (m := fun i => Fin (d' i)) hp hωQ hω'Q hπQ hlinQ hkerQ eQ hQ hdvd
    (not_dvd_pRegularExponent hp) (pRegularExponent_pos (p := p) (G := G)).ne'
    ((blockRepresentation π μ₀).comp Q.subtype)
  exact this

end Restriction

/-! ### Navarro (3.16) with the restriction hypothesis discharged -/

section Integral

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Fintype G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [DecidableEq ι]
  [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  [Invertible (Nat.card G : K)]
variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
variable [FaithfulSMul 𝒪 K] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]
  (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    MatrixModule.blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
variable {N : ℕ} {ωBT : K}

set_option maxHeartbeats 400000 in
-- The whole Brauer-characterization chain plus the two splitting constructions.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
include hp hω hω' hπ hlin hkerJ e hnil in
/-- **Navarro (3.16), unconditionally**: over algebraically closed `K` and residue field, every
`μ_0 ∈ IBr(B)` is a `ℤ`-combination of `{χ⁰ : χ ∈ Irr(B)}`.

The restriction hypothesis of `exists_int_block_sum_eq_irreducibleBrauerCharacter` — which is
where Brauer's characterization of characters enters — is discharged by
`restrict_irreducibleBrauerCharacter_mem_virtualCharacters`. -/
theorem exists_int_block_sum_eq_irreducibleBrauerCharacter_of_isAlgClosed
    [IsAlgClosed (ResidueField 𝒪)] [IsAlgClosed K] (hN : N ≠ 0) (hgN : ∀ g : G, g ^ N = 1)
    (hωBT : IsPrimitiveRoot ωBT N) (μ₀ : ι) :
    ∃ a : ι' → ℤ,
      (∀ i : ι', blockOfIrr e hπ hlin hnil i
        ≠ Quotient.mk (MatrixModule.blockSetoid π hπ hlin) μ₀ → a i = 0) ∧
      ∀ g : G, IsPRegular p g →
        algebraMap 𝒪 K (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ₀ g)
          = ∑ i : ι', (a i : K) * algebraMap 𝒪 K (ordinaryCharacter (𝒪 := 𝒪) e i g) :=
  exists_int_block_sum_eq_irreducibleBrauerCharacter hp hω hω' hπ hlin hkerJ e hnil hN hgN hωBT μ₀
    fun _ hQ =>
      restrict_irreducibleBrauerCharacter_mem_virtualCharacters (K := K) hp hω hω' π μ₀ hQ

end Integral

end OddOrder.RepresentationTheory.Modular
