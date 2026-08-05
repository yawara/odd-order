/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.QuotientPairing
import OddOrder.GroupTheory.RepresentationTheory.Modular.QuotientSplitting

/-!
# Navarro (7.6): the Cartan matrices are related by `C = |P| C̄`

Final step of Navarro (7.6).  Let `N ⊴ G` be a `p`-subgroup centralised by every `p`-regular
element of `G` (in the Brauer–Suzuki application `N = P ≤ Z(G)`, so the hypothesis is free).  Two
facts have already been established:

* the induced splitting `π̄` of `k[G/N]` has the **same** index set `ι` for the irreducible Brauer
  characters, and the two families take the same values under `g ↦ ḡ`
  (`irreducibleBrauerCharacter_quotientPi`, `QuotientSplitting`);
* the pairing scales by `|N|`: `|N| · [a,b]⁰_G = [ā,b̄]⁰_Ḡ` (`card_mul_pairingZero_quotient`,
  `QuotientPairing`).

Navarro's argument is then pure linear algebra: `([φ,θ]⁰)` is a two-sided inverse of the Cartan
matrix (`sum_cartanMatrix_mul_pairingZero`), a matrix has at most one inverse, and `|N| C̄`
inverts the same matrix that `C` does.  Hence `C = |N| C̄`.

Because the Cartan matrix is block diagonal (`cartanMatrix_eq_zero_of_centralCharacterAlg_ne`),
the block form `C_B = |P| C_B̄` of the theorem statement is the restriction of this identity to the
indices lying in a block; no separate argument is needed.

Note that the two ordinary splittings are unrelated: `Irr(G/N)` is a *proper* subset of `Irr(G)`
in general, so `e'` is a splitting datum of `K[G/N]` with its own index set, and the two primitive
roots of unity for `G/N` may be chosen independently of those for `G`.  Only the modular index set
`ι` is shared, and that sharing is the content of (7.6).

## Main results

* `OddOrder.RepresentationTheory.Modular.eq_of_sum_mul_eq_ite` — uniqueness of the inverse, in the
  index form the Cartan identity supplies
* `OddOrder.RepresentationTheory.Modular.card_mul_pairingZero_irreducibleBrauerCharacter_quotientPi`
* `OddOrder.RepresentationTheory.Modular.natCast_cartanMatrix_quotientPi` — `C = |N| C̄` in `K`
* `OddOrder.RepresentationTheory.Modular.cartanMatrix_quotientPi` — `C = |N| C̄` in `ℕ`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

/-! ### Uniqueness of the inverse -/

/-- **Two families with the same right inverse agree.**  Stated in the index form in which
`sum_cartanMatrix_mul_pairingZero` delivers `Cᵀ · P = 1`: the hypothesis says that both `c` and
`c'` invert `P`, and a square matrix has at most one inverse. -/
theorem eq_of_sum_mul_eq_ite {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]
    (P c c' : ι → ι → K)
    (hc : ∀ φ θ : ι, ∑ μ, c μ θ * P μ φ = if φ = θ then 1 else 0)
    (hc' : ∀ φ θ : ι, ∑ μ, c' μ θ * P μ φ = if φ = θ then 1 else 0) :
    c = c' := by
  have key : ∀ d : ι → ι → K, (∀ φ θ : ι, ∑ μ, d μ θ * P μ φ = if φ = θ then 1 else 0) →
      (Matrix.of fun θ μ => d μ θ) * Matrix.of P = 1 := by
    intro d hd
    ext θ φ
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [hd φ θ]
    exact if_congr eq_comm rfl rfl
  have hinv := (Matrix.inv_eq_left_inv (key c hc)).symm.trans (Matrix.inv_eq_left_inv (key c' hc'))
  ext μ θ
  exact congrFun (congrFun hinv θ) μ

/-! ### The Cartan matrices of `G` and of `G/N` -/

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} [Fintype ι'] {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)]
variable {ι'' : Type*} [Fintype ι''] {m' : ι'' → Type*} [∀ i, Fintype (m' i)]
  [∀ i, DecidableEq (m' i)] [∀ i, Nonempty (m' i)]
variable {N : Subgroup G} [N.Normal] [hpF : Fact p.Prime]
  [Invertible (Nat.card G : K)] [Invertible (Nat.card (G ⧸ N) : K)]
variable {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {ϖ : 𝒪} (hϖ : IsPrimitiveRoot ϖ (pRegularExponent p (G ⧸ N)))
  {ϖ' : ResidueField 𝒪} (hϖ' : IsPrimitiveRoot ϖ' (pRegularExponent p (G ⧸ N)))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
  (e' : MonoidAlgebra K (G ⧸ N) ≃ₐ[K] ∀ j, Matrix (m' j) (m' j) K)
  (hN : IsPGroup p ↥N)
  (hcent : ∀ x : G, IsPRegular p x → ∀ z ∈ N, Commute x z)

omit [IsDomain 𝒪] [ValuationRing 𝒪] [IsFractionRing 𝒪 K] [Fintype ι] in
include hcent in
/-- **The pairing of two irreducible Brauer characters scales by `|N|`.**  This is
`card_mul_pairingZero_quotient` fed with the value identity `φ(g) = φ̄(ḡ)` of (7.6). -/
theorem card_mul_pairingZero_irreducibleBrauerCharacter_quotientPi
    [Fintype G] [Fintype (G ⧸ N)] (μ φ : ι) :
    (Nat.card ↥N : K) * pairingZero (𝒪 := 𝒪) p K
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π μ)
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π φ)
      = pairingZero (𝒪 := 𝒪) p K
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) (quotientPi π hπ hlin hN).toRingHom μ)
        (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) (quotientPi π hπ hlin hN).toRingHom φ) :=
  card_mul_pairingZero_quotient hpF.out hN hcent _ _ _ _
    (fun g _ => (irreducibleBrauerCharacter_quotientPi π hπ hlin hN μ g).symm)
    (fun g _ => (irreducibleBrauerCharacter_quotientPi π hπ hlin hN φ g).symm)

include hcent in
/-- **Navarro (7.6): `C = |P| C̄`**, read in `K`.  Both `C` and `|N| C̄` invert the matrix
`([μ,φ]⁰_G)` — the first by `sum_cartanMatrix_mul_pairingZero` for `G`, the second because the
pairing for `G/N` is `|N|` times the pairing for `G` — and the inverse is unique. -/
theorem natCast_cartanMatrix_quotientPi (μ θ : ι) :
    ((cartanMatrix hpF.out hω hω' hπ hlin hkerJ e μ θ : ℕ) : K)
      = (Nat.card ↥N : K) * ((cartanMatrix hpF.out hϖ hϖ'
          (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)
          (ker_quotientPi π hπ hlin hN hkerJ) e' μ θ : ℕ) : K) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  refine congrFun (congrFun (eq_of_sum_mul_eq_ite
    (fun a b : ι => pairingZero (𝒪 := 𝒪) p K
      (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π a)
      (irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪) π b))
    (fun a b : ι => ((cartanMatrix hpF.out hω hω' hπ hlin hkerJ e a b : ℕ) : K))
    (fun a b : ι => (Nat.card ↥N : K) * ((cartanMatrix hpF.out hϖ hϖ'
      (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)
      (ker_quotientPi π hπ hlin hN hkerJ) e' a b : ℕ) : K))
    (fun φ' θ' => sum_cartanMatrix_mul_pairingZero hpF.out hω hω' hπ hlin hkerJ e φ' θ')
    fun φ' θ' => ?_) μ) θ
  rw [← sum_cartanMatrix_mul_pairingZero (𝒪 := 𝒪) hpF.out hϖ hϖ'
    (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)
    (ker_quotientPi π hπ hlin hN hkerJ) e' φ' θ']
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← card_mul_pairingZero_irreducibleBrauerCharacter_quotientPi hπ hlin hN hcent ν φ']
  ring

include hcent in
/-- **Navarro (7.6): `C = |P| C̄`.**  The `ℕ`-valued form; `K` has characteristic zero, so the
identity of `natCast_cartanMatrix_quotientPi` transfers back. -/
theorem cartanMatrix_quotientPi (μ θ : ι) :
    cartanMatrix hpF.out hω hω' hπ hlin hkerJ e μ θ
      = Nat.card ↥N * cartanMatrix hpF.out hϖ hϖ'
          (quotientPi_surjective π hπ hlin hN) (quotientPi_smul π hπ hlin hN)
          (ker_quotientPi π hπ hlin hN hkerJ) e' μ θ := by
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  refine Nat.cast_injective (R := K) ?_
  rw [Nat.cast_mul]
  exact natCast_cartanMatrix_quotientPi hω hω' hϖ hϖ' hπ hlin hkerJ e e' hN hcent μ θ

end OddOrder.RepresentationTheory.Modular
