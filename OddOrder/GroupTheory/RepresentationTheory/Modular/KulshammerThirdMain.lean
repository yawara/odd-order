/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.PElementSumCount
import OddOrder.GroupTheory.PRegularElementCount
import OddOrder.GroupTheory.RepresentationTheory.Modular.KulshammerFormula

/-!
# Külshammer's route to the third main theorem: `e_{B_0}` is read off inside `C_G(Q)`

Külshammer's formula (Navarro (6.14), `coeff_pElementSum_mul_pRegularSum_principalBlock`) says

`(Ĝ_p · Ĝ⁰)(g) = |G⁰|* · e_{B_0}(g)`,

and the left side is a plain count (`coeff_pElementSum_mul_pRegularSum`):

`(Ĝ_p · Ĝ⁰)(g) = |Ω_G(g)|*`,  `Ω_G(g) = {(x, y) : x a p-element, y p-regular, x y = g}`.

So `e_{B_0}` is determined by counting: `|G⁰|* · e_{B_0}(g) = |Ω_G(g)|*`, and `p ∤ |G⁰|`
(`not_dvd_card_isPRegular`) makes the left factor invertible.

Now let `Q` be a `p`-subgroup and `g ∈ C_G(Q)`.  Navarro, Problem (6.1)
(`card_pFactorPairs_modEq_centralizer`) says `Q` sees `Ω_G(g)` only through its centraliser,

`|Ω_G(g)| ≡ |Ω_{C_G(Q)}(g)| (mod p)`,

and the same action on `G⁰` gives the matching normalisation `|G⁰| ≡ |C_G(Q)⁰| (mod p)`
(`card_pRegular_modEq_centralizer`).  Since the residue field has characteristic `p`, the two
instances of Külshammer's formula — one for `G`, one for `C_G(Q)` — have equal right-hand sides
and equal left-hand factors, so

`e_{B_0}^G(g) = e_{b_0}^{C_G(Q)}(g)`  for `g ∈ C_G(Q)`,

i.e. `Br_Q(e_{B_0}) = e_{b_0}`.  This is the computation behind the **third main theorem** for
`Q C_G(Q) ≤ H ≤ N_G(Q)`, and it bypasses Okuyama's argument ((6.6)) together with the height
theory and Brauer's characterisation of characters that it needs.

## Main results

* `OddOrder.RepresentationTheory.Modular.card_pRegular_mul_coeff_principalBlock` — Külshammer's
  formula in counting form, at an arbitrary group element
* `OddOrder.RepresentationTheory.Modular.eq_of_card_pRegular_mul_eq` — the comparison step,
  stated on the two counts alone
* `OddOrder.RepresentationTheory.Modular.coeff_principalBlock_eq_centralizer` —
  `e_{B_0}^G(g) = e_{b_0}^{C_G(Q)}(g)`
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupAlgebra OddOrder.GroupTheory
  OddOrder.GroupTheory.CenterClassSum

/-! ### The two counts and the cancellation -/

section Counting

variable {p : ℕ} {G : Type*} [Group G]

open scoped Classical in
/-- The `Finset.card` form of `|G⁰|` used by the block statements is `Nat.card` of the
`p`-regular carrier. -/
theorem card_filter_isPRegular [Fintype G] :
    (Finset.univ.filter (fun g : G => IsPRegular p g)).card = Nat.card (PRegularCarrier p G) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

variable [Finite G] {Q : Subgroup G} {k : Type*} [Field k] [CharP k p]

/-- **The comparison step of Külshammer's route to the third main theorem.**

Both sides of Külshammer's formula are counts, and a `p`-subgroup `Q` sees both of them only
through `C_G(Q)`: `|Ω_G(g)| ≡ |Ω_{C_G(Q)}(g)|` (Navarro, Problem (6.1)) and
`|G⁰| ≡ |C_G(Q)⁰|` (mod `p`).  In characteristic `p` the two formulas therefore read
`|G⁰|* · a = |G⁰|* · b`, and `p ∤ |G⁰|` cancels the factor.

Stated on the counts alone, so that it applies to whatever block data the two groups carry. -/
theorem eq_of_card_pRegular_mul_eq (hp : p.Prime) (hQ : IsPGroup p ↥Q)
    (g : ↥(Subgroup.centralizer (Q : Set G))) {a b : k}
    (ha : (Nat.card (PRegularCarrier p G) : k) * a = (Nat.card (PFactorPairs p (g : G)) : k))
    (hb : (Nat.card (PRegularCarrier p ↥(Subgroup.centralizer (Q : Set G))) : k) * b
      = (Nat.card (PFactorPairs p g) : k)) :
    a = b := by
  -- `|Ω_G(g)| ≡ |Ω_H(g)|`: Problem (6.1), then the pairs inside `H` are the pairs with both
  -- entries in `H`.
  have heqΩ : Nat.card (PFactorPairs p g)
      = Nat.card {q : PFactorPairs p ((g : G)) //
          (q : G × G).1 ∈ Subgroup.centralizer (Q : Set G) ∧
            (q : G × G).2 ∈ Subgroup.centralizer (Q : Set G)} :=
    Nat.card_congr (pFactorPairsSubgroupEquiv (H := Subgroup.centralizer (Q : Set G)) p g)
  have hΩ : Nat.card (PFactorPairs p ((g : G))) ≡ Nat.card (PFactorPairs p g) [MOD p] := by
    rw [heqΩ]
    exact card_pFactorPairs_modEq_centralizer Q (g : G) hp hQ g.2
  -- `|G⁰| ≡ |H⁰|`: the same action on the `p`-regular elements.
  have heqreg : Nat.card (PRegularCarrier p ↥(Subgroup.centralizer (Q : Set G)))
      = Nat.card {y : PRegularCarrier p G // (y : G) ∈ Subgroup.centralizer (Q : Set G)} :=
    Nat.card_congr (pRegularSubgroupEquiv (H := Subgroup.centralizer (Q : Set G)) p)
  have hreg : Nat.card (PRegularCarrier p G)
      ≡ Nat.card (PRegularCarrier p ↥(Subgroup.centralizer (Q : Set G))) [MOD p] := by
    rw [heqreg]
    exact card_pRegular_modEq_centralizer Q hp hQ
  have hΩk : (Nat.card (PFactorPairs p ((g : G))) : k) = (Nat.card (PFactorPairs p g) : k) :=
    (CharP.natCast_eq_natCast k p).mpr hΩ
  have hregk : (Nat.card (PRegularCarrier p G) : k)
      = (Nat.card (PRegularCarrier p ↥(Subgroup.centralizer (Q : Set G))) : k) :=
    (CharP.natCast_eq_natCast k p).mpr hreg
  have hne : (Nat.card (PRegularCarrier p G) : k) ≠ 0 := fun h =>
    not_dvd_card_isPRegular (G := G) hp ((CharP.cast_eq_zero_iff k p _).mp h)
  refine mul_left_cancel₀ hne ?_
  rw [ha, hΩk, ← hb, hregk]

end Counting

/-! ### Külshammer's formula in counting form -/

variable {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [Field K] [CharZero K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Invertible (Nat.card G : K)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι']
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
variable [HenselianLocalRing 𝒪] {p : ℕ} [IsPModularSystem p 𝒪] [Fintype (ConjClasses G)]
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    MatrixModule.blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

set_option maxHeartbeats 1600000 in
-- Same instance chains as (6.14); the extra work here is only the transport along `mk g`.
set_option linter.unusedFintypeInType false in
open scoped Classical in
/-- **Külshammer's formula in counting form**, at an arbitrary `g` (not just a class
representative):

`|G⁰|* · e_{B_0}(g) = |Ω(g)|*`,  `Ω(g) = {(x, y) : x a p-element, y p-regular, x y = g}`.

Both sides of (6.14) are coefficients of central elements, hence constant on conjugacy classes,
so the statement at `(mk g).out` transports to `g`. -/
theorem card_pRegular_mul_coeff_principalBlock [Fact p.Prime]
    [Fintype (MatrixModule.Block πG hπG hlinG)] (S : Sylow p G) (g : G)
    {F : MatrixModule.Block πG hπG hlinG → Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)}
    {F' : MatrixModule.Block πG hπG hlinG →
      Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)}
    (hidem : ∀ B, IsIdempotentElem (F B))
    (hf : ∀ B, MonoidAlgebra.mapRingHom G (residue 𝒪) ((F B : MonoidAlgebra 𝒪 G))
      = ((F' B : MonoidAlgebra (ResidueField 𝒪) G)))
    (hB : ∀ B, MatrixModule.blockCharacterPi πG hπG hlinG (F' B) = Pi.single B 1)
    (hweak : ∀ B : MatrixModule.Block πG hπG hlinG, ∀ x : ↥(S : Subgroup G), (x : G) ≠ 1 →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character g⁻¹
          * (wedderburnRepresentation e i).character (x : G) = 0)
    (hvanish : ∀ B : MatrixModule.Block πG hπG hlinG,
      B ≠ principalBlock πG hπG hlinG hnilG →
      MatrixModule.blockCharacter πG hπG hlinG B
        ⟨pRegularSum p (ResidueField 𝒪), pRegularSum_mem_center⟩ = 0) :
    (Nat.card (PRegularCarrier p G) : ResidueField 𝒪)
        * ((F' (principalBlock πG hπG hlinG hnilG) :
            MonoidAlgebra (ResidueField 𝒪) G)).coeff g
      = (Nat.card (PFactorPairs p g) : ResidueField 𝒪) := by
  classical
  set C : ConjClasses G := ConjClasses.mk g with hC
  have hmk : ConjClasses.mk C.out = ConjClasses.mk g := by
    rw [hC, ← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  have hconj : IsConj C.out g := ConjClasses.mk_eq_mk_iff_isConj.mp hmk
  -- transport `hweak` from `g⁻¹` to `C.out⁻¹`: characters are class functions
  have hweak' : ∀ B : MatrixModule.Block πG hπG hlinG, ∀ x : ↥(S : Subgroup G), (x : G) ≠ 1 →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character C.out⁻¹
          * (wedderburnRepresentation e i).character (x : G) = 0 := by
    intro B x hx
    rw [← hweak B x hx]
    exact Finset.sum_congr rfl fun i _ => by
      rw [character_eq_of_isConj (wedderburnRepresentation e i) (IsConj.inv' hconj)]
  have key := coeff_pElementSum_mul_pRegularSum_principalBlock e hπG hlinG hnilG S C hidem hf hB
    hweak' hvanish
  -- both sides are coefficients of central elements, so they may be read at `g`
  have hcentral : (pElementSum p (ResidueField 𝒪) (G := G) * pRegularSum p (ResidueField 𝒪))
      ∈ Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G) :=
    Subalgebra.mul_mem _ pElementSum_mem_center pRegularSum_mem_center
  rw [coeff_center_of_mk_eq hcentral hmk,
    coeff_center_of_mk_eq (F' (principalBlock πG hπG hlinG hnilG)).2 hmk,
    OddOrder.GroupAlgebra.coeff_pElementSum_mul_pRegularSum (p := p) g,
    card_filter_isPRegular] at key
  exact key.symm

/-! ### `Br_Q(e_{B_0}) = e_{b_0}` -/

section ThirdMain

variable {Q : Subgroup G}
variable [Fintype ↥(Subgroup.centralizer (Q : Set G))]
  [DecidableEq (ConjClasses ↥(Subgroup.centralizer (Q : Set G)))]
  [Fintype (ConjClasses ↥(Subgroup.centralizer (Q : Set G)))]
  [Invertible (Nat.card ↥(Subgroup.centralizer (Q : Set G)) : K)]
variable {ι'C : Type*} {mC : ι'C → Type*} [∀ i, Fintype (mC i)] [∀ i, DecidableEq (mC i)]
  [∀ i, Nonempty (mC i)] [Fintype ι'C]
variable (eC : MonoidAlgebra K ↥(Subgroup.centralizer (Q : Set G)) ≃ₐ[K]
    ∀ i, Matrix (mC i) (mC i) K)
variable {ιC : Type*} [Finite ιC] {nnC : ιC → Type*} [∀ j, Fintype (nnC j)]
  [∀ j, DecidableEq (nnC j)] [∀ j, Nonempty (nnC j)]
variable {πC : MonoidAlgebra (ResidueField 𝒪) ↥(Subgroup.centralizer (Q : Set G)) →+*
    ∀ j, Matrix (nnC j) (nnC j) (ResidueField 𝒪)}
  (hπC : Function.Surjective πC)
  (hlinC : ∀ (c : ResidueField 𝒪)
    (a : MonoidAlgebra (ResidueField 𝒪) ↥(Subgroup.centralizer (Q : Set G))),
    πC (c • a) = c • πC a)
  (hnilC : ∀ z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) ↥(Subgroup.centralizer (Q : Set G))),
    MatrixModule.blockCharacterPi πC hπC hlinC z = 0 → IsNilpotent z)

set_option maxHeartbeats 1600000 in
-- Two full copies of the splitting data of (6.14), one for `G` and one for `C_G(Q)`.
set_option linter.unusedFintypeInType false in
open scoped Classical in
/-- **`Br_Q(e_{B_0}) = e_{b_0}`** (coefficient form), the computation behind the third main
theorem for `Q C_G(Q) ≤ H ≤ N_G(Q)` along Külshammer's route.

For a `p`-subgroup `Q` and `g ∈ C_G(Q)`, the coefficient of the principal block idempotent of
`G` at `g` equals the coefficient of the principal block idempotent of `C_G(Q)` at `g`.

Külshammer's formula (`card_pRegular_mul_coeff_principalBlock`) turns each coefficient into a
count of factorisations `g = x y` normalised by the number of `p`-regular elements, and `Q` sees
both counts only through `C_G(Q)` (Navarro, Problem (6.1)). -/
theorem coeff_principalBlock_eq_centralizer (hp : p.Prime) (hQ : IsPGroup p ↥Q)
    [Fintype (MatrixModule.Block πG hπG hlinG)] [Fintype (MatrixModule.Block πC hπC hlinC)]
    (SG : Sylow p G) (SC : Sylow p ↥(Subgroup.centralizer (Q : Set G)))
    (g : ↥(Subgroup.centralizer (Q : Set G)))
    {F : MatrixModule.Block πG hπG hlinG → Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)}
    {F' : MatrixModule.Block πG hπG hlinG →
      Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G)}
    (hidem : ∀ B, IsIdempotentElem (F B))
    (hf : ∀ B, MonoidAlgebra.mapRingHom G (residue 𝒪) ((F B : MonoidAlgebra 𝒪 G))
      = ((F' B : MonoidAlgebra (ResidueField 𝒪) G)))
    (hB : ∀ B, MatrixModule.blockCharacterPi πG hπG hlinG (F' B) = Pi.single B 1)
    (hweak : ∀ B : MatrixModule.Block πG hπG hlinG, ∀ x : ↥(SG : Subgroup G), (x : G) ≠ 1 →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr e hπG hlinG hnilG i = B),
        (wedderburnRepresentation e i).character (g : G)⁻¹
          * (wedderburnRepresentation e i).character (x : G) = 0)
    (hvanish : ∀ B : MatrixModule.Block πG hπG hlinG,
      B ≠ principalBlock πG hπG hlinG hnilG →
      MatrixModule.blockCharacter πG hπG hlinG B
        ⟨pRegularSum p (ResidueField 𝒪), pRegularSum_mem_center⟩ = 0)
    {FC : MatrixModule.Block πC hπC hlinC →
      Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 ↥(Subgroup.centralizer (Q : Set G)))}
    {FC' : MatrixModule.Block πC hπC hlinC →
      Subalgebra.center (ResidueField 𝒪)
        (MonoidAlgebra (ResidueField 𝒪) ↥(Subgroup.centralizer (Q : Set G)))}
    (hidemC : ∀ B, IsIdempotentElem (FC B))
    (hfC : ∀ B, MonoidAlgebra.mapRingHom ↥(Subgroup.centralizer (Q : Set G)) (residue 𝒪)
        ((FC B : MonoidAlgebra 𝒪 ↥(Subgroup.centralizer (Q : Set G))))
      = ((FC' B : MonoidAlgebra (ResidueField 𝒪) ↥(Subgroup.centralizer (Q : Set G)))))
    (hBC : ∀ B, MatrixModule.blockCharacterPi πC hπC hlinC (FC' B) = Pi.single B 1)
    (hweakC : ∀ B : MatrixModule.Block πC hπC hlinC,
      ∀ x : ↥(SC : Subgroup ↥(Subgroup.centralizer (Q : Set G))),
        (x : ↥(Subgroup.centralizer (Q : Set G))) ≠ 1 →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr eC hπC hlinC hnilC i = B),
        (wedderburnRepresentation eC i).character g⁻¹
          * (wedderburnRepresentation eC i).character
              (x : ↥(Subgroup.centralizer (Q : Set G))) = 0)
    (hvanishC : ∀ B : MatrixModule.Block πC hπC hlinC,
      B ≠ principalBlock πC hπC hlinC hnilC →
      MatrixModule.blockCharacter πC hπC hlinC B
        ⟨pRegularSum p (ResidueField 𝒪), pRegularSum_mem_center⟩ = 0) :
    ((F' (principalBlock πG hπG hlinG hnilG) :
        MonoidAlgebra (ResidueField 𝒪) G)).coeff (g : G)
      = ((FC' (principalBlock πC hπC hlinC hnilC) :
          MonoidAlgebra (ResidueField 𝒪) ↥(Subgroup.centralizer (Q : Set G)))).coeff g := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  exact eq_of_card_pRegular_mul_eq (k := ResidueField 𝒪) hp hQ g
    (card_pRegular_mul_coeff_principalBlock e hπG hlinG hnilG SG (g : G)
      hidem hf hB hweak hvanish)
    (card_pRegular_mul_coeff_principalBlock eC hπC hlinC hnilC SC g
      hidemC hfC hBC hweakC hvanishC)

end ThirdMain

end OddOrder.RepresentationTheory.Modular
