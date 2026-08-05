/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.PElementSumCount
import OddOrder.GroupTheory.PRegularElementCount
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockCharacterOffCentralizer
import OddOrder.GroupTheory.RepresentationTheory.Modular.InducedBlockDefined
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

Feeding it back into the central characters gives the **converse** half of the third main
theorem, which is the direction Brauer–Suzuki uses: for `b` a block of `C_G(Q)`,

`λ_b^G(e_{B_0}) = λ_b(Br_Q(e_{B_0})) = λ_b(e_{b_0}) = δ_{b b_0}`,

so `b^G = B_0` — which makes the left side `λ_{B_0}(e_{B_0}) = 1` — forces `b = b_0`.

## Main results

* `OddOrder.RepresentationTheory.Modular.card_pRegular_mul_coeff_principalBlock` — Külshammer's
  formula in counting form, at an arbitrary group element
* `OddOrder.RepresentationTheory.Modular.eq_of_card_pRegular_mul_eq` — the comparison step,
  stated on the two counts alone
* `OddOrder.RepresentationTheory.Modular.coeff_principalBlock_eq_centralizer` —
  `e_{B_0}^G(g) = e_{b_0}^{C_G(Q)}(g)`
* `OddOrder.RepresentationTheory.Modular.eq_principalBlock_of_inducedBlockOfNormalizer_eq` —
  the converse of the third main theorem for `H = C_G(Q)`, `Q` abelian
* `OddOrder.RepresentationTheory.Modular.eq_of_card_pRegular_mul_eq_intermediate`,
  `OddOrder.RepresentationTheory.Modular.coeff_principalBlock_eq_centralizer_intermediate` —
  the same comparison between `C_G(Q)` and an arbitrary intermediate `Q C_G(Q) ≤ H`
* `..._of_inducedBlockOfNormalizer_eq_intermediate` — the converse of the third main theorem for
  a general `Q C_G(Q) ≤ H ≤ N_G(Q)`

⚠ The two converse statements have *incomparable* hypotheses.  The `H = C_G(Q)` one needs no
`Q ≤ H`, because there `Br_Q(e_{B_0}) = e_{b_0}` on the nose; the general one needs `Q ≤ H` (it
goes through Navarro (4.7) inside `H`), which at `H = C_G(Q)` would force `Q` abelian.  Together
they cover Navarro's range `Q C_G(Q) ⊆ H ⊆ N_G(Q)` and, in addition, `H = C_G(Q)` for
non-abelian `Q`.
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupAlgebra OddOrder.GroupTheory
  OddOrder.GroupTheory.CenterClassSum

/-! ### The two counts and the cancellation -/

section Counting

variable {p : ℕ} {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
  {k : Type*} [Field k] [CharP k p]

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

/-- **The comparison step run inside an intermediate subgroup** `Q C_G(Q) ≤ H`.

Identical to `eq_of_card_pRegular_mul_eq` with `G` replaced by `H`: the `Q`-action on the
factorisations with entries in `H` again has the pairs in `C_G(Q)` as fixed points
(`card_pFactorPairsMem_modEq_centralizer`), and likewise on the `p`-regular elements. -/
theorem eq_of_card_pRegular_mul_eq_intermediate (hp : p.Prime) (hQ : IsPGroup p ↥Q)
    {H : Subgroup G} (hQH : Q ≤ H) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (g : ↥(Subgroup.centralizer (Q : Set G))) {a b : k}
    (ha : (Nat.card (PRegularCarrier p ↥H) : k) * a
      = (Nat.card (PFactorPairs p (⟨(g : G), hCH g.2⟩ : ↥H)) : k))
    (hb : (Nat.card (PRegularCarrier p ↥(Subgroup.centralizer (Q : Set G))) : k) * b
      = (Nat.card (PFactorPairs p g) : k)) :
    a = b := by
  -- `|Ω_H(g)| ≡ |Ω_{C_G(Q)}(g)|`
  have heqH : Nat.card (PFactorPairs p (⟨(g : G), hCH g.2⟩ : ↥H))
      = Nat.card {q : PFactorPairs p ((g : G)) //
          (q : G × G).1 ∈ H ∧ (q : G × G).2 ∈ H} :=
    Nat.card_congr (pFactorPairsSubgroupEquiv (H := H) p ⟨(g : G), hCH g.2⟩)
  have heqC : Nat.card (PFactorPairs p g)
      = Nat.card {q : PFactorPairs p ((g : G)) //
          (q : G × G).1 ∈ Subgroup.centralizer (Q : Set G) ∧
            (q : G × G).2 ∈ Subgroup.centralizer (Q : Set G)} :=
    Nat.card_congr (pFactorPairsSubgroupEquiv (H := Subgroup.centralizer (Q : Set G)) p g)
  have hΩ : Nat.card (PFactorPairs p (⟨(g : G), hCH g.2⟩ : ↥H))
      ≡ Nat.card (PFactorPairs p g) [MOD p] := by
    rw [heqH, heqC]
    exact card_pFactorPairsMem_modEq_centralizer hp hQ hQH hCH g.2
  -- `|H⁰| ≡ |C_G(Q)⁰|`
  have hregH : Nat.card (PRegularCarrier p ↥H)
      = Nat.card {y : PRegularCarrier p G // (y : G) ∈ H} :=
    Nat.card_congr (pRegularSubgroupEquiv (H := H) p)
  have hregC : Nat.card (PRegularCarrier p ↥(Subgroup.centralizer (Q : Set G)))
      = Nat.card {y : PRegularCarrier p G // (y : G) ∈ Subgroup.centralizer (Q : Set G)} :=
    Nat.card_congr (pRegularSubgroupEquiv (H := Subgroup.centralizer (Q : Set G)) p)
  have hreg : Nat.card (PRegularCarrier p ↥H)
      ≡ Nat.card (PRegularCarrier p ↥(Subgroup.centralizer (Q : Set G))) [MOD p] := by
    rw [hregH, hregC]
    exact card_pRegularMem_modEq_centralizer hp hQ hQH hCH
  have hΩk : (Nat.card (PFactorPairs p (⟨(g : G), hCH g.2⟩ : ↥H)) : k)
      = (Nat.card (PFactorPairs p g) : k) := (CharP.natCast_eq_natCast k p).mpr hΩ
  have hregk : (Nat.card (PRegularCarrier p ↥H) : k)
      = (Nat.card (PRegularCarrier p ↥(Subgroup.centralizer (Q : Set G))) : k) :=
    (CharP.natCast_eq_natCast k p).mpr hreg
  have hne : (Nat.card (PRegularCarrier p ↥H) : k) ≠ 0 := fun h =>
    not_dvd_card_isPRegular (G := ↥H) hp ((CharP.cast_eq_zero_iff k p _).mp h)
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

/-! ### The same coefficient identity between an intermediate subgroup and `C_G(Q)` -/

section IntermediateCoeff

variable {Q : Subgroup G} {H : Subgroup G}
variable [Fintype ↥H] [DecidableEq (ConjClasses ↥H)] [Fintype (ConjClasses ↥H)]
  [Invertible (Nat.card ↥H : K)]
variable {ι'H : Type*} {mH : ι'H → Type*} [∀ i, Fintype (mH i)] [∀ i, DecidableEq (mH i)]
  [∀ i, Nonempty (mH i)] [Fintype ι'H]
variable (eH : MonoidAlgebra K ↥H ≃ₐ[K] ∀ i, Matrix (mH i) (mH i) K)
variable {ιH : Type*} [Finite ιH] {nnH : ιH → Type*} [∀ j, Fintype (nnH j)]
  [∀ j, DecidableEq (nnH j)] [∀ j, Nonempty (nnH j)]
variable {πH : MonoidAlgebra (ResidueField 𝒪) ↥H →+*
    ∀ j, Matrix (nnH j) (nnH j) (ResidueField 𝒪)}
  (hπH : Function.Surjective πH)
  (hlinH : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥H),
    πH (c • a) = c • πH a)
  (hnilH : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) ↥H),
    MatrixModule.blockCharacterPi πH hπH hlinH z = 0 → IsNilpotent z)
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
-- Two full copies of the splitting data of (6.14), one for `H` and one for `C_G(Q)`; the
-- ambient `G` only supplies the subgroups, so its own splitting data is not in play.
omit [DecidableEq (ConjClasses G)] [Invertible (Nat.card G : K)] [Fintype (ConjClasses G)] in
set_option linter.unusedFintypeInType false in
open scoped Classical in
/-- **`e_{b_0}^H(g) = e_{b_0}^{C_G(Q)}(g)`** for `g ∈ C_G(Q)`, when `Q C_G(Q) ≤ H`.

Identical to `coeff_principalBlock_eq_centralizer` with `G` replaced by `H`: Külshammer's formula
holds in `H` just as in `G` (it involves no subgroup at all), and the two counts it compares are
again seen by `Q` only through `C_G(Q)` (`eq_of_card_pRegular_mul_eq_intermediate`). -/
theorem coeff_principalBlock_eq_centralizer_intermediate [Fact p.Prime]
    (hp : p.Prime) (hQ : IsPGroup p ↥Q) (hQH : Q ≤ H)
    (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    [Fintype (MatrixModule.Block πH hπH hlinH)] [Fintype (MatrixModule.Block πC hπC hlinC)]
    (SH : Sylow p ↥H) (SC : Sylow p ↥(Subgroup.centralizer (Q : Set G)))
    (g : ↥(Subgroup.centralizer (Q : Set G)))
    {FH : MatrixModule.Block πH hπH hlinH → Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 ↥H)}
    {F'H : MatrixModule.Block πH hπH hlinH →
      Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) ↥H)}
    (hidemH : ∀ B, IsIdempotentElem (FH B))
    (hfH : ∀ B, MonoidAlgebra.mapRingHom ↥H (residue 𝒪) ((FH B : MonoidAlgebra 𝒪 ↥H))
      = ((F'H B : MonoidAlgebra (ResidueField 𝒪) ↥H)))
    (hBH : ∀ B, MatrixModule.blockCharacterPi πH hπH hlinH (F'H B) = Pi.single B 1)
    (hweakH : ∀ B : MatrixModule.Block πH hπH hlinH, ∀ x : ↥(SH : Subgroup ↥H),
        (x : ↥H) ≠ 1 →
      ∑ i ∈ Finset.univ.filter (fun i => blockOfIrr eH hπH hlinH hnilH i = B),
        (wedderburnRepresentation eH i).character (⟨(g : G), hCH g.2⟩ : ↥H)⁻¹
          * (wedderburnRepresentation eH i).character (x : ↥H) = 0)
    (hvanishH : ∀ B : MatrixModule.Block πH hπH hlinH,
      B ≠ principalBlock πH hπH hlinH hnilH →
      MatrixModule.blockCharacter πH hπH hlinH B
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
    ((F'H (principalBlock πH hπH hlinH hnilH) :
        MonoidAlgebra (ResidueField 𝒪) ↥H)).coeff (⟨(g : G), hCH g.2⟩ : ↥H)
      = ((FC' (principalBlock πC hπC hlinC hnilC) :
          MonoidAlgebra (ResidueField 𝒪) ↥(Subgroup.centralizer (Q : Set G)))).coeff g := by
  classical
  exact eq_of_card_pRegular_mul_eq_intermediate (k := ResidueField 𝒪) hp hQ hQH hCH g
    (card_pRegular_mul_coeff_principalBlock eH hπH hlinH hnilH SH ⟨(g : G), hCH g.2⟩
      hidemH hfH hBH hweakH hvanishH)
    (card_pRegular_mul_coeff_principalBlock eC hπC hlinC hnilC SC g
      hidemC hfC hBC hweakC hvanishC)

end IntermediateCoeff

/-! ### The converse of the third main theorem for `H = C_G(Q)` -/

section Converse

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] {p : ℕ} [Fact p.Prime] [CharP k p]
variable {Q : Subgroup G} [Fintype ↥(Subgroup.centralizer (Q : Set G))]
  [DecidablePred fun g : G => g ∈ Subgroup.centralizer (Q : Set G)]

omit [Fintype G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] [Fact p.Prime]
  [CharP k p] in
/-- **`Br_Q(x) = y`** as soon as `x` and `y` have the same coefficients on `C_G(Q)`: for
`H = C_G(Q)` the Brauer homomorphism is exactly the restriction of the support to `H`. -/
theorem brauerTrunc_eq_of_coeff_eq (x : MonoidAlgebra k G)
    (y : MonoidAlgebra k ↥(Subgroup.centralizer (Q : Set G)))
    (h : ∀ g : ↥(Subgroup.centralizer (Q : Set G)), x.coeff (g : G) = y.coeff g) :
    brauerTrunc Q (Subgroup.centralizer (Q : Set G)) x = y := by
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun g => ?_)
  rw [coeff_brauerTrunc, if_pos g.2]
  exact h g

variable {ιC : Type*} [Finite ιC] {nnC : ιC → Type*} [∀ i, Fintype (nnC i)]
  [∀ i, DecidableEq (nnC i)] [∀ i, Nonempty (nnC i)]
variable (πC : MonoidAlgebra k ↥(Subgroup.centralizer (Q : Set G)) →+*
    ∀ j, Matrix (nnC j) (nnC j) k)
  (hπC : Function.Surjective πC)
  (hlinC : ∀ (c : k) (a : MonoidAlgebra k ↥(Subgroup.centralizer (Q : Set G))),
    πC (c • a) = c • πC a)
  (hnilC : ∀ z : Subalgebra.center k (MonoidAlgebra k ↥(Subgroup.centralizer (Q : Set G))),
    MatrixModule.blockCharacterPi πC hπC hlinC z = 0 → IsNilpotent z)
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable (πG : MonoidAlgebra k G →+* ∀ j, Matrix (nnG j) (nnG j) k)
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : k) (a : MonoidAlgebra k G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center k (MonoidAlgebra k G),
    MatrixModule.blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

-- keep the `Pi.single` hypotheses in the same (classical) decidability shape as (6.14)
omit [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] in
open scoped Classical in
/-- **The converse half of Brauer's third main theorem** for `H = C_G(Q)`: a block `b` of
`C_G(Q)` whose induced central character `λ_b ∘ Br_Q` names the principal block of `G` *is* the
principal block of `C_G(Q)`.

This is the direction the Brauer–Suzuki argument uses, and Külshammer's route reaches it without
Okuyama's argument: `Br_Q(e_{B_0}) = e_{b_0}` (`hcoeff`, supplied by
`coeff_principalBlock_eq_centralizer`) turns the induced central character into
`λ_b(e_{b_0}) = δ_{b b_0}`, while `b^G = B_0` forces it to be `λ_{B_0}(e_{B_0}) = 1`.

⚠ The hypothesis is phrased on `blockOfCentralCharacter (λ_b ∘ Br_Q)` rather than on
`inducedBlockOfNormalizer`, so that **no abelianness of `Q` is needed**: identifying
`λ_b ∘ Br_Q` with Navarro's `λ_b^G` is (4.14), which asks for `Q C_G(Q) ≤ H` and hence — with
`H = C_G(Q)` — for `Q ≤ C_G(Q)`.  That identification is only needed to *read* the hypothesis as
`b^G = B_0`; see `eq_principalBlock_of_inducedBlockOfNormalizer_eq`. -/
theorem eq_principalBlock_of_blockOfCentralCharacter_eq (hQ : IsPGroup p ↥Q)
    {F' : MatrixModule.Block πG hπG hlinG → Subalgebra.center k (MonoidAlgebra k G)}
    {FC' : MatrixModule.Block πC hπC hlinC →
      Subalgebra.center k (MonoidAlgebra k ↥(Subgroup.centralizer (Q : Set G)))}
    (hB : ∀ B, MatrixModule.blockCharacterPi πG hπG hlinG (F' B) = Pi.single B 1)
    (hBC : ∀ B, MatrixModule.blockCharacterPi πC hπC hlinC (FC' B) = Pi.single B 1)
    (hcoeff : ∀ g : ↥(Subgroup.centralizer (Q : Set G)),
      ((F' (principalBlock πG hπG hlinG hnilG) : MonoidAlgebra k G)).coeff (g : G)
        = ((FC' (principalBlock πC hπC hlinC hnilC) :
            MonoidAlgebra k ↥(Subgroup.centralizer (Q : Set G)))).coeff g)
    (b : MatrixModule.Block πC hπC hlinC)
    (hind : MatrixModule.blockOfCentralCharacter πG hπG hlinG hnilG
        (inducedCentralCharacterAlgHom πC hπC hlinC hQ le_rfl
          (Subgroup.centralizer_le_normalizer _) b)
      = principalBlock πG hπG hlinG hnilG) :
    b = principalBlock πC hπC hlinC hnilC := by
  classical
  -- `Br_Q(e_{B_0}) = e_{b_0}`
  have hbr : brauerCenterHom Q (Subgroup.centralizer (Q : Set G)) hQ le_rfl
        (Subgroup.centralizer_le_normalizer _) (F' (principalBlock πG hπG hlinG hnilG))
      = FC' (principalBlock πC hπC hlinC hnilC) :=
    Subtype.ext (by
      rw [coe_brauerCenterHom_apply]
      exact brauerTrunc_eq_of_coeff_eq _ _ hcoeff)
  -- `b^G = B_0` means `λ_{B_0} = λ_b ∘ Br_Q`
  have hchar : MatrixModule.blockCharacter πG hπG hlinG (principalBlock πG hπG hlinG hnilG)
      = inducedCentralCharacterAlgHom πC hπC hlinC hQ le_rfl
          (Subgroup.centralizer_le_normalizer _) b := by
    rw [← hind]
    exact MatrixModule.blockCharacter_blockOfCentralCharacter πG hπG hlinG hnilG _
  -- evaluate at `e_{B_0}`
  have heval := DFunLike.congr_fun hchar (F' (principalBlock πG hπG hlinG hnilG))
  have hL : MatrixModule.blockCharacter πG hπG hlinG (principalBlock πG hπG hlinG hnilG)
      (F' (principalBlock πG hπG hlinG hnilG)) = 1 := by
    rw [← MatrixModule.blockCharacterPi_apply, hB, Pi.single_eq_same]
  have hR : inducedCentralCharacterAlgHom πC hπC hlinC hQ le_rfl
        (Subgroup.centralizer_le_normalizer _) b (F' (principalBlock πG hπG hlinG hnilG))
      = if b = principalBlock πC hπC hlinC hnilC then (1 : k) else 0 := by
    change MatrixModule.blockCharacter πC hπC hlinC b
      (brauerCenterHom Q (Subgroup.centralizer (Q : Set G)) hQ le_rfl
        (Subgroup.centralizer_le_normalizer _)
        (F' (principalBlock πG hπG hlinG hnilG))) = _
    rw [hbr, ← MatrixModule.blockCharacterPi_apply, hBC, Pi.single_apply]
  rw [hL, hR] at heval
  by_contra hne
  rw [if_neg hne] at heval
  exact one_ne_zero heval

-- keep the `Pi.single` hypotheses in the same (classical) decidability shape as (6.14)
open scoped Classical in
/-- **The converse half of Brauer's third main theorem** in Navarro's own reading `b^G = B_0`.

`inducedBlockOfNormalizer` is by definition the block named by `λ_b ∘ Br_Q`, so this is
`eq_principalBlock_of_blockOfCentralCharacter_eq` verbatim; the extra hypothesis `hQab` is what
Navarro's `Q C_G(Q) ≤ H ≤ N_G(Q)` becomes at `H = C_G(Q)`, and it is used only to know that
`λ_b ∘ Br_Q` really is the induced central character (Navarro (4.14)). -/
theorem eq_principalBlock_of_inducedBlockOfNormalizer_eq
    (hQ : IsPGroup p ↥Q) (hQab : Q ≤ Subgroup.centralizer (Q : Set G))
    {F' : MatrixModule.Block πG hπG hlinG → Subalgebra.center k (MonoidAlgebra k G)}
    {FC' : MatrixModule.Block πC hπC hlinC →
      Subalgebra.center k (MonoidAlgebra k ↥(Subgroup.centralizer (Q : Set G)))}
    (hB : ∀ B, MatrixModule.blockCharacterPi πG hπG hlinG (F' B) = Pi.single B 1)
    (hBC : ∀ B, MatrixModule.blockCharacterPi πC hπC hlinC (FC' B) = Pi.single B 1)
    (hcoeff : ∀ g : ↥(Subgroup.centralizer (Q : Set G)),
      ((F' (principalBlock πG hπG hlinG hnilG) : MonoidAlgebra k G)).coeff (g : G)
        = ((FC' (principalBlock πC hπC hlinC hnilC) :
            MonoidAlgebra k ↥(Subgroup.centralizer (Q : Set G)))).coeff g)
    (b : MatrixModule.Block πC hπC hlinC)
    (hind : inducedBlockOfNormalizer πC hπC hlinC πG hπG hlinG hnilG hQ hQab le_rfl
        (Subgroup.centralizer_le_normalizer _) b
      = principalBlock πG hπG hlinG hnilG) :
    b = principalBlock πC hπC hlinC hnilC :=
  eq_principalBlock_of_blockOfCentralCharacter_eq πC hπC hlinC hnilC πG hπG hlinG hnilG hQ
    hB hBC hcoeff b hind

end Converse

/-! ### The converse of the third main theorem for a general intermediate subgroup -/

section ConverseIntermediate

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] {p : ℕ} [Fact p.Prime] [CharP k p]
variable {Q H : Subgroup G} [Fintype ↥H] [DecidableEq (ConjClasses ↥H)]
  [Fintype (ConjClasses ↥H)]
  [DecidablePred fun g : G => g ∈ Subgroup.centralizer (Q : Set G)]
variable {ιH : Type*} [Finite ιH] {nnH : ιH → Type*} [∀ i, Fintype (nnH i)]
  [∀ i, DecidableEq (nnH i)] [∀ i, Nonempty (nnH i)]
variable (πH : MonoidAlgebra k ↥H →+* ∀ j, Matrix (nnH j) (nnH j) k)
  (hπH : Function.Surjective πH)
  (hlinH : ∀ (c : k) (a : MonoidAlgebra k ↥H), πH (c • a) = c • πH a)
  (hnilH : ∀ z : Subalgebra.center k (MonoidAlgebra k ↥H),
    MatrixModule.blockCharacterPi πH hπH hlinH z = 0 → IsNilpotent z)
variable {ιG : Type*} [Finite ιG] {nnG : ιG → Type*} [∀ j, Fintype (nnG j)]
  [∀ j, DecidableEq (nnG j)] [∀ j, Nonempty (nnG j)]
variable (πG : MonoidAlgebra k G →+* ∀ j, Matrix (nnG j) (nnG j) k)
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : k) (a : MonoidAlgebra k G), πG (c • a) = c • πG a)
  (hnilG : ∀ z : Subalgebra.center k (MonoidAlgebra k G),
    MatrixModule.blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)

-- keep the `Pi.single` hypotheses in the same (classical) decidability shape as (6.14);
-- the class-sum expansion of `Z(kH)` needs `cl(H)` finite and decidable, which the statement
-- itself does not mention
omit [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open scoped Classical in
/-- **The converse half of Brauer's third main theorem**, for a general intermediate subgroup
`Q C_G(Q) ≤ H ≤ N_G(Q)`: a block `b` of `H` whose induced central character `λ_b ∘ Br_Q` names
the principal block of `G` is the principal block of `H`.

Same three lines as the `H = C_G(Q)` case, with one extra ingredient.  There
`Br_Q(e_{B_0(G)}) = e_{b_0}` *on the nose*; here `e_{B_0(H)}` need not be supported on `C_G(Q)`,
so the two agree only **on `C_G(Q)`** (`hcoeff`, supplied by
`coeff_principalBlock_eq_centralizer` together with
`coeff_principalBlock_eq_centralizer_intermediate`).  That is enough, because a block character
of `H` only sees the coefficients on `C_G(Q)` — Navarro (4.7) in `H`-class form
(`blockCharacter_eq_of_coeff_eq_on_centralizer`). -/
theorem eq_principalBlock_of_blockOfCentralCharacter_eq_intermediate
    (hQ : IsPGroup p ↥Q) (hQH : Q ≤ H)
    (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Q : Set G))
    {F' : MatrixModule.Block πG hπG hlinG → Subalgebra.center k (MonoidAlgebra k G)}
    {F'H : MatrixModule.Block πH hπH hlinH → Subalgebra.center k (MonoidAlgebra k ↥H)}
    (hB : ∀ B, MatrixModule.blockCharacterPi πG hπG hlinG (F' B) = Pi.single B 1)
    (hBH : ∀ B, MatrixModule.blockCharacterPi πH hπH hlinH (F'H B) = Pi.single B 1)
    (hcoeff : ∀ h : ↥H, (h : G) ∈ Subgroup.centralizer (Q : Set G) →
      ((F' (principalBlock πG hπG hlinG hnilG) : MonoidAlgebra k G)).coeff (h : G)
        = ((F'H (principalBlock πH hπH hlinH hnilH) : MonoidAlgebra k ↥H)).coeff h)
    (b : MatrixModule.Block πH hπH hlinH)
    (hind : MatrixModule.blockOfCentralCharacter πG hπG hlinG hnilG
        (inducedCentralCharacterAlgHom πH hπH hlinH hQ hCH hHN b)
      = principalBlock πG hπG hlinG hnilG) :
    b = principalBlock πH hπH hlinH hnilH := by
  classical
  -- `b^G = B_0(G)` means `λ_{B_0(G)} = λ_b ∘ Br_Q`
  have hchar : MatrixModule.blockCharacter πG hπG hlinG (principalBlock πG hπG hlinG hnilG)
      = inducedCentralCharacterAlgHom πH hπH hlinH hQ hCH hHN b := by
    rw [← hind]
    exact MatrixModule.blockCharacter_blockOfCentralCharacter πG hπG hlinG hnilG _
  have heval := DFunLike.congr_fun hchar (F' (principalBlock πG hπG hlinG hnilG))
  have hL : MatrixModule.blockCharacter πG hπG hlinG (principalBlock πG hπG hlinG hnilG)
      (F' (principalBlock πG hπG hlinG hnilG)) = 1 := by
    rw [← MatrixModule.blockCharacterPi_apply, hB, Pi.single_eq_same]
  -- `Br_Q(e_{B_0(G)})` and `e_{B_0(H)}` agree on `C_G(Q)`, which is all `λ_b` sees
  have hR : inducedCentralCharacterAlgHom πH hπH hlinH hQ hCH hHN b
        (F' (principalBlock πG hπG hlinG hnilG))
      = if b = principalBlock πH hπH hlinH hnilH then (1 : k) else 0 := by
    change MatrixModule.blockCharacter πH hπH hlinH b
      (brauerCenterHom Q H hQ hCH hHN (F' (principalBlock πG hπG hlinG hnilG))) = _
    rw [blockCharacter_eq_of_coeff_eq_on_centralizer (P := Q) hπH hlinH hQ hQH hHN b
        (w := F'H (principalBlock πH hπH hlinH hnilH))
        (fun h hh => by
          rw [coe_brauerCenterHom_apply, coeff_brauerTrunc, if_pos hh]
          exact hcoeff h hh),
      ← MatrixModule.blockCharacterPi_apply, hBH, Pi.single_apply]
  rw [hL, hR] at heval
  by_contra hne
  rw [if_neg hne] at heval
  exact one_ne_zero heval

-- keep the `Pi.single` hypotheses in the same (classical) decidability shape as (6.14)
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open scoped Classical in
/-- **Brauer's third main theorem, converse half, in Navarro's own reading `b^G = B_0`**, for
`Q C_G(Q) ≤ H ≤ N_G(Q)`.

`inducedBlockOfNormalizer` is by definition the block named by `λ_b ∘ Br_Q`, so this is
`eq_principalBlock_of_blockOfCentralCharacter_eq_intermediate` verbatim. -/
theorem eq_principalBlock_of_inducedBlockOfNormalizer_eq_intermediate
    (hQ : IsPGroup p ↥Q) (hQH : Q ≤ H)
    (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Q : Set G))
    {F' : MatrixModule.Block πG hπG hlinG → Subalgebra.center k (MonoidAlgebra k G)}
    {F'H : MatrixModule.Block πH hπH hlinH → Subalgebra.center k (MonoidAlgebra k ↥H)}
    (hB : ∀ B, MatrixModule.blockCharacterPi πG hπG hlinG (F' B) = Pi.single B 1)
    (hBH : ∀ B, MatrixModule.blockCharacterPi πH hπH hlinH (F'H B) = Pi.single B 1)
    (hcoeff : ∀ h : ↥H, (h : G) ∈ Subgroup.centralizer (Q : Set G) →
      ((F' (principalBlock πG hπG hlinG hnilG) : MonoidAlgebra k G)).coeff (h : G)
        = ((F'H (principalBlock πH hπH hlinH hnilH) : MonoidAlgebra k ↥H)).coeff h)
    (b : MatrixModule.Block πH hπH hlinH)
    (hind : inducedBlockOfNormalizer πH hπH hlinH πG hπG hlinG hnilG hQ hQH hCH hHN b
      = principalBlock πG hπG hlinG hnilG) :
    b = principalBlock πH hπH hlinH hnilH :=
  eq_principalBlock_of_blockOfCentralCharacter_eq_intermediate πH hπH hlinH hnilH πG hπG hlinG
    hnilG hQ hQH hCH hHN hB hBH hcoeff b hind

end ConverseIntermediate

end OddOrder.RepresentationTheory.Modular
