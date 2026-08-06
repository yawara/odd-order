/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlockBasicSet
import OddOrder.GroupTheory.RepresentationTheory.Modular.PrincipalBlockTrivial

/-!
# The trivial character inside the basic set of Navarro (7.4)

Navarro's Brauer–Suzuki argument reads off the **first entry** of each basic-set column: on
p. 141 the columns at `t` start with `d^t_{00} = 1`, `d^t_{01} = d^t_{02} = 0`, and the column at
`y` with `d^y_{00} = 1`.  The index `0` is that of the trivial character `1_G`, and the reason is
always the same:

* the basic set `𝓑 = {ε_j χ_j⁰ : j ∈ Irr(B_0), j ≠ j₀}` of (7.4) **contains the constant function
  `1`**, namely at the index `i₀` of the trivial character (`ε_{i₀} = 1_G(t) = 1`), and
* `𝓑` is **linearly independent** on the `p`-regular classes.

So a family whose `𝓑`-expansion is the constant `1` *is* `Pi.single i₀ 1`.

The independence is `eq_zero_of_vanishing_on_pRegular_of_apply_eq_zero` (the relation lattice of
`Irr(B_0)` is one-dimensional and its generator has no zero coordinate); this file only recasts it
from "a relation supported on `Irr(B_0)` and vanishing at `j₀`" into the shape "two expansions in
`𝓑` agree", which is what the consumers want.

## Main results

* `OddOrder.RepresentationTheory.Modular.eq_zero_of_sum_principalBasicSet_eq_zero` — `𝓑` is
  independent on `G⁰`
* `OddOrder.RepresentationTheory.Modular.eq_of_sum_principalBasicSet_eq` — expansions in `𝓑` are
  unique
* `OddOrder.RepresentationTheory.Modular.principalBasicSet_eq_one_of_trivial` — `η_{i₀} = 1`
* `OddOrder.RepresentationTheory.Modular.eq_ite_of_sum_principalBasicSet_eq_one` — Navarro's
  `d^x_{00} = 1`, `d^x_{0j} = 0` (`j ≠ 0`)
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.MatrixModule
open OddOrder.RepresentationTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪] [IsIntegrallyClosed 𝒪]
  [IsAlgClosed (FractionRing 𝒪)]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [FaithfulSMul 𝒪 K]
  [Fact p.Prime] [CharP (ResidueField 𝒪) p]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] [Invertible (Nat.card G : K)] {t : G} [Fintype ↥(centralizerOf t)]
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [Fintype ι'] [∀ i, Nonempty (m i)]
variable {κ : Type*} {mG : κ → Type*} [∀ i, Fintype (mG i)] [∀ i, DecidableEq (mG i)]
  [Fintype κ] [DecidableEq κ] [∀ i, Nonempty (mG i)]
variable {ιG : Type*} {nnG : ιG → Type*} [∀ i, Fintype (nnG i)] [∀ i, DecidableEq (nnG i)]
  [Fintype ιG] [∀ i, Nonempty (nnG i)]
variable (hp : p.Prime) (hx : IsPElement p t)
  {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p ↥(centralizerOf t)))
  (e : MonoidAlgebra K ↥(centralizerOf t) ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)
  (eG : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (mG i) (mG i) K)
  {πG : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nnG j) (nnG j) (ResidueField 𝒪)}
  (hπG : Function.Surjective πG)
  (hlinG : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), πG (c • a) = c • πG a)
  {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t) →+*
    ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t)),
    π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t)))
  (hnil : ∀ z : Subalgebra.center (ResidueField 𝒪)
      (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf t)),
    blockCharacterPi π hπ hlin z = 0 → IsNilpotent z)
  (hnilG : ∀ z : Subalgebra.center (ResidueField 𝒪) (MonoidAlgebra (ResidueField 𝒪) G),
    blockCharacterPi πG hπG hlinG z = 0 → IsNilpotent z)
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p ↥(centralizerOf t)))
  {ζ : 𝒪} (hζ : ζ ^ p = 1) (hζk : residue 𝒪 ζ = 1) (hζK : algebraMap 𝒪 K ζ ≠ 1)
  (hconv : ∀ b : Block π hπ hlin,
    inducedBlockOfCentralizer t π hπ hlin πG hπG hlinG hnilG hp hx b
      = principalBlock πG hπG hlinG hnilG → b = principalBlock π hπ hlin hnil)
  {N : Subgroup ↥(centralizerOf t)} [N.Normal] (hNp : ¬ p ∣ Nat.card ↥N)
  (hquot : IsPGroup p (↥(centralizerOf t) ⧸ N)) (S : Sylow p ↥(centralizerOf t))
  {φ₀ : ι} (hφ₀ : Quotient.mk (blockSetoid π hπ hlin) φ₀ = principalBlock π hπ hlin hnil)

/-! ### The constant function `1` is a member of the basic set -/

omit [IsIntegrallyClosed 𝒪] [IsAlgClosed (FractionRing 𝒪)] [Invertible (Nat.card G : K)]
  [Fintype ↥(centralizerOf t)] [Fintype κ] in
set_option linter.unusedFintypeInType false in
open scoped Classical in
/-- **The trivial character contributes the constant function `1` to the basic set.**  Its sign is
`ε_{i₀} = 1_G(t) = 1`, and `η_{i₀}(g) = ε_{i₀} · 1_G(g) = 1`. -/
theorem principalBasicSet_eq_one_of_trivial {i₀ j₀ : κ}
    (hi₀B : blockOfIrr eG hπG hlinG hnilG i₀ = principalBlock πG hπG hlinG hnilG)
    (hi₀ : ∀ g : G, (wedderburnRepresentation eG i₀).character g = 1) (hne : i₀ ≠ j₀) (g : G) :
    principalBasicSet eG hπG hlinG hnilG t j₀ i₀ g = 1 := by
  classical
  rw [principalBasicSet, if_pos ⟨hi₀B, hne⟩, hi₀, hi₀, one_mul]

omit [Fintype G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]
  [Invertible (Nat.card G : K)] [Fintype ↥(centralizerOf t)] [Fintype κ] [DecidableEq κ]
  [∀ i, Nonempty (mG i)] in
set_option linter.unusedFintypeInType false in
/-- **The trivial character is not the discarded index.**  Navarro drops an index `j₀` with
`ε_{j₀} = -1`, and the trivial character has `ε = 1`. -/
theorem ne_of_character_involution_eq_neg_one [CharZero K] {i₀ j₀ : κ}
    (hi₀ : ∀ g : G, (wedderburnRepresentation eG i₀).character g = 1)
    (hj₀ : (wedderburnRepresentation eG j₀).character t = -1) : i₀ ≠ j₀ := by
  rintro rfl
  rw [hi₀ t] at hj₀
  exact absurd hj₀ (by norm_num)

/-! ### Independence of the basic set -/

set_option maxHeartbeats 1000000 in
-- The independence statement it recasts carries the full modular-datum chain.
set_option linter.unusedFintypeInType false in
open scoped Classical in
include hp hx hω hω' e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ in
/-- **The basic set `𝓑` of Navarro (7.4) is linearly independent on `G⁰`.**

`∑_j c_j η_j` vanishing on the `p`-regular classes forces `c_j = 0` for every `j` that actually
occurs in `𝓑` (i.e. `χ_j ∈ Irr(B_0)`, `j ≠ j₀`).  Transporting `c` through the signs turns the
hypothesis into a relation among the `χ⁰` supported on `Irr(B_0)` and vanishing at `j₀`, which is
`eq_zero_of_vanishing_on_pRegular_of_apply_eq_zero`. -/
theorem eq_zero_of_sum_principalBasicSet_eq_zero
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj t v) (ht1 : t ≠ 1)
    (hcart : cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ = 4)
    (ht : t * t = 1) {j₀ : κ}
    (hj₀ : blockOfIrr eG hπG hlinG hnilG j₀ = principalBlock πG hπG hlinG hnilG) {c : κ → K}
    (hvan : ∀ g : G, IsPRegular p g →
      (∑ j : κ, c j * principalBasicSet eG hπG hlinG hnilG t j₀ j g) = 0)
    {j : κ} (hjB : blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG)
    (hjne : j ≠ j₀) :
    c j = 0 := by
  classical
  let a : κ → K := fun l =>
    if blockOfIrr eG hπG hlinG hnilG l = principalBlock πG hπG hlinG hnilG ∧ l ≠ j₀ then
      c l * (wedderburnRepresentation eG l).character t
    else 0
  have ha : ∀ l : κ, a l
      = if blockOfIrr eG hπG hlinG hnilG l = principalBlock πG hπG hlinG hnilG ∧ l ≠ j₀ then
          c l * (wedderburnRepresentation eG l).character t
        else 0 := fun _ => rfl
  have hterm : ∀ (l : κ) (g : G),
      a l * (wedderburnRepresentation eG l).character g
        = c l * principalBasicSet eG hπG hlinG hnilG t j₀ l g := by
    intro l g
    rw [ha l, principalBasicSet]
    by_cases hl : blockOfIrr eG hπG hlinG hnilG l = principalBlock πG hπG hlinG hnilG ∧ l ≠ j₀
    · rw [if_pos hl, if_pos hl]; ring
    · rw [if_neg hl, if_neg hl, zero_mul, mul_zero]
  have hzero := eq_zero_of_vanishing_on_pRegular_of_apply_eq_zero hp hx hω e eG hπG hlinG hπ hlin
    hkerJ hnil hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ hconjall ht1 hcart ht
    (a := a)
    (fun l hl => by rw [ha l]; exact if_neg fun hc => hl hc.1)
    (fun g hg => by
      rw [Finset.sum_congr rfl fun l _ => hterm l g]; exact hvan g hg)
    hj₀ (by rw [ha j₀]; exact if_neg fun hc => hc.2 rfl)
  -- `a j = c j * ε_j` and `ε_j² = 1`
  have haj : c j * (wedderburnRepresentation eG j).character t = 0 := by
    have hj : a j = 0 := congrFun hzero j
    rwa [ha j, if_pos ⟨hjB, hjne⟩] at hj
  have hεsq := character_involution_mul_self hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil hnilG hω'
    hζ hζk hζK hconv hNp hquot S hφ₀ ht hconjall ht1 hcart hjB
  calc c j = c j * (wedderburnRepresentation eG j).character t
        * (wedderburnRepresentation eG j).character t := by rw [mul_assoc, hεsq, mul_one]
    _ = 0 := by rw [haj, zero_mul]

set_option maxHeartbeats 1000000 in
-- Same chain as the independence statement it applies to a difference.
set_option linter.unusedFintypeInType false in
open scoped Classical in
include hp hx hω hω' e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ in
/-- **Expansions in the basic set are unique.**  The difference of two families with the same
values on `G⁰` is a relation, hence zero on `𝓑`. -/
theorem eq_of_sum_principalBasicSet_eq
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj t v) (ht1 : t ≠ 1)
    (hcart : cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ = 4)
    (ht : t * t = 1) {j₀ : κ}
    (hj₀ : blockOfIrr eG hπG hlinG hnilG j₀ = principalBlock πG hπG hlinG hnilG) {c c' : κ → K}
    (hvan : ∀ g : G, IsPRegular p g →
      (∑ j : κ, c j * principalBasicSet eG hπG hlinG hnilG t j₀ j g)
        = ∑ j : κ, c' j * principalBasicSet eG hπG hlinG hnilG t j₀ j g)
    {j : κ} (hjB : blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG)
    (hjne : j ≠ j₀) :
    c j = c' j := by
  have hsub := eq_zero_of_sum_principalBasicSet_eq_zero hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil
    hnilG hω' hζ hζk hζK hconv hNp hquot S hφ₀ hconjall ht1 hcart ht hj₀
    (c := fun l => c l - c' l)
    (fun g hg => by
      rw [Finset.sum_congr rfl fun l _ => sub_mul (c l) (c' l) _, Finset.sum_sub_distrib,
        hvan g hg, sub_self])
    hjB hjne
  exact sub_eq_zero.mp hsub

set_option maxHeartbeats 1000000 in
-- Same chain as the uniqueness statement it specialises.
set_option linter.unusedFintypeInType false in
open scoped Classical in
include hp hx hω hω' e hπG hlinG hkerJ hnil hζ hζk hζK hconv hNp hquot S hφ₀ in
/-- **Navarro's "`1` in the first entry" of a basic-set column** (p. 141: `d^t_{00} = 1`,
`d^t_{01} = d^t_{02} = 0`, and `d^y_{00} = 1`).

A family whose expansion in `𝓑` is the constant function `1` is `Pi.single i₀ 1`, `i₀` being the
index of the trivial character — because `η_{i₀} = 1` is itself a member of `𝓑`.

In the "analysis at `x`" this is applied to the basic-set column of the trivial character of the
ambient group: `1_G(x y) = 1` for every `p`-regular `y ∈ C_G(x)`. -/
theorem eq_ite_of_sum_principalBasicSet_eq_one
    (hconjall : ∀ v : G, IsPElement p v → v ≠ 1 → IsConj t v) (ht1 : t ≠ 1)
    (hcart : cartanMatrix (𝒪 := 𝒪) (nn := nn) hp hω hω' hπ hlin hkerJ e φ₀ φ₀ = 4)
    (ht : t * t = 1) {j₀ : κ}
    (hj₀ : blockOfIrr eG hπG hlinG hnilG j₀ = principalBlock πG hπG hlinG hnilG) {c : κ → K}
    (hone : ∀ g : G, IsPRegular p g →
      (∑ j : κ, c j * principalBasicSet eG hπG hlinG hnilG t j₀ j g) = 1)
    {i₀ : κ} (hi₀B : blockOfIrr eG hπG hlinG hnilG i₀ = principalBlock πG hπG hlinG hnilG)
    (hi₀ : ∀ g : G, (wedderburnRepresentation eG i₀).character g = 1) (hi₀ne : i₀ ≠ j₀)
    {j : κ} (hjB : blockOfIrr eG hπG hlinG hnilG j = principalBlock πG hπG hlinG hnilG)
    (hjne : j ≠ j₀) :
    c j = if j = i₀ then 1 else 0 := by
  classical
  refine eq_of_sum_principalBasicSet_eq hp hx hω e eG hπG hlinG hπ hlin hkerJ hnil hnilG hω' hζ
    hζk hζK hconv hNp hquot S hφ₀ hconjall ht1 hcart ht hj₀
    (c' := fun l => if l = i₀ then 1 else 0) (fun g hg => ?_) hjB hjne
  rw [hone g hg, Finset.sum_congr rfl fun l _ =>
      show (if l = i₀ then (1 : K) else 0) * principalBasicSet eG hπG hlinG hnilG t j₀ l g
          = if l = i₀ then principalBasicSet eG hπG hlinG hnilG t j₀ l g else 0 by
        by_cases hl : l = i₀
        · rw [if_pos hl, if_pos hl, one_mul]
        · rw [if_neg hl, if_neg hl, zero_mul],
    Finset.sum_ite_eq' Finset.univ i₀ (principalBasicSet eG hπG hlinG hnilG t j₀ · g),
    if_pos (Finset.mem_univ i₀),
    principalBasicSet_eq_one_of_trivial eG hπG hlinG hnilG hi₀B hi₀ hi₀ne g]

end OddOrder.RepresentationTheory.Modular
