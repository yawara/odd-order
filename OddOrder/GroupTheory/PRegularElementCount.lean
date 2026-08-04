/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import OddOrder.GroupTheory.PRegularElement

/-!
# The number of `p`-regular elements is prime to `p`

`|G⁰| ≢ 0 (mod p)`, where `G⁰` is the set of elements of order prime to `p`.

The proof is two steps and uses no character theory:

* a Sylow `p`-subgroup `P` acts on `G⁰` by conjugation, so `|G⁰| ≡ |G⁰ ∩ C_G(P)| (mod p)`;
* in `C := C_G(P)` every `p`-element lies in `P` — a `p`-element of `C` normalises `P`, so it
  generates a `p`-group together with `P`, and `P` is a *maximal* `p`-subgroup — while `P ∩ C`
  is central in `C` by the definition of the centraliser.  Hence `x ↦ x_{p'}` identifies `C⁰`
  with the coset space `C / (P ∩ C)`, and `P ∩ C` is a Sylow `p`-subgroup of `C`, so that index
  is prime to `p`.

In character-theoretic terms this says that `1_G` has height zero in the principal block:
Navarro's `[1̃_G, 1_G] = |G⁰| / |G|_{p'}` is a unit at `p`.  Proving it directly avoids the
apparatus of Navarro Chapter 3 (`~` functions, Brauer's characterisation of characters,
valuations) at this point of the development.

## Main results

* `OddOrder.GroupTheory.card_isPRegular_modEq_centralizer` — `|G⁰| ≡ |G⁰ ∩ C_G(P)| (mod p)`
* `OddOrder.GroupTheory.card_isPRegular_eq_index` — `|C⁰| = [C : Q]` when every `p`-element of
  `C` lies in the central `p`-subgroup `Q`
* `OddOrder.GroupTheory.not_dvd_card_isPRegular` — **`p ∤ |G⁰|`**
-/

namespace OddOrder.GroupTheory

open MulAction

variable {G : Type*} [Group G] {p : ℕ}

/-- Every element of a `p`-subgroup is a `p`-element. -/
theorem isPElement_of_mem_of_isPGroup [Fact p.Prime] {H : Subgroup G} (hH : IsPGroup p ↥H)
    {x : G} (hx : x ∈ H) : IsPElement p x :=
  isPElement_coe_iff.mpr (IsPGroup.iff_orderOf.mp hH ⟨x, hx⟩)

/-- The `p`-regular elements of `G`, as a type. -/
abbrev PRegularCarrier (p : ℕ) (G : Type*) [Group G] : Type _ := {g : G // IsPRegular p g}

/-- **A subgroup acts on the `p`-regular elements by conjugation.** -/
instance instMulActionPRegularCarrier {P : Subgroup G} : MulAction ↥P (PRegularCarrier p G) where
  smul u g := ⟨(u : G) * (g : G) * (u : G)⁻¹, g.2.conj (u : G)⟩
  one_smul g := Subtype.ext (by
    change ((1 : ↥P) : G) * (g : G) * (((1 : ↥P) : G))⁻¹ = (g : G)
    rw [OneMemClass.coe_one, one_mul, inv_one, mul_one])
  mul_smul u v g := Subtype.ext (by
    change ((u * v : ↥P) : G) * (g : G) * (((u * v : ↥P) : G))⁻¹
      = (u : G) * ((v : G) * (g : G) * (v : G)⁻¹) * (u : G)⁻¹
    push_cast
    group)

theorem coe_smul_pRegularCarrier {P : Subgroup G} (u : ↥P) (g : PRegularCarrier p G) :
    ((u • g : PRegularCarrier p G) : G) = (u : G) * (g : G) * (u : G)⁻¹ := rfl

/-- The `p`-regular elements fixed by `P` are those centralising `P`. -/
theorem mem_fixedPoints_pRegularCarrier_iff {P : Subgroup G} (g : PRegularCarrier p G) :
    g ∈ fixedPoints ↥P (PRegularCarrier p G)
      ↔ (g : G) ∈ Subgroup.centralizer (P : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h u hu
    have hg := congrArg Subtype.val (h ⟨u, hu⟩)
    rw [coe_smul_pRegularCarrier] at hg
    calc u * (g : G) = u * (g : G) * u⁻¹ * u := by group
      _ = (g : G) * u := by rw [hg]
  · intro h u
    refine Subtype.ext ?_
    rw [coe_smul_pRegularCarrier, h (u : G) u.2]
    group

/-- **`|G⁰| ≡ |G⁰ ∩ C_G(P)| (mod p)`** for a `p`-subgroup `P`: the orbits of `P` acting by
conjugation have `p`-power size, and the fixed points are the `p`-regular elements centralising
`P`. -/
theorem card_isPRegular_modEq_centralizer [Finite G] (hp : p.Prime) {P : Subgroup G}
    (hP : IsPGroup p ↥P) :
    Nat.card (PRegularCarrier p G)
      ≡ Nat.card {g : G // IsPRegular p g ∧ g ∈ Subgroup.centralizer (P : Set G)} [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (fixedPoints ↥P (PRegularCarrier p G))
      = Nat.card {g : G // IsPRegular p g ∧ g ∈ Subgroup.centralizer (P : Set G)} :=
    Nat.card_congr
      ((Equiv.subtypeEquivRight fun g => mem_fixedPoints_pRegularCarrier_iff g).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _))
  rw [← hcard]
  exact hP.card_modEq_card_fixedPoints _

/-- **`|C⁰| = [C : Q]`** when `Q` is a central `p`-subgroup of `C` containing every `p`-element
of `C`.

The bijection sends a `p`-regular element to its coset.  It is injective because a difference
`y₁⁻¹y₂ ∈ Q` is the `p`-part of the `p`-regular element `y₂ = y₁ · (y₁⁻¹y₂)`, hence trivial; it
is surjective because `x` and `x_{p'}` differ by `x_p ∈ Q`. -/
theorem card_isPRegular_eq_index {C : Type*} [Group C] [Finite C] (hp : p.Prime) {Q : Subgroup C}
    (hQp : ∀ q ∈ Q, IsPElement p q) (hQcentral : ∀ q ∈ Q, ∀ c : C, Commute q c)
    (hQall : ∀ x : C, IsPElement p x → x ∈ Q) :
    Nat.card (PRegularCarrier p C) = Q.index := by
  change Nat.card (PRegularCarrier p C) = Nat.card (C ⧸ Q)
  refine Nat.card_congr (Equiv.ofBijective (fun y => (QuotientGroup.mk (y : C) : C ⧸ Q)) ⟨?_, ?_⟩)
  · rintro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ h
    have hmem : y₁⁻¹ * y₂ ∈ Q := QuotientGroup.eq.mp h
    have hcomm : Commute (y₁⁻¹ * y₂) y₁ := hQcentral _ hmem _
    have hg : y₁ * (y₁⁻¹ * y₂) = y₂ := by group
    have hq : y₁⁻¹ * y₂ = pPart p y₂ :=
      (eq_pPart_of_commute hp hcomm (hQp _ hmem) hy₁ hg).1
    rw [pPart_eq_one_of_isPRegular hp hy₂] at hq
    exact Subtype.ext (inv_mul_eq_one.mp hq)
  · refine Quotient.ind fun x => ?_
    refine ⟨⟨pRegularPart p x, isPRegular_pRegularPart hp (isOfFinOrder_of_finite x)⟩, ?_⟩
    refine QuotientGroup.eq.mpr ?_
    have hx : (pRegularPart p x)⁻¹ * x = pPart p x := by
      rw [inv_mul_eq_iff_eq_mul]
      exact (pRegularPart_mul_pPart hp (isOfFinOrder_of_finite x)).symm
    rw [hx]
    exact hQall _ (isPElement_pPart hp x)

/-- **`p ∤ |G⁰|`**: the number of `p`-regular elements of a finite group is prime to `p`. -/
theorem not_dvd_card_isPRegular [Finite G] (hp : p.Prime) :
    ¬ p ∣ Nat.card (PRegularCarrier p G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  set C : Subgroup G := Subgroup.centralizer ((P : Subgroup G) : Set G) with hC
  -- conjugation by an element of `C` is the identity on `P`
  have hconj : ∀ x : ↥C, ∀ k ∈ (P : Subgroup G), (x : G) * k * (x : G)⁻¹ = k := by
    intro x k hk
    rw [← (Subgroup.mem_centralizer_iff.mp x.2) k hk]
    group
  -- (1) every `p`-element of `C` lies in `P`: it normalises `P`, and `P` is a maximal `p`-group
  have hmemP : ∀ x : ↥C, IsPElement p x → (x : G) ∈ (P : Subgroup G) := by
    intro x hx
    have hxnorm : (x : G) ∈ Subgroup.normalizer (P : Subgroup G) := by
      refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => ?_, fun hh => ?_⟩
      · rw [hconj x h hh]; exact hh
      · have hcm := (Subgroup.mem_centralizer_iff.mp x.2) _ hh
        have h2 : (x : G) * h = (x : G) * ((x : G) * h * (x : G)⁻¹) := by
          rw [← hcm]; group
        rw [mul_left_cancel h2]
        exact hh
    have hzp : Subgroup.zpowers (x : G) ≤ Subgroup.normalizer (P : Subgroup G) :=
      Subgroup.zpowers_le.mpr hxnorm
    have hpg : IsPGroup p ↥((P : Subgroup G) ⊔ Subgroup.zpowers (x : G)) :=
      IsPGroup.to_sup_of_normal_left' P.isPGroup'
        (IsPGroup.of_card (n := (isPElement_coe_iff.mpr hx).choose)
          (by rw [Nat.card_zpowers]; exact (isPElement_coe_iff.mpr hx).choose_spec)) hzp
    have heq := P.is_maximal' hpg le_sup_left
    have hle : Subgroup.zpowers (x : G) ≤ (P : Subgroup G) ⊔ Subgroup.zpowers (x : G) :=
      le_sup_right
    have hmem := hle (Subgroup.mem_zpowers (x : G))
    rwa [heq] at hmem
  -- (2) `Q := P ∩ C` is central in `C` and contains every `p`-element of `C`
  set Q : Subgroup ↥C := (P : Subgroup G).subgroupOf C with hQdef
  have hQmem : ∀ q : ↥C, q ∈ Q ↔ (q : G) ∈ (P : Subgroup G) := fun _ =>
    Subgroup.mem_subgroupOf
  have hQp : ∀ q ∈ Q, IsPElement p q := fun q hq =>
    isPElement_coe_iff.mp (isPElement_of_mem_of_isPGroup P.isPGroup' ((hQmem q).mp hq))
  have hQcentral : ∀ q ∈ Q, ∀ c : ↥C, Commute q c := fun q hq c =>
    Subtype.ext (by
      push_cast
      exact (Subgroup.mem_centralizer_iff.mp c.2) (q : G) ((hQmem q).mp hq))
  have hQall : ∀ x : ↥C, IsPElement p x → x ∈ Q := fun x hx => (hQmem x).mpr (hmemP x hx)
  -- (3) `Q` is a Sylow `p`-subgroup of `C`, so its index is prime to `p`
  have hQpg : IsPGroup p ↥Q := IsPGroup.iff_orderOf.mpr fun q =>
    isPElement_coe_iff.mp (hQp (q : ↥C) q.2)
  obtain ⟨S, hS⟩ := hQpg.exists_le_sylow
  have hSQ : (S : Subgroup ↥C) ≤ Q := fun s hs =>
    hQall s (isPElement_of_mem_of_isPGroup S.isPGroup' hs)
  have hQS : Q = (S : Subgroup ↥C) := le_antisymm hS hSQ
  have hindex : ¬ p ∣ Q.index := by rw [hQS]; exact S.not_dvd_index
  -- (4) assemble
  have hmod := card_isPRegular_modEq_centralizer (G := G) (P := (P : Subgroup G)) hp P.isPGroup'
  have hcong : Nat.card {g : G // IsPRegular p g ∧ g ∈ C} = Nat.card (PRegularCarrier p ↥C) :=
    Nat.card_congr <|
      (Equiv.subtypeEquivRight fun _ => and_comm).trans <|
        (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ C) (IsPRegular p)).symm.trans <|
          Equiv.subtypeEquivRight fun _ => isPRegular_coe_iff
  rw [hcong, card_isPRegular_eq_index hp hQp hQcentral hQall] at hmod
  intro hdvd
  exact hindex (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)))

end OddOrder.GroupTheory
