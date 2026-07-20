/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import OddOrder.GroupTheory.PiElementDecomposition

/-!
# Suzuki 2-groups

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
79--96, p. 79.  See also T. Peterfalvi, *Character Theory for the Odd Order
Theorem*, Appendix III, Definition 1, p. 141.

This source-neutral leaf contains the definition-level API shared by Higman’s
classification, Peterfalvi’s Appendix III restatement, and concrete groups
whose root subgroups are Suzuki 2-groups.  The paper-specific classification
proof lives under `OddOrder.Higman.Suzuki2Groups`.
-/

namespace OddOrder.GroupTheory.Suzuki2Group

variable {P : Type*} [Group P]

/-- The nonidentity involutions of a group. -/
def involutions (P : Type*) [Group P] : Set P :=
  {x | x ^ 2 = 1 ∧ x ≠ 1}

/-- A subgroup of the automorphism group acts transitively on the involutions
when every ordered pair of involutions is connected by an automorphism.

This is the action hypothesis in Higman's original definition of a Suzuki
`2`-group.  Regularity is a later conclusion of the classification. -/
def ActsTransitivelyOnInvolutions (A : Subgroup (MulAut P)) : Prop :=
  ∀ x ∈ involutions P, ∀ y ∈ involutions P,
    ∃ a : ↥A, (a : MulAut P) x = y

/-- A subgroup of the automorphism group acts regularly on the involutions
when every ordered pair of involutions is connected by a unique automorphism. -/
def ActsRegularlyOnInvolutions (A : Subgroup (MulAut P)) : Prop :=
  ∀ x ∈ involutions P, ∀ y ∈ involutions P,
    ∃! a : ↥A, (a : MulAut P) x = y

/-- Every regular action on the involutions is transitive. -/
theorem ActsRegularlyOnInvolutions.transitive
    {A : Subgroup (MulAut P)} (hreg : ActsRegularlyOnInvolutions A) :
    ActsTransitivelyOnInvolutions A := by
  intro x hx y hy
  obtain ⟨a, ha, _⟩ := hreg x hx y hy
  exact ⟨a, ha⟩

/-- Automorphisms preserve the set of nonidentity involutions. -/
theorem map_mem_involutions_iff (a : MulAut P) (x : P) :
    a x ∈ involutions P ↔ x ∈ involutions P := by
  simp only [involutions, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx2, hx1⟩
    constructor
    · apply a.injective
      simpa only [map_pow, map_one] using hx2
    · intro hx
      apply hx1
      simp only [hx, map_one]
  · rintro ⟨hx2, hx1⟩
    constructor
    · simpa only [map_pow, map_one] using congrArg a hx2
    · intro hax
      apply hx1
      apply a.injective
      simpa only [map_one] using hax

/-- The permutation representation of the automorphism group on the
nonidentity involutions. -/
def involutionPermHom (P : Type*) [Group P] :
    MulAut P →* Equiv.Perm ↥(involutions P) where
  toFun a := (MulAut.toPerm P a).subtypePerm fun x => map_mem_involutions_iff a x
  map_one' := by
    ext x
    rfl
  map_mul' a b := by
    ext x
    rfl

@[simp]
theorem involutionPermHom_apply_coe (a : MulAut P) (x : ↥(involutions P)) :
    ((involutionPermHom P a x : ↥(involutions P)) : P) = a x :=
  rfl

/-- If the powers of a permutation carry one point onto every point of a
finite nonempty type, the order of the permutation is the cardinality of the
type.  This includes the one-point (identity permutation) case. -/
private theorem orderOf_eq_natCard_of_zpow_transitive
    {X : Type*} [Finite X] (σ : Equiv.Perm X) (x : X)
    (htrans : ∀ y : X, ∃ n : ℤ, (σ ^ n) x = y) :
    orderOf σ = Nat.card X := by
  let evaluation : ↥(Subgroup.zpowers σ) → X := fun τ => (τ : Equiv.Perm X) x
  have hevaluation_injective : Function.Injective evaluation := by
    rintro ⟨τ, hτ⟩ ⟨υ, hυ⟩ hτυ
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hυ
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro y
    obtain ⟨n, rfl⟩ := htrans y
    change (σ ^ i) ((σ ^ n) x) = (σ ^ j) ((σ ^ n) x)
    rw [Equiv.Perm.zpow_apply_comm σ i n, Equiv.Perm.zpow_apply_comm σ j n]
    exact congrArg (σ ^ n) hτυ
  have hevaluation_surjective : Function.Surjective evaluation := by
    intro y
    obtain ⟨n, hn⟩ := htrans y
    exact ⟨⟨σ ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩⟩, hn⟩
  calc
    orderOf σ = Nat.card ↥(Subgroup.zpowers σ) := (Nat.card_zpowers σ).symm
    _ = Nat.card X :=
      Nat.card_congr
        (Equiv.ofBijective evaluation
          ⟨hevaluation_injective, hevaluation_surjective⟩)

/-- A finite cyclic automorphism group transitive on the involutions contains
a cyclic transitive subgroup whose order has no prime divisors beyond those
of the number of involutions.

This is the source-neutral actor reduction used at the start of Higman's
Lemma 11.  For a cyclic generator `g`, split `g = a * b` into its `π`- and
`π′`-parts, where `π` consists of the prime divisors of the involution count.
The permutation image of `b` has order both dividing that count and supported
outside `π`, hence is trivial.  Therefore `a` induces the same transitive
permutation as `g`.  No regularity hypothesis is used. -/
theorem exists_primeSupported_cyclic_actor
    [Finite P] (A : Subgroup (MulAut P))
    (hcyc : IsCyclic ↥A)
    (htrans : ActsTransitivelyOnInvolutions A)
    (hinv : (involutions P).Nonempty) :
    ∃ B : Subgroup (MulAut P),
      B ≤ A ∧
      IsCyclic ↥B ∧
      ActsTransitivelyOnInvolutions B ∧
      (involutions P).ncard ∣ Nat.card B ∧
      ∀ p : ℕ, p.Prime → p ∣ Nat.card B → p ∣ (involutions P).ncard := by
  classical
  obtain ⟨x, hx⟩ := hinv
  obtain ⟨g, hgen⟩ := hcyc.exists_generator
  let ρ : A →* Equiv.Perm ↥(involutions P) :=
    (involutionPermHom P).comp A.subtype
  have hgenerator_transitive (u v : ↥(involutions P)) :
      ∃ n : ℤ, (ρ g ^ n) u = v := by
    obtain ⟨c, hc⟩ := htrans u u.property v v.property
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hgen c)
    refine ⟨n, ?_⟩
    rw [← map_zpow, hn]
    apply Subtype.ext
    change (c : MulAut P) u = v
    exact hc
  have hρg : orderOf (ρ g) = (involutions P).ncard := by
    calc
      orderOf (ρ g) = Nat.card ↥(involutions P) :=
        orderOf_eq_natCard_of_zpow_transitive
          (ρ g) ⟨x, hx⟩ (hgenerator_transitive ⟨x, hx⟩)
      _ = (involutions P).ncard := Nat.card_coe_set_eq _
  let π : Set ℕ := {p | p ∣ (involutions P).ncard}
  obtain ⟨a, b, hab, -, haπ, hbπ, -, hbgen⟩ :=
    OddOrder.GroupTheory.exists_isPiElement_mul (G := A) π g
  have hρb_mem : ρ b ∈ Subgroup.zpowers (ρ g) := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hbgen
    rw [← hn, map_zpow]
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
  have hρb_dvd : orderOf (ρ b) ∣ (involutions P).ncard := by
    simpa only [hρg] using orderOf_dvd_of_mem_zpowers hρb_mem
  have hρb_one : ρ b = 1 := by
    rw [← orderOf_eq_one_iff]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hp_order_b : p ∈ (orderOf b).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hp, hpdvd.trans (orderOf_map_dvd ρ b), (orderOf_pos b).ne'⟩
    have hp_not_dvd : ¬p ∣ (involutions P).ncard := by
      have hpcomp := hbπ p hp_order_b
      change p ∉ π at hpcomp
      simpa only [π, Set.mem_setOf_eq] using hpcomp
    exact hp_not_dvd (hpdvd.trans hρb_dvd)
  have hρa : ρ a = ρ g := by
    calc
      ρ a = ρ a * ρ b := by rw [hρb_one, mul_one]
      _ = ρ (a * b) := (map_mul ρ a b).symm
      _ = ρ g := congrArg ρ hab
  let B : Subgroup (MulAut P) := Subgroup.zpowers (a : MulAut P)
  have hBA : B ≤ A := by
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact A.zpow_mem a.property n
  have hBtrans : ActsTransitivelyOnInvolutions B := by
    intro u hu v hv
    obtain ⟨n, hn⟩ :=
      hgenerator_transitive (⟨u, hu⟩ : ↥(involutions P)) ⟨v, hv⟩
    have hna : (ρ a ^ n) (⟨u, hu⟩ : ↥(involutions P)) = ⟨v, hv⟩ := by
      simpa only [hρa] using hn
    let c : B :=
      ⟨(a : MulAut P) ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩⟩
    refine ⟨c, ?_⟩
    have hna' : ρ (a ^ n) (⟨u, hu⟩ : ↥(involutions P)) = ⟨v, hv⟩ := by
      rw [map_zpow]
      exact hna
    have hna_val := congrArg Subtype.val hna'
    change (A.subtype (a ^ n)) u = v at hna_val
    have hcoe : A.subtype (a ^ n) = A.subtype a ^ n :=
      map_zpow A.subtype a n
    exact (congrArg (fun φ : MulAut P => φ u) hcoe.symm).trans hna_val
  have hcardB : Nat.card B = orderOf a := by
    calc
      Nat.card B = orderOf (a : MulAut P) := Nat.card_zpowers _
      _ = orderOf a := Subgroup.orderOf_coe a
  have hcard_dvd : (involutions P).ncard ∣ Nat.card B := by
    rw [hcardB]
    simpa only [hρa, hρg] using orderOf_map_dvd ρ a
  have hprime_support :
      ∀ p : ℕ, p.Prime → p ∣ Nat.card B → p ∣ (involutions P).ncard := by
    intro p hp hpdvd
    apply haπ p
    apply Nat.mem_primeFactors.mpr
    rw [hcardB] at hpdvd
    exact ⟨hp, hpdvd, (orderOf_pos a).ne'⟩
  exact ⟨B, hBA, inferInstance, hBtrans, hcard_dvd, hprime_support⟩

/-- A finite nontrivial `2`-group has an odd number of nonidentity
involutions. -/
theorem involutions_ncard_odd_of_isPGroup
    [Finite P] (hP : IsPGroup 2 P)
    (hinv : (involutions P).Nonempty) :
    Odd (involutions P).ncard := by
  classical
  obtain ⟨x, hx⟩ := hinv
  letI : Nontrivial P := ⟨⟨x, 1, hx.2⟩⟩
  letI : Fintype P := Fintype.ofFinite P
  let f : Function.End P := fun y => y⁻¹
  have hf2 : f ^ 2 = 1 := by
    funext y
    change (y⁻¹)⁻¹ = y
    simp
  have hmod :=
    Equiv.Perm.card_fixedPoints_modEq
      (f := f) (p := 2) (n := 1) (by simpa using hf2)
  have hcard_ne : Nat.card P ≠ 1 :=
    ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  have htwo : 2 ∣ Nat.card P :=
    hP.card_eq_or_dvd.resolve_left hcard_ne
  have hPmod : Fintype.card P % 2 = 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.dvd_iff_mod_eq_zero.mp htwo
  have hfixedMod : Fintype.card ↥(Function.fixedPoints f) % 2 = 0 := by
    rw [Nat.ModEq] at hmod
    omega
  have hfixed :
      Function.fixedPoints f = insert 1 (involutions P) := by
    ext y
    change y⁻¹ = y ↔ y = 1 ∨ (y ^ 2 = 1 ∧ y ≠ 1)
    constructor
    · intro hy
      have hy2 : y ^ 2 = 1 := by
        rw [pow_two, ← inv_eq_iff_mul_eq_one]
        exact hy
      by_cases hy1 : y = 1
      · exact Or.inl hy1
      · exact Or.inr ⟨hy2, hy1⟩
    · rintro (rfl | ⟨hy2, _⟩)
      · simp
      · rw [inv_eq_iff_mul_eq_one, ← pow_two]
        exact hy2
  have hfixedCard :
      Fintype.card ↥(Function.fixedPoints f) =
        (involutions P).ncard + 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hfixed,
      Set.ncard_insert_of_notMem]
    simp [involutions]
  rw [Nat.odd_iff]
  omega

/-- For a finite `2`-group, the prime-supported transitive cyclic actor can
be chosen to have odd order. -/
theorem exists_odd_primeSupported_cyclic_actor
    [Finite P] (hP : IsPGroup 2 P)
    (A : Subgroup (MulAut P))
    (hcyc : IsCyclic ↥A)
    (htrans : ActsTransitivelyOnInvolutions A)
    (hinv : (involutions P).Nonempty) :
    ∃ B : Subgroup (MulAut P),
      B ≤ A ∧
      IsCyclic ↥B ∧
      ActsTransitivelyOnInvolutions B ∧
      (involutions P).ncard ∣ Nat.card B ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card B → p ∣ (involutions P).ncard) ∧
      Odd (Nat.card B) := by
  obtain ⟨B, hBA, hBcyc, hBtrans, hcard_dvd, hprime_support⟩ :=
    exists_primeSupported_cyclic_actor A hcyc htrans hinv
  have hinv_odd := involutions_ncard_odd_of_isPGroup hP hinv
  have hBodd : Odd (Nat.card B) := Nat.not_even_iff_odd.mp fun hBeven =>
    hinv_odd.not_two_dvd_nat
      (hprime_support 2 Nat.prime_two (Even.two_dvd hBeven))
  exact ⟨B, hBA, hBcyc, hBtrans, hcard_dvd, hprime_support, hBodd⟩

/-- A group acting regularly on the involutions of a finite `2`-group has
odd order.

The orbit of one involution identifies the actor with the full involution
set.  Inversion pairs the remaining elements of the ambient `2`-group, so
that set has odd cardinality. -/
theorem actor_card_odd_of_regular_on_involutions
    [Finite P] (hP : IsPGroup 2 P)
    (A : Subgroup (MulAut P))
    (hreg : ActsRegularlyOnInvolutions A)
    (hinv : (involutions P).Nonempty) :
    Odd (Nat.card A) := by
  classical
  have hinvOdd := involutions_ncard_odd_of_isPGroup hP hinv
  obtain ⟨x, hx⟩ := hinv
  let orbit : A → ↥(involutions P) := fun a =>
    ⟨(a : MulAut P) x, by
      constructor
      · simpa only [map_pow, map_one] using
          congrArg (a : MulAut P) hx.1
      · intro hax
        apply hx.2
        apply (a : MulAut P).injective
        simpa only [map_one] using hax⟩
  have horbitInj : Function.Injective orbit := by
    intro a b hab
    let y : P := (a : MulAut P) x
    have hy : y ∈ involutions P := (orbit a).2
    obtain ⟨c, hc, huniq⟩ := hreg x hx y hy
    have ha : (a : MulAut P) x = y := rfl
    have hb : (b : MulAut P) x = y := by
      exact (congrArg Subtype.val hab).symm
    exact (huniq a ha).trans (huniq b hb).symm
  have horbitSurj : Function.Surjective orbit := by
    intro y
    obtain ⟨a, ha, _⟩ := hreg x hx y y.2
    exact ⟨a, Subtype.ext ha⟩
  have hcardActor : Nat.card A = (involutions P).ncard := by
    calc
      Nat.card A = Nat.card ↥(involutions P) :=
        Nat.card_congr (Equiv.ofBijective orbit ⟨horbitInj, horbitSurj⟩)
      _ = (involutions P).ncard := Nat.card_coe_set_eq _
  rwa [hcardActor]

/-- A compatibility predicate for existing consumers that package a regular
actor with a nonabelian `2`-group.

This is stronger than **Higman, Suzuki 2-groups, p. 79**, where the cyclic
actor is assumed only to act transitively on the involutions; regularity is a
conclusion of the classification.  Source-faithful proofs of that
classification therefore start from `ActsTransitivelyOnInvolutions` rather
than from this predicate.  The acting group is represented as a subgroup of
`MulAut P`, so faithfulness is built into the representation. -/
def IsSuzuki2Group (P : Type*) [Group P] : Prop :=
  IsPGroup 2 P ∧
    ¬ IsMulCommutative P ∧
    (∃ x y : P, x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y) ∧
    ∃ A : Subgroup (MulAut P), IsCyclic ↥A ∧ ActsRegularlyOnInvolutions A

end OddOrder.GroupTheory.Suzuki2Group
