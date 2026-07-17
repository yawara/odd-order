/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.LineScalarCharacter
import OddOrder.GroupTheory.ElementaryAbelian
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Bender–Glauberman Lemma 2.7: `(ℤ/q)²` acting faithfully on `(ℤ/p)²`

Reference: Bender–Glauberman, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994),
Lemma 2.7 (pp. 16–17). Issue 3009.

Let `p`, `q` be distinct primes, `P` an elementary abelian group of order `p²`, `Q` an elementary
abelian group of order `q²`, and `Q ⊆ Aut(P)`.  Then

* **(a)** `q ∣ p − 1`, and
* **(b)** some `α ∈ Q^#` acts on `P` as a scalar `x ↦ x^r`, with `r^q ≡ 1 (mod p)` and
  `r ≢ 1 (mod p)`.

## Formulation

We render `P` as a `2`-dimensional `𝔽_p`-vector space and `Q ⊆ Aut(P)` as a **faithful**
`𝔽_p`-linear representation `ρ : Representation (ZMod p) Q P`.  This is a faithful rendering of
"`Q ⊆ Aut(P)`": the group automorphisms of an elementary abelian `p`-group are exactly `GL` over
`𝔽_p` (an automorphism is `ℤ`-linear, hence `𝔽_p`-linear since `𝔽_p = ℤ/p`), so `Aut(P) = GL₂(𝔽_p)`
and a subgroup `Q ⊆ Aut(P)` is precisely a faithful `𝔽_p`-linear action.

## Proof

The crux (`isCyclic_of_faithful_isIrreducible`) is Gorenstein Thm 3.2.3: *a finite commutative
group with a faithful irreducible representation over a field is cyclic*.  We prove it via the
annihilator: irreducibility makes `ρ.asModule` a simple `F[Q]`-module; as `F[Q]` is commutative
its annihilator `ann` is a maximal ideal and `E := F[Q] ⧸ ann` is a field (a domain).  Then
`Q ↪ E` (via `α ↦ single α 1`) by faithfulness, and a finite subgroup of a domain's units is
cyclic.

For the main result: `Q ≅ (ℤ/q)²` is **not** cyclic, so `ρ` is not irreducible; as `finrank = 2`
this gives a line `W`, and by Maschke (`|Q| = q²` coprime to `p`) a complementary line `W'`, with
`P = W ⊕ W'`.  Each line carries a scalar character `χᵢ : Q →* 𝔽_pˣ` (`LineScalarCharacter`), the
pair `(χ₁, χ₂)` is injective, and each `χᵢ α` is a `q`-th root of unity.  Since `Q` is not cyclic,
`δ := χ₁ · χ₂⁻¹ : Q → 𝔽_pˣ` is not injective, giving `α ≠ 1` with `χ₁ α = χ₂ α =: r`, and `r ≠ 1`
by faithfulness.  Then `r` has order `q`, `α` acts as `r`, and `q = orderOf r ∣ |𝔽_pˣ| = p − 1`.
-/

namespace OddOrder.RepresentationTheory

open scoped MonoidAlgebra

/-- **Gorenstein Thm 3.2.3** (the crux of BG Lemma 2.7): a finite commutative group `Q` with a
faithful *irreducible* representation over a field `F` is cyclic.

Proof: irreducibility makes `ρ.asModule` a simple `F[Q]`-module; as `F[Q]` is commutative its
annihilator `ann` is maximal, so `E := F[Q] ⧸ ann` is a field (an integral domain).  The map
`Q →* E`, `α ↦ single α 1 mod ann`, is injective because `ρ` is faithful, and a finite subgroup of
the units of a domain is cyclic. -/
theorem isCyclic_of_faithful_isIrreducible {F : Type*} [Field F] {Q : Type*} [CommGroup Q]
    [Finite Q] {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F Q V)
    [ρ.IsIrreducible] (hfaith : Function.Injective ρ) : IsCyclic Q := by
  -- `ρ.asModule` is a simple `F[Q]`-module, so its annihilator is a maximal ideal.
  haveI hsimple : IsSimpleModule F[Q] ρ.asModule := inferInstance
  set ann : Ideal F[Q] := Module.annihilator F[Q] ρ.asModule with hann
  haveI hmax : ann.IsMaximal := IsSimpleModule.annihilator_isMaximal
  -- `E := F[Q] ⧸ ann` is an integral domain (`ann` maximal ⟹ prime).
  -- The multiplicative embedding `Q ↪ E`.
  let f : Q →* (F[Q] ⧸ ann) :=
    (Ideal.Quotient.mk ann : F[Q] →+* F[Q] ⧸ ann).toMonoidHom.comp (MonoidAlgebra.of F Q)
  have hf : Function.Injective f := by
    intro α β hαβ
    -- `f α = mk (single α 1)`, so `hαβ` says `single α 1 - single β 1 ∈ ann`.
    have hαβ' : Ideal.Quotient.mk ann (MonoidAlgebra.single α (1 : F))
        = Ideal.Quotient.mk ann (MonoidAlgebra.single β (1 : F)) := hαβ
    have hmem : (MonoidAlgebra.single α (1 : F) - MonoidAlgebra.single β (1 : F)) ∈ ann :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hαβ'
    apply hfaith
    refine LinearMap.ext fun w => ?_
    have hz := (Module.mem_annihilator.mp hmem) (ρ.asModuleEquiv.symm w)
    rw [sub_smul, sub_eq_zero, Representation.single_smul, Representation.single_smul,
      one_smul, one_smul, LinearEquiv.apply_symm_apply] at hz
    exact hz
  exact isCyclic_of_injective_ringHom f hf

/-- **Bender–Glauberman Lemma 2.7.** Let `p ≠ q` be primes, `P` a `2`-dimensional `𝔽_p`-space and
`Q` an elementary abelian group of order `q²` acting `𝔽_p`-linearly and faithfully on `P`.  Then

* **(a)** `q ∣ p − 1`, and
* **(b)** some `α ≠ 1` acts on `P` as a scalar `r` of order exactly `q`.

(See the file docstring for why the module formulation faithfully renders `Q ⊆ Aut(P)`.) -/
theorem elemAbelian_aut_action {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {P : Type*} [AddCommGroup P] [Module (ZMod p) P] [Module.Finite (ZMod p) P]
    (hP : Module.finrank (ZMod p) P = 2)
    {Q : Type*} [Group Q] [Finite Q]
    (hQea : OddOrder.GroupTheory.IsElementaryAbelian q Q) (hQcard : Nat.card Q = q ^ 2)
    (ρ : Representation (ZMod p) Q P) (hfaith : Function.Injective ρ) :
    q ∣ p - 1 ∧
      ∃ α : Q, α ≠ 1 ∧ ∃ r : (ZMod p)ˣ, orderOf r = q ∧ ∀ x : P, ρ α x = (r : ZMod p) • x := by
  classical
  -- Basic instances.
  haveI hne : NeZero ((Nat.card Q : ℕ) : ZMod p) := by
    refine ⟨fun hcontra => ?_⟩
    rw [hQcard, ZMod.natCast_eq_zero_iff] at hcontra
    exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hcontra))
  -- `Q` is not cyclic.
  have hnotcyclic : ¬ IsCyclic Q :=
    hQea.not_isCyclic_of_card_prime_sq Fact.out hQcard
  -- Convenient submodule top/bot identities for the subrepresentation lattice.
  have hbotTS : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl
  have htopTS : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl
  -- `ρ` is not irreducible (else the crux would make `Q` cyclic).
  have hnotirr : ¬ ρ.IsIrreducible := by
    intro hirr
    letI : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hQea.comm }
    haveI := hirr
    exact hnotcyclic (isCyclic_of_faithful_isIrreducible ρ hfaith)
  -- `P` is nontrivial, hence so is the subrepresentation lattice.
  haveI hntP : Nontrivial P := Module.nontrivial_of_finrank_pos (by rw [hP]; norm_num)
  have hbnt : (⊥ : Subrepresentation ρ) ≠ (⊤ : Subrepresentation ρ) := by
    intro h
    have h2 := congrArg Subrepresentation.toSubmodule h
    rw [hbotTS, htopTS] at h2
    exact bot_ne_top h2
  haveI hntSub : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, hbnt⟩
  -- Extract a proper nonzero subrepresentation `W`.
  have hmid : ∃ W : Subrepresentation ρ, W ≠ ⊥ ∧ W ≠ ⊤ := by
    by_contra hcon
    apply hnotirr
    refine { eq_bot_or_eq_top := fun W => ?_ }
    by_contra hW
    exact hcon ⟨W, fun h => hW (Or.inl h), fun h => hW (Or.inr h)⟩
  obtain ⟨W, hWbot, hWtop⟩ := hmid
  -- Maschke: `ρ` is semisimple, so `W` has a complement `W'`.
  haveI : Representation.IsSemisimpleRepresentation ρ := inferInstance
  obtain ⟨W', hWW'⟩ := exists_isCompl W
  -- Translate `IsCompl` from subrepresentations to `𝔽_p`-submodules.
  have hbot : W.toSubmodule ⊓ W'.toSubmodule = ⊥ := by
    have := congrArg Subrepresentation.toSubmodule hWW'.disjoint.eq_bot
    rwa [Subrepresentation.toSubmodule_inf, hbotTS] at this
  have htopP : W.toSubmodule ⊔ W'.toSubmodule = ⊤ := by
    have := congrArg Subrepresentation.toSubmodule hWW'.codisjoint.eq_top
    rwa [Subrepresentation.toSubmodule_sup, htopTS] at this
  have hcompl : IsCompl W.toSubmodule W'.toSubmodule :=
    ⟨disjoint_iff.mpr hbot, codisjoint_iff.mpr htopP⟩
  -- `W`, `W'` are lines.
  have hWtop' : W.toSubmodule ≠ ⊤ := fun h =>
    hWtop (Subrepresentation.toSubmodule_injective (by rw [h, htopTS]))
  have hWbot' : W.toSubmodule ≠ ⊥ := fun h =>
    hWbot (Subrepresentation.toSubmodule_injective (by rw [h, hbotTS]))
  have hdimW : Module.finrank (ZMod p) W.toSubmodule = 1 := by
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne le_top hWtop')
    rw [finrank_top, hP] at hlt
    have hgt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne bot_le (Ne.symm hWbot'))
    rw [finrank_bot] at hgt
    omega
  have hdimW' : Module.finrank (ZMod p) W'.toSubmodule = 1 := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hdimW, hP] at hsum
    omega
  -- Scalar characters of the two lines.
  set χ₁ : Q →* (ZMod p)ˣ := lineScalarChar W.toRepresentation hdimW with hχ₁
  set χ₂ : Q →* (ZMod p)ˣ := lineScalarChar W'.toRepresentation hdimW' with hχ₂
  -- The subrepresentation acts on its line by the ambient `ρ` (as an equation in `P`).
  have htoRep : ∀ (u : Q) (x : W.toSubmodule), ((W.toRepresentation u) x : P) = ρ u (x : P) :=
    fun _ _ => rfl
  have htoRep' : ∀ (u : Q) (x : W'.toSubmodule), ((W'.toRepresentation u) x : P) = ρ u (x : P) :=
    fun _ _ => rfl
  -- `ρ u` acts as the scalar `χᵢ u` on each line.
  have hactW : ∀ (u : Q) (y : P), y ∈ W.toSubmodule → ρ u y = (χ₁ u : ZMod p) • y := by
    intro u y hy
    have h := congrArg Subtype.val (lineScalarChar_smul W.toRepresentation hdimW u ⟨y, hy⟩)
    rw [htoRep, SetLike.val_smul] at h
    exact h
  have hactW' : ∀ (u : Q) (y : P), y ∈ W'.toSubmodule → ρ u y = (χ₂ u : ZMod p) • y := by
    intro u y hy
    have h := congrArg Subtype.val (lineScalarChar_smul W'.toRepresentation hdimW' u ⟨y, hy⟩)
    rw [htoRep', SetLike.val_smul] at h
    exact h
  -- Faithfulness of the pair `(χ₁, χ₂)`.
  have hpair : ∀ (u : Q), χ₁ u = 1 → χ₂ u = 1 → u = 1 := by
    intro u h1 h2
    apply hfaith
    refine LinearMap.ext fun x => ?_
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp
      (show x ∈ W.toSubmodule ⊔ W'.toSubmodule by rw [htopP]; exact Submodule.mem_top)
    have e1 : ρ u w₁ = w₁ := by
      have hh := congrArg Subtype.val
        ((lineScalarChar_eq_one_iff W.toRepresentation hdimW u).mp h1 ⟨w₁, hw₁⟩)
      rw [htoRep] at hh
      exact hh
    have e2 : ρ u w₂ = w₂ := by
      have hh := congrArg Subtype.val
        ((lineScalarChar_eq_one_iff W'.toRepresentation hdimW' u).mp h2 ⟨w₂, hw₂⟩)
      rw [htoRep'] at hh
      exact hh
    rw [map_add, e1, e2, map_one, Module.End.one_apply]
  -- Since `Q` is not cyclic, `δ := χ₁ · χ₂⁻¹` is not injective.
  have hδ_ninj : ¬ Function.Injective (⇑(χ₁ * χ₂⁻¹)) :=
    fun hinj => hnotcyclic (isCyclic_of_injective (χ₁ * χ₂⁻¹) hinj)
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hδ_ninj
  set α : Q := a * b⁻¹ with hαdef
  have hαne : α ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  have hδα : (χ₁ * χ₂⁻¹) α = 1 := by
    rw [hαdef, map_mul, map_inv, hab, mul_inv_cancel]
  have hχeq : χ₁ α = χ₂ α :=
    mul_inv_eq_one.mp (show χ₁ α * (χ₂ α)⁻¹ = 1 from hδα)
  have hr1 : χ₁ α ≠ 1 := fun h1 => hαne (hpair α h1 (hχeq ▸ h1))
  -- `r := χ₁ α` has order exactly `q`.
  have hrq1 : (χ₁ α) ^ q = 1 := by rw [← map_pow, hQea.pow_eq_one α, map_one]
  have horder : orderOf (χ₁ α) = q := orderOf_eq_prime hrq1 hr1
  -- (a): `q = orderOf r ∣ |𝔽_pˣ| = p − 1`.
  have hqdvd : q ∣ p - 1 := by
    have hd := orderOf_dvd_natCard (χ₁ α)
    rw [horder, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime Fact.out] at hd
    exact hd
  refine ⟨hqdvd, α, hαne, χ₁ α, horder, ?_⟩
  -- (b): `ρ α` acts as the scalar `χ₁ α` on all of `P`.
  intro x
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp
    (show x ∈ W.toSubmodule ⊔ W'.toSubmodule by rw [htopP]; exact Submodule.mem_top)
  rw [map_add, hactW α w₁ hw₁, hactW' α w₂ hw₂, hχeq, smul_add]

end OddOrder.RepresentationTheory
