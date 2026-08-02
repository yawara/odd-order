/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.QuadraticFrobenius
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.TwoPowerCongruence

/-!
# Pairs of Frobenius powers on a finite field of characteristic `2`

A pair of automorphisms of `𝐅_{2^n}` is determined, up to order, by the product
map `a ↦ σ(a) · τ(a)` it induces: writing `σ = Frob^i` and `τ = Frob^j`, the map
is `a ↦ a^{2^i + 2^j}`, and on the cyclic group `𝐅_{2^n}^×` of order `2^n - 1`
the exponent `2^i + 2^j` determines the unordered pair `{i, j}` modulo `n`.

This is the exponent bookkeeping behind Peterfalvi Part II, Ch. III §3, p. 121:
every automorphism pair `(σ, τ)` surviving in the Appendix III Lemma 2(c)
expansion of the quadratic map `χ` satisfies `σ(a) τ(a) = a^d` on `F^×`, so once
`d` has been normalized to the shape `1 + 2^t` the restrictions of `σ` and `τ` to
`F` are forced to be `1_F` and `θ = Frob^t` in some order — which is exactly what
makes the book's cocycle `φ(x, y) = λ₁ x y^σ + λ̄₁ x̄ ȳ^σ` satisfy
`φ(a x, b y) = a b^θ φ(x, y)`.

The arithmetic core is `two_pow_pair_sum_eq` (`TwoPowerCongruence.lean`, in
Higman's exponent-congruence family): two powers of two can only collide with two
powers of two modulo `2^n - 1`.

⚠ Importing `Higman/…/TwoPowerCongruence` from `Algebra/` inverts the usual
layering.  It is deliberate: that file is pure `ℕ`/`ZMod` arithmetic with no
`OddOrder` imports of its own, and it already carries the subset-sum machinery
(`sum_two_pow_zmod_eq_or_of_subset_range`, carry collapse) that this file needs.
Rebuilding it here would duplicate ~200 lines.  If the generic block is ever
split out into a base leaf, this import should follow it.

## Main results

* `two_pow_pair_congruence_of_pow_eq` — from `λ^{2^i + 2^j} = λ^{2^k + 2^l}` for
  `λ` of order `2^n - 1`, the congruence consumed by `two_pow_pair_sum_eq`.
* `frobIndex_pair_eq_of_pow_mul_eq` — the field form: if
  `a^{2^i} a^{2^j} = a^{2^k} a^{2^l}` for all `a`, then `{i, j} = {k, l}` mod `n`.
* `odd_orderOf_inv_mul_of_mul_eq_mul` — the consequence §3 (3) consumes: if
  `σ(a) τ(a) = ψ(a) φ(ψ(a))` then `σ⁻¹τ` is `φ` or `φ⁻¹`, so it inherits `φ`'s odd order.
* `restrictToFrobFixed`, `odd_orderOf_restrictToFrobFixed_inv_mul` — the same for a pair
  of automorphisms of `E`, restricted to `F`.
-/

set_option autoImplicit false

namespace OddOrder.FiniteField

open OddOrder.Higman.Suzuki2Groups

/-- **From an equality of powers to the exponent congruence.**  For `λ` of order
`2^n - 1`, `λ^{2^i + 2^j} = λ^{2^k + 2^l}` says exactly that the exponents agree
in `ZMod (2^n - 1)`, in the form `two_pow_pair_sum_eq` consumes. -/
theorem two_pow_pair_congruence_of_pow_eq {M : Type*} [Monoid M] {lam : M}
    {n i j k l : ℕ} (hn : 0 < n) (hord : orderOf lam = 2 ^ n - 1)
    (h : lam ^ (2 ^ i + 2 ^ j) = lam ^ (2 ^ k + 2 ^ l)) :
    (2 : ZMod (2 ^ n - 1)) ^ i + 2 ^ j = 2 ^ k + 2 ^ l := by
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hfin : IsOfFinOrder lam := orderOf_pos_iff.mp (by rw [hord]; omega)
  have hmod : 2 ^ i + 2 ^ j ≡ 2 ^ k + 2 ^ l [MOD 2 ^ n - 1] := by
    rw [← hord]
    exact hfin.pow_eq_pow_iff_modEq.mp h
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  push_cast at hcast
  exact hcast

/-- **A pair of Frobenius powers is determined, up to order, by the product map
it induces**: if `a^{2^i} · a^{2^j} = a^{2^k} · a^{2^l}` for every `a` in a field
of order `2^n`, then `{i, j} = {k, l}` modulo `n`.

Applied with `(k, l) = (0, t)` this is the step of Peterfalvi Part II, Ch. III §3,
p. 121 reading `{σ|_F, τ|_F} = {1_F, θ}` off the scaling law `χ(a x) = a^{1+θ} χ(x)`. -/
theorem frobIndex_pair_eq_of_pow_mul_eq {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hn : n ≠ 0) (hcard : Nat.card F = 2 ^ n) {i j k l : ℕ}
    (h : ∀ a : F, a ^ 2 ^ i * a ^ 2 ^ j = a ^ 2 ^ k * a ^ 2 ^ l) :
    ((i : ZMod n) = (k : ZMod n) ∧ (j : ZMod n) = (l : ZMod n)) ∨
      ((i : ZMod n) = (l : ZMod n) ∧ (j : ZMod n) = (k : ZMod n)) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hordg : orderOf ((g : F)) = 2 ^ n - 1 := by
    rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg,
      Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcard]
  have hpow : (g : F) ^ (2 ^ i + 2 ^ j) = (g : F) ^ (2 ^ k + 2 ^ l) := by
    rw [pow_add, pow_add]
    exact h _
  exact two_pow_pair_sum_eq (Nat.pos_of_ne_zero hn)
    (two_pow_pair_congruence_of_pow_eq (Nat.pos_of_ne_zero hn) hordg hpow)

/-- **`{σ, τ} = {ψ, φψ}`, read off as an order statement** (Peterfalvi Part II, Ch. III §3,
p. 121).

The book's step is

> if `λ_{μν} ≠ 0`, then `a^μ a^ν = a a^θ` for `a ∈ F`, whence `{μ|_F, ν|_F} = {1_F, θ}`.

`frobIndex_pair_eq_of_pow_mul_eq` gives the unordered equality of exponents; here it is
turned into what §3 (3) actually consumes, namely that `θ = σ⁻¹τ` has the same order as
the book's `θ` — in particular **odd**, since that is a structure field of the type-`B`
datum (`TypeBData.phi_orderOf_odd`).

The extra `ψ` is not decoration: the exponent `d` of Ch. III §3 is only determined up to
a power of two (replacing the `Q₀`-coordinate by `Frobⁱ ∘ ι` replaces `d` by `2ⁱ d`), so
the relation available is `a^d = ψ(a) · φ(ψ(a))` rather than `a · φ(a)`.  The twist
`σ⁻¹τ` is unaffected: `RingAut F` is abelian, so both branches give `φ^{±1}`. -/
theorem odd_orderOf_inv_mul_of_mul_eq_mul {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : n ≠ 0) (hcard : Nat.card F = 2 ^ n) (σ τ ψ φ : RingAut F)
    (hodd : Odd (orderOf φ)) (hmul : ∀ a : F, σ a * τ a = ψ a * φ (ψ a)) :
    Odd (orderOf (σ⁻¹ * τ)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, hi⟩ := exists_pow_eq_of_ringAut hcard hn σ
  obtain ⟨j, hj⟩ := exists_pow_eq_of_ringAut hcard hn τ
  obtain ⟨s, hs⟩ := exists_pow_eq_of_ringAut hcard hn ψ
  obtain ⟨r, hr⟩ := exists_pow_eq_of_ringAut hcard hn φ
  have hpow : ∀ (α : RingAut F) (k : ℕ), (∀ x : F, α x = x ^ 2 ^ k) →
      α = qFrobenius F 2 1 ^ k := by
    intro α k hk
    rw [qFrobenius_pow]
    exact RingEquiv.ext fun x => hk x
  have hσ := hpow σ i hi
  have hτ := hpow τ j hj
  have hψ := hpow ψ s hs
  have hφ := hpow φ r hr
  -- congruent exponents give equal automorphisms, the Frobenius having order `n`
  have key : ∀ a b : ℕ, (a : ZMod n) = (b : ZMod n) →
      (qFrobenius F 2 1 : RingAut F) ^ a = qFrobenius F 2 1 ^ b := by
    intro a b hab
    rw [pow_eq_pow_iff_modEq, orderOf_frobenius hcard hn]
    exact (ZMod.natCast_eq_natCast_iff a b n).mp hab
  have h : ∀ a : F, a ^ 2 ^ i * a ^ 2 ^ j = a ^ 2 ^ s * a ^ 2 ^ (s + r) := by
    intro a
    rw [← hi a, ← hj a, ← hs a, pow_add, pow_mul, ← hr (a ^ 2 ^ s), ← hs a]
    exact hmul a
  rcases frobIndex_pair_eq_of_pow_mul_eq hn hcard h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `σ = ψ` and `τ = φψ`
    have hστ : σ⁻¹ * τ = φ := by
      rw [hσ, hτ, hψ, hφ] at *
      rw [key i s h1, key j (s + r) h2, pow_add]
      group
    rw [hστ]
    exact hodd
  · -- `σ = φψ` and `τ = ψ`
    have hστ : σ⁻¹ * τ = φ⁻¹ := by
      rw [hσ, hτ, hψ, hφ] at *
      rw [key i (s + r) h1, key j s h2, pow_add]
      group
    rw [hστ, orderOf_inv]
    exact hodd

/-! ## Restricting Frobenius powers of `E` to the subfield `F` -/

section Restrict

variable {E : Type*} [Field E] [Finite E] [CharP E 2] {m : ℕ}

/-- **Every automorphism of `E` preserves `F`**: `α(a)^q = α(a^q) = α(a)`. -/
theorem map_mem_frobFixedSubfield (α : E ≃+* E) {a : E}
    (ha : a ∈ frobFixedSubfield E 2 m) : α a ∈ frobFixedSubfield E 2 m := by
  rw [mem_frobFixedSubfield] at ha ⊢
  rw [← map_pow, ha]

/-- The restriction to `F` of an automorphism of `E`, as an additive automorphism.

Used to move a coordinate `ι : … ≃+ F` by an automorphism of `E`, which is how the
normalization `α = 1` of Peterfalvi Part II, Ch. III §3, p. 121 is carried out:
replacing `ι` by `α⁻¹ ∘ ι` replaces `χ` by `α⁻¹ ∘ χ`. -/
noncomputable def frobFixedRestrict (α : E ≃+* E) :
    ↥(frobFixedSubfield E 2 m) ≃+ ↥(frobFixedSubfield E 2 m) where
  toFun a := ⟨α a, map_mem_frobFixedSubfield α a.2⟩
  invFun a := ⟨α.symm a, map_mem_frobFixedSubfield α.symm a.2⟩
  left_inv a := Subtype.ext (α.symm_apply_apply a)
  right_inv a := Subtype.ext (α.apply_symm_apply a)
  map_add' a b := Subtype.ext (map_add α (a : E) (b : E))

@[simp] theorem frobFixedRestrict_apply (α : E ≃+* E)
    (a : ↥(frobFixedSubfield E 2 m)) :
    ((frobFixedRestrict (m := m) α a : ↥(frobFixedSubfield E 2 m)) : E) = α (a : E) :=
  rfl

/-- **On `F` the Frobenius exponent only matters modulo `m`**: the `q`-power
Frobenius is the identity there, so `a^{2^i} = a^{2^{i mod m}}`. -/
theorem pow_two_pow_mod_of_mem_frobFixed {a : E}
    (ha : a ∈ frobFixedSubfield E 2 m) (i : ℕ) :
    a ^ 2 ^ i = a ^ 2 ^ (i % m) := by
  have hfix : a ^ 2 ^ m = a := mem_frobFixedSubfield.mp ha
  have key : ∀ k : ℕ, a ^ 2 ^ (m * k) = a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, pow_add, pow_mul, ih, hfix]
  conv_lhs => rw [← Nat.div_add_mod i m]
  rw [pow_add, pow_mul, key (i / m)]

/-- **The restriction of an automorphism of `E` to `F`**, as an automorphism of `F`.

Well defined by `map_mem_frobFixedSubfield`, and bijective because `F` is finite. -/
noncomputable def restrictToFrobFixed (α : E ≃+* E) :
    RingAut ↥(frobFixedSubfield E 2 m) :=
  RingEquiv.ofBijective
    ({ toFun := fun a => ⟨α (a : E), map_mem_frobFixedSubfield α a.2⟩
       map_one' := Subtype.ext (by simp)
       map_mul' := fun a b => Subtype.ext (by simp)
       map_zero' := Subtype.ext (by simp)
       map_add' := fun a b => Subtype.ext (by simp) } :
      ↥(frobFixedSubfield E 2 m) →+* ↥(frobFixedSubfield E 2 m))
    (by
      haveI : Finite ↥(frobFixedSubfield E 2 m) := Subtype.finite
      have hinj : Function.Injective
          (fun a : ↥(frobFixedSubfield E 2 m) =>
            (⟨α (a : E), map_mem_frobFixedSubfield α a.2⟩ :
              ↥(frobFixedSubfield E 2 m))) :=
        fun a b hab => Subtype.ext (α.injective (congrArg Subtype.val hab))
      exact ⟨hinj, Finite.surjective_of_injective hinj⟩)

@[simp] theorem coe_restrictToFrobFixed (α : E ≃+* E)
    (a : ↥(frobFixedSubfield E 2 m)) :
    ((restrictToFrobFixed α a : ↥(frobFixedSubfield E 2 m)) : E) = α (a : E) := rfl

/-- The restriction of `σ⁻¹τ` is `σ⁻¹τ` on `F`. -/
theorem coe_restrictToFrobFixed_inv_mul (σ τ : E ≃+* E)
    (a : ↥(frobFixedSubfield E 2 m)) :
    ((((restrictToFrobFixed σ)⁻¹ * restrictToFrobFixed τ :
      RingAut ↥(frobFixedSubfield E 2 m)) a : ↥(frobFixedSubfield E 2 m)) : E)
      = σ.symm (τ (a : E)) := by
  have hb : ((restrictToFrobFixed τ a : ↥(frobFixedSubfield E 2 m)) : E) = τ (a : E) := rfl
  have happ : (((restrictToFrobFixed σ)⁻¹ * restrictToFrobFixed τ :
      RingAut ↥(frobFixedSubfield E 2 m)) a : ↥(frobFixedSubfield E 2 m))
      = (restrictToFrobFixed σ).symm (restrictToFrobFixed τ a) := rfl
  rw [happ]
  refine σ.injective ?_
  rw [σ.apply_symm_apply, ← hb]
  exact coe_restrictToFrobFixed σ ((restrictToFrobFixed σ).symm (restrictToFrobFixed τ a))
    ▸ congrArg (Subtype.val (p := fun x => x ∈ frobFixedSubfield E 2 m))
      ((restrictToFrobFixed σ).apply_symm_apply (restrictToFrobFixed τ a))

/-- **A pair of Frobenius powers of `E` is determined on `F`, up to order, by the
product map it induces there.**

`E`'s automorphisms restrict to `F` through their exponent modulo `m`, so this is
`frobIndex_pair_eq_of_pow_mul_eq` for the field `F` of order `2^m`.

Peterfalvi Part II, Ch. III §3, p. 121: applied to two pairs surviving in the
Lemma 2(c) expansion of `χ` — both satisfying `σ(a) τ(a) = a^d` on `F^×` — it says
all surviving pairs have the *same* restriction to `F`, which is the hypothesis of
`exists_bilinear_lift_of_pinned_restriction`. -/
theorem restrict_pair_eq_of_mul_eq_on_frobFixed (hm : m ≠ 0)
    (hcard : Nat.card E = (2 ^ m) ^ 2) (i j i' j' : ℕ)
    (h : ∀ a : E, a ∈ frobFixedSubfield E 2 m →
      a ^ 2 ^ i * a ^ 2 ^ j = a ^ 2 ^ i' * a ^ 2 ^ j') :
    (∀ a ∈ frobFixedSubfield E 2 m, a ^ 2 ^ i = a ^ 2 ^ i' ∧ a ^ 2 ^ j = a ^ 2 ^ j') ∨
      (∀ a ∈ frobFixedSubfield E 2 m,
        a ^ 2 ^ i = a ^ 2 ^ j' ∧ a ^ 2 ^ j = a ^ 2 ^ i') := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(frobFixedSubfield E 2 m) := Subtype.finite
  -- the hypothesis, read inside `F`
  have hF : ∀ a : ↥(frobFixedSubfield E 2 m),
      a ^ 2 ^ i * a ^ 2 ^ j = a ^ 2 ^ i' * a ^ 2 ^ j' := by
    intro a
    refine Subtype.ext ?_
    push_cast
    exact h (a : E) a.2
  -- `mod m` transport of the conclusion back to `E`
  have hmod : ∀ (k l : ℕ), (k : ZMod m) = (l : ZMod m) →
      ∀ a ∈ frobFixedSubfield E 2 m, a ^ 2 ^ k = a ^ 2 ^ l := by
    intro k l hkl a ha
    have : k % m = l % m := (ZMod.natCast_eq_natCast_iff' k l m).mp hkl
    rw [pow_two_pow_mod_of_mem_frobFixed ha k, pow_two_pow_mod_of_mem_frobFixed ha l, this]
  rcases frobIndex_pair_eq_of_pow_mul_eq (F := ↥(frobFixedSubfield E 2 m)) hm
    (natCard_frobFixedSubfield hcard hm) hF with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl fun a ha => ⟨hmod i i' h1 a ha, hmod j j' h2 a ha⟩
  · exact Or.inr fun a ha => ⟨hmod i j' h1 a ha, hmod j i' h2 a ha⟩

/-- **The scaling pair of `E` has odd-order twist on `F`** — the form §3 (3) consumes
(Peterfalvi Part II, Ch. III §3, p. 121 into Ch. IV §3 (3), p. 130).

`σ` and `τ` are the scaling pair of the Ch. III §3 Proposition, automorphisms of `E`; the
relation they satisfy on `F` is the book's `a^μ a^ν = a a^θ`, with `θ` the type-`B`
automorphism of `F` — of odd order by `TypeBData.phi_orderOf_odd`.  Then `σ⁻¹τ` restricted
to `F` is `θ` or `θ⁻¹`, hence of odd order.

⚠ On `E` itself `σ⁻¹τ` need *not* have odd order: it inverts the norm-one subgroup, so it
may be the `q`-Frobenius, of order `2`.  Only the restriction is constrained. -/
theorem odd_orderOf_restrictToFrobFixed_inv_mul (hm : m ≠ 0)
    (hcard : Nat.card E = (2 ^ m) ^ 2) (σ τ : E ≃+* E)
    (ψ φ : RingAut ↥(frobFixedSubfield E 2 m)) (hodd : Odd (orderOf φ))
    (hmul : ∀ a : ↥(frobFixedSubfield E 2 m),
      σ (a : E) * τ (a : E)
        = ((ψ a : ↥(frobFixedSubfield E 2 m)) : E)
          * ((φ (ψ a) : ↥(frobFixedSubfield E 2 m)) : E)) :
    Odd (orderOf ((restrictToFrobFixed (m := m) σ)⁻¹ * restrictToFrobFixed (m := m) τ)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(frobFixedSubfield E 2 m) := Subtype.finite
  refine odd_orderOf_inv_mul_of_mul_eq_mul (F := ↥(frobFixedSubfield E 2 m)) hm
    (natCard_frobFixedSubfield hcard hm) _ _ ψ φ hodd fun a => ?_
  apply Subtype.ext
  push_cast
  exact hmul a

end Restrict

end OddOrder.FiniteField
