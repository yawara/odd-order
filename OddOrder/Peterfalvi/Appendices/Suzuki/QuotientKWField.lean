/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.WCyclicDivides
import OddOrder.Peterfalvi.Appendices.SemilinearField
import OddOrder.Algebra.QuadraticFrobenius

/-!
# Peterfalvi Part II, Ch. III §3: the field `E = 𝐅_{q²}` on `S ⧸ Q₀`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §3, p. 120, first step of the Proposition:

> We identify `(S/Q₀) ⋊ KW` with `E ⋊ K₁W₁`, where `E = 𝐅_{q²}`, `K₁ = F^×` and
> `W₁ ≤ {x ∈ E^× : x^{1+q} = 1}`.

The book gets there by splitting on `θ = 1` / `θ ≠ 1` and invoking Appendix III
Propositions 1 and 2 to make `w` act as multiplication by some `ω ∈ E^×`.  The
route taken here avoids the case split: `KW` acts *irreducibly* on `S/Q₀`, so
Appendix I Proposition 2 (`Huppert.exists_field_semilinear_with_scalar`) produces
the field directly, of order `|S/Q₀| = q²`, with the whole of `KW` realized by
scalars.

Irreducibility is a two-line count once the pieces of Ch. I §3 Lemma 5 are in
hand.  Let `U ≤ S/Q₀` be `KW`-invariant.

* `U` is `K`-invariant and `K` (of order `q − 1 = 2^m − 1`) acts freely off the
  identity, so `q − 1` divides `|U| − 1`; as `|U|` is a power of `2` this forces
  `|U|` to be a power of `q` (`card_invariant_eq_pow_of_fixedPointFree`), hence
  `|U| ∈ {1, q, q²}` because `|S/Q₀| = q²`.
* The middle case is excluded by the moved-summand engine
  (`Suzuki2Groups.map_quotientCongr_ne_of_fixedPoints_le`): an invariant subgroup
  of order exactly `|Z(Q)|` cannot be stabilized by a nonidentity element of `W`,
  and `W ≠ 1` under hypothesis (C2).

## Main results

* `Hypothesis.quotientKWHom` — the combined `K × W` action on `Q ⧸ Z(Q)`
  (the two actions commute because `W = C_V(K)`).
* `Hypothesis.isAInvariant_quotientKW_eq_bot_or_top` — irreducibility of that
  action.
* `Hypothesis.exists_field_quotient_of_orderThree` — the field `E` with
  `|E| = q²` over which `Q ⧸ Z(Q)` is a line, together with the scalar
  realization `μ : K × W →* Eˣ` of the action.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

namespace Hypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## The combined `K × W` action on the central quotient -/

/-- The action of `W` on the central quotient `Q ⧸ Z(Q)` induced by conjugation.
(The centre is characteristic, so no fixed-point information is needed to induce
the action; that `W` fixes `Z(Q) = Q₀` *pointwise* is the extra input used by the
moved-summand engine, see `quotientWHom_eq_quotientCongr`.) -/
@[reducible] noncomputable def quotientWHom :
    ↥hyp.W →* MulAut (↥hyp.Q ⧸ Subgroup.center hyp.Q) :=
  quotientMulAutHom (IsAInvariant.of_characteristic hyp.conjQByW)

/-- The action of the actual `K`-actor on the central quotient.  Kept reducible
so that the `LemmaFiveSetup` fields and the moved-summand engine — both phrased
with the raw `quotientMulAutHom` — unify with it without an explicit rewrite. -/
@[reducible] noncomputable def quotientKHom :
    ↥hyp.actualKActor →* MulAut (↥hyp.Q ⧸ Subgroup.center hyp.Q) :=
  quotientMulAutHom (IsAInvariant.of_characteristic hyp.actualKActor.subtype)

@[simp] theorem quotientWHom_apply_mk (v : ↥hyp.W) (x : ↥hyp.Q) :
    hyp.quotientWHom v (QuotientGroup.mk x) =
      QuotientGroup.mk (hyp.conjQByW v x) := rfl

@[simp] theorem quotientKHom_apply_mk (k : ↥hyp.actualKActor) (x : ↥hyp.Q) :
    hyp.quotientKHom k (QuotientGroup.mk x) =
      QuotientGroup.mk (hyp.actualKActor.subtype k x) := rfl

/-- On the central quotient the induced `W`-action agrees with the
`Suzuki2Groups.quotientCongr` form required by the moved-summand engine.  Both
are `QuotientGroup.congr` applied to the same automorphism, so this is `rfl`
(the differing hypotheses are proofs of propositions). -/
theorem quotientWHom_eq_quotientCongr (v : ↥hyp.W)
    (hfix : ∀ z ∈ Subgroup.center hyp.Q, hyp.conjQByW v z = z) :
    hyp.quotientWHom v = Suzuki2Groups.quotientCongr (hyp.conjQByW v) hfix := rfl

/-- The `K`- and `W`-actions on `Q ⧸ Z(Q)` commute: `W = C_V(K)` centralizes `K`
inside `G`, so the two conjugation automorphisms of `Q` commute
(`conjQByW_commute_actualKActor`) and the property descends to the quotient. -/
theorem commute_quotientKHom_quotientWHom (k : ↥hyp.actualKActor) (v : ↥hyp.W) :
    Commute (hyp.quotientKHom k) (hyp.quotientWHom v) := by
  have key : hyp.quotientKHom k * hyp.quotientWHom v
      = hyp.quotientWHom v * hyp.quotientKHom k := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : (hyp.actualKActor.subtype k * hyp.conjQByW v) x
        = (hyp.conjQByW v * hyp.actualKActor.subtype k) x :=
      DFunLike.congr_fun (hyp.conjQByW_commute_actualKActor v k).eq x
    exact congrArg
      (fun y : ↥hyp.Q => (QuotientGroup.mk y : ↥hyp.Q ⧸ Subgroup.center hyp.Q)) hx
  exact key

/-- **The combined `K × W` action on `Q ⧸ Z(Q)`** (Peterfalvi Part II, Ch. III
§3, p. 120: the group called `KW` there).  Taking the *direct product* of the two
cyclic actors rather than their product inside `MulAut` keeps the group
commutative, which is what Appendix I Proposition 2 requires; the two actions do
commute, so this is a homomorphism. -/
noncomputable def quotientKWHom :
    ↥hyp.actualKActor × ↥hyp.W →*
      MulAut (↥hyp.Q ⧸ Subgroup.center hyp.Q) :=
  MonoidHom.noncommCoprod hyp.quotientKHom hyp.quotientWHom
    hyp.commute_quotientKHom_quotientWHom

theorem quotientKWHom_apply (kv : ↥hyp.actualKActor × ↥hyp.W) :
    hyp.quotientKWHom kv = hyp.quotientKHom kv.1 * hyp.quotientWHom kv.2 :=
  rfl

/-- A `KW`-invariant subgroup of the quotient is `K`-invariant. -/
theorem isAInvariant_quotientKHom_of_quotientKW
    {U : Subgroup (↥hyp.Q ⧸ Subgroup.center hyp.Q)}
    (hU : IsAInvariant hyp.quotientKWHom U) :
    IsAInvariant hyp.quotientKHom U := by
  intro k
  have h := hU (k, 1)
  rwa [hyp.quotientKWHom_apply, map_one, mul_one] at h

/-- A `KW`-invariant subgroup of the quotient is `W`-invariant. -/
theorem isAInvariant_quotientWHom_of_quotientKW
    {U : Subgroup (↥hyp.Q ⧸ Subgroup.center hyp.Q)}
    (hU : IsAInvariant hyp.quotientKWHom U) :
    IsAInvariant hyp.quotientWHom U := by
  intro v
  have h := hU (1, v)
  rwa [hyp.quotientKWHom_apply, map_one, one_mul] at h

/-! ## Irreducibility of the `KW`-action -/

/-- `|Q ⧸ Z(Q)| = q²` when `|Q| = q³` and `|Z(Q)| = q`. -/
theorem card_quotient_center_eq_sq {m : ℕ}
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card hyp.Q = Nat.card ↥hyp.Q0 ^ 3)
    (hZcard : Nat.card ↥(Subgroup.center hyp.Q) = 2 ^ m) :
    Nat.card (↥hyp.Q ⧸ Subgroup.center hyp.Q) = (2 ^ m) ^ 2 := by
  have hpos : 0 < (2 : ℕ) ^ m := by positivity
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center hyp.Q)
  rw [hZcard, hcardQ, hQ0card] at h
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [← h]
  ring

/-- **Irreducibility of the `KW`-action on `S/Q₀`** (Peterfalvi Part II, Ch. III
§3, p. 120).  Under hypothesis (C2) — in particular `W ≠ 1` — every
`KW`-invariant subgroup of `Q ⧸ Z(Q)` is trivial or everything.

`K` acts freely off the identity and has order `q − 1`, so an invariant subgroup
has order a power of `q`; since `|Q ⧸ Z(Q)| = q²` the only remaining possibility
is order exactly `q = |Z(Q)|`, and that is excluded by the moved-summand engine
applied to a nonidentity element of `W`. -/
theorem isAInvariant_quotientKW_eq_bot_or_top
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card hyp.Q = Nat.card ↥hyp.Q0 ^ 3)
    (inductionHypothesis : TheoremAInductionBelow G Ω)
    (s : hyp.LemmaFiveSetup m)
    {w : G} (hw : w ∈ hyp.W) (hw1 : w ≠ 1)
    (U : Subgroup (↥hyp.Q ⧸ Subgroup.center hyp.Q))
    (hU : IsAInvariant hyp.quotientKWHom U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  have hZcard : Nat.card ↥(Subgroup.center hyp.Q) = 2 ^ m := by
    rw [s.centerEqQ0,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv,
      hQ0card]
  have hMcard : Nat.card (↥hyp.Q ⧸ Subgroup.center hyp.Q) = (2 ^ m) ^ 2 :=
    hyp.card_quotient_center_eq_sq hQ0card hcardQ hZcard
  -- `|U|` is a power of `q`
  have hP2 : IsPGroup 2 (↥hyp.Q ⧸ Subgroup.center hyp.Q) := by
    refine (IsPGroup.of_card (p := 2) (n := m * 3) ?_).to_quotient _
    rw [hcardQ, hQ0card, ← pow_mul]
  obtain ⟨j, hj⟩ :=
    OddOrder.Higman.Suzuki2Groups.card_invariant_eq_pow_of_fixedPointFree
      hP2 hm s.freeQuotient s.cardActor
      (hyp.isAInvariant_quotientKHom_of_quotientKW hU)
  -- `|U| ∣ q²` bounds the exponent
  have hdvd : Nat.card ↥U ∣ (2 ^ m) ^ 2 := hMcard ▸ Subgroup.card_subgroup_dvd_card U
  have hq1 : 1 < (2 : ℕ) ^ m := Nat.one_lt_pow hm (by norm_num)
  have hjle : j ≤ 2 :=
    (Nat.pow_dvd_pow_iff_le_right hq1).mp (hj ▸ hdvd)
  interval_cases j
  · -- `|U| = 1`
    left
    rw [pow_zero] at hj
    exact Subgroup.eq_bot_of_card_eq U hj
  · -- `|U| = q = |Z(Q)|`: excluded by the moved-summand engine
    exfalso
    rw [pow_one] at hj
    obtain ⟨hω1, hωodd, -, -, hωfix⟩ :=
      hyp.conjQByW_omega_facts hw hw1 hst hm hQ0card hcardQ inductionHypothesis
        s.centerEqQ0
    have hWfix : ∀ z ∈ Subgroup.center hyp.Q,
        hyp.conjQByW ⟨w, hw⟩ z = z :=
      hyp.conjQByW_fixes_center s.centerEqQ0 ⟨w, hw⟩
    have hne := Suzuki2Groups.map_quotientCongr_ne_of_fixedPoints_le
      (le_refl _) s.centerSq s.sqMem s.invMem
      (hyp.isAInvariant_quotientKHom_of_quotientKW hU) (by rw [hj, hZcard])
      s.transCenter s.centerNeBot
      (hyp.conjQByW ⟨w, hw⟩) hω1 hωodd hWfix hωfix
    apply hne
    rw [← hyp.quotientWHom_eq_quotientCongr ⟨w, hw⟩ hWfix]
    exact hyp.isAInvariant_quotientWHom_of_quotientKW hU ⟨w, hw⟩
  · -- `|U| = q²`: everything
    right
    exact Subgroup.eq_top_of_card_eq U (by rw [hj, hMcard])

/-! ## The field `E = 𝐅_{q²}` -/

/-- **The standard model of `(S/Q₀) ⋊ KW`** produced by step (1) of the Ch. III §3
Proposition (Peterfalvi Part II, p. 120): a field `E` of order `q²` whose additive
group *is* `S/Q₀` and on which `KW` acts by multiplication, with `K₁ = μ(K) = F^×`
and `W₁ = μ(W)` inside the norm-one subgroup.

Bundled as a structure rather than left as a long existential because the later
steps of the Proposition (`σ`, `λ₁`, `φ`, the identification `S ≅ S₁`) all add
data on top of the same field; cf. `LemmaFiveSetup` and `Suzuki2Groups.TypeBData`.

The additive coordinate `coord : Additive (S/Q₀) ≃+ E` is the book's `α` of p. 119.
It is an `AddEquiv` rather than a `Module E` structure on the quotient because the
commutativity of `S/Q₀` is a *theorem* here (it comes from `LemmaFiveSetup`), so no
`CommGroup` instance on the quotient is available in the statement. -/
structure QuotientFieldModel (hyp : Hypothesis G Ω) (m : ℕ) where
  /-- the field `E = 𝐅_{q²}` -/
  E : Type uG
  [field : Field E]
  [finite : Finite E]
  [charTwo : CharP E 2]
  /-- `|E| = q²` -/
  card : Nat.card E = (2 ^ m) ^ 2
  /-- the scalar realization `K × W → E^×` of the action, i.e. `K₁W₁` -/
  mu : ↥hyp.actualKActor × ↥hyp.W →* Eˣ
  /-- the book's coordinate `α : S/Q₀ → E` -/
  coord : Additive (↥hyp.Q ⧸ Subgroup.center hyp.Q) ≃+ E
  /-- the action of `KW` becomes multiplication in `E` -/
  coord_act : ∀ (kv : ↥hyp.actualKActor × ↥hyp.W)
    (y : ↥hyp.Q ⧸ Subgroup.center hyp.Q),
    coord (Additive.ofMul (hyp.quotientKWHom kv y))
      = (mu kv : E) * coord (Additive.ofMul y)
  /-- `K₁ ⊆ F`: `μ(K)` is fixed by the `q`-power Frobenius, as `|K| = q − 1` -/
  mu_K_frobFixed : ∀ k : ↥hyp.actualKActor,
    ((mu (k, 1) : Eˣ) : E) ^ 2 ^ m = ((mu (k, 1) : Eˣ) : E)
  /-- `μ` is injective on `K`, so `K₁` is *all* of `F^×` -/
  mu_K_injective : Function.Injective fun k : ↥hyp.actualKActor => mu (k, 1)
  /-- `W₁ ≤ {x : x^{1+q} = 1}`, as `|W|` divides `q + 1` (Ch. I §3 Lemma 5) -/
  mu_W_normOne : ∀ v : ↥hyp.W, mu (1, v) ^ (2 ^ m + 1) = 1

attribute [instance] QuotientFieldModel.field QuotientFieldModel.finite
  QuotientFieldModel.charTwo

/-- **`S/Q₀` is a line over `E = 𝐅_{q²}`, and `KW` acts by scalars**
(Peterfalvi Part II, Ch. III §3, p. 120, first step of the Proposition).

Appendix I Proposition 2 (`Huppert.exists_field_semilinear_with_scalar`) applied
to the irreducible `K × W`-action of `isAInvariant_quotientKW_eq_bot_or_top`: the
endomorphism algebra of the central quotient is a field `E` with
`|E| = |S/Q₀| = q²`, over which `S/Q₀` is one-dimensional, and every element of
`KW` acts as multiplication by a unit of `E`.

This is the book's identification of `(S/Q₀) ⋊ KW` with `E ⋊ K₁W₁`.  The book
reaches it by splitting on `θ = 1` / `θ ≠ 1` and invoking Appendix III
Propositions 1 and 2 to exhibit `ω ∈ E^×` with `x^w = ω x`; here the field comes
out of the irreducibility of the *whole* of `KW` in one step, and `ω = μ (1, w)`.

Stated with the additive coordinate `α : Additive (S/Q₀) ≃+ E` of p. 119 rather
than with a `Module E` structure on the quotient: the commutativity of `S/Q₀` is
a *theorem* here (it comes from `LemmaFiveSetup`), so no `CommGroup` instance on
the quotient is available in the statement, and `AddEquiv` needs none.

The last three conjuncts are the book's `K₁ = F^×` and
`W₁ ≤ {x ∈ E^× : x^{1+q} = 1}`:

* `μ (k, 1)` is fixed by the Frobenius `x ↦ x^q` of `E`, i.e. lies in the subfield
  `F = 𝐅_q`, because `|K| = q − 1`;
* `k ↦ μ (k, 1)` is injective, so `μ` maps `K` *onto* the order-`(q − 1)` subgroup
  `F^×` of the cyclic group `E^×`;
* `μ (1, v)^{1+q} = 1`, because `|W|` divides `q + 1` (Ch. I §3 Lemma 5).

The characteristic is recorded as the `charTwo` instance field of
`QuotientFieldModel` because every later step of the Proposition works with the
`q`-power Frobenius `x ↦ x^q` of `E` (the book's `x ↦ x̄`). -/
theorem nonempty_quotientFieldModel_of_orderThree
    (hst : orderOf (hyp.distinguishedInvolution * hyp.t) = 3)
    (hQsuz : IsSuzuki2Group ↥hyp.Q)
    {m : ℕ} (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hcardQ : Nat.card hyp.Q = Nat.card ↥hyp.Q0 ^ 3)
    (inductionHypothesis : TheoremAInductionBelow G Ω)
    (s : hyp.LemmaFiveSetup m)
    {w : G} (hw : w ∈ hyp.W) (hw1 : w ≠ 1) :
    Nonempty (hyp.QuotientFieldModel m) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZcard : Nat.card ↥(Subgroup.center hyp.Q) = 2 ^ m := by
    rw [s.centerEqQ0,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Q0_le_Q).toEquiv,
      hQ0card]
  have hMcard : Nat.card (↥hyp.Q ⧸ Subgroup.center hyp.Q) = (2 ^ m) ^ 2 :=
    hyp.card_quotient_center_eq_sq hQ0card hcardQ hZcard
  have hirr : ∀ U : Subgroup (↥hyp.Q ⧸ Subgroup.center hyp.Q),
      IsAInvariant hyp.quotientKWHom U → U = ⊥ ∨ U = ⊤ := fun U hU =>
    hyp.isAInvariant_quotientKW_eq_bot_or_top hst hm hQ0card hcardQ
      inductionHypothesis s hw hw1 U hU
  have hEA : IsElementaryAbelian 2 (↥hyp.Q ⧸ Subgroup.center hyp.Q) :=
    s.isplit.split.quotientEA
  obtain ⟨hWcyc, hWdvd⟩ :=
    hyp.isCyclic_W_and_card_dvd_of_orderThree hst hQsuz hm hQ0card hcardQ
      inductionHypothesis
  haveI := hWcyc
  letI : CommGroup (↥hyp.Q ⧸ Subgroup.center hyp.Q) :=
    { (inferInstance : Group (↥hyp.Q ⧸ Subgroup.center hyp.Q)) with
      mul_comm := hEA.comm }
  haveI hMnontriv : Nontrivial (↥hyp.Q ⧸ Subgroup.center hyp.Q) := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hMcard]
    calc 1 < 2 ^ m := Nat.one_lt_pow hm (by norm_num)
      _ ≤ (2 ^ m) ^ 2 := Nat.le_self_pow (by norm_num) _
  letI : CommGroup ↥hyp.actualKActor := IsCyclic.commGroup
  letI : CommGroup ↥hyp.W := IsCyclic.commGroup
  obtain ⟨E, instE, instFin, μ, α, hcardE, hμ⟩ :=
    Huppert.exists_field_coordinate_of_irreducible hEA hyp.quotientKWHom hirr
  letI : Field E := instE
  haveI : Finite E := instFin
  have htwo : (2 : E) = 0 := by
    obtain ⟨u, hu⟩ := exists_ne (1 : ↥hyp.Q ⧸ Subgroup.center hyp.Q)
    have h1 : Additive.ofMul u + Additive.ofMul u = 0 := by
      have h := hEA.pow_eq_one u
      rw [pow_two] at h
      exact Additive.toMul.injective (by simpa using h)
    have h2 : α (Additive.ofMul u) + α (Additive.ofMul u) = 0 := by
      rw [← map_add, h1, map_zero]
    have hne : α (Additive.ofMul u) ≠ 0 := fun h =>
      hu (Additive.ofMul.injective (α.injective (h.trans (map_zero α).symm)))
    rcases mul_eq_zero.mp (show (2 : E) * α (Additive.ofMul u) = 0 by
      rw [two_mul]; exact h2) with h | h
    · exact h
    · exact absurd h hne
  haveI : CharP E 2 := OddOrder.FiniteField.charP_two_of_two_eq_zero htwo
  -- `μ (k, 1)` is Frobenius-fixed: its order divides `|K| = q − 1`
  have hKfix : ∀ k : ↥hyp.actualKActor,
      ((μ (k, 1) : Eˣ) : E) ^ 2 ^ m = ((μ (k, 1) : Eˣ) : E) := by
    intro k
    have hk : k ^ (2 ^ m - 1) = 1 := by rw [← s.cardActor]; exact pow_card_eq_one'
    have hp : ((k, 1) : ↥hyp.actualKActor × ↥hyp.W) ^ (2 ^ m - 1) = 1 := by
      rw [Prod.pow_mk, hk, one_pow, Prod.mk_one_one]
    have hone : ((μ (k, 1) : Eˣ) : E) ^ (2 ^ m - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hp, map_one, Units.val_one]
    have hle : 1 ≤ (2 : ℕ) ^ m := Nat.one_le_two_pow
    rw [show (2 : ℕ) ^ m = (2 ^ m - 1) + 1 by omega, pow_succ, hone, one_mul]
  -- injectivity: a `K`-actor acting trivially on the quotient is trivial
  have hKinj : Function.Injective fun k : ↥hyp.actualKActor => μ (k, 1) := by
    refine (injective_iff_map_eq_one (f := (μ.comp (MonoidHom.inl _ _)))).mpr ?_
    intro k hk1
    by_contra hkne
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥hyp.Q ⧸ Subgroup.center hyp.Q)
    refine hy (s.freeQuotient k hkne y ?_)
    have hfix : hyp.quotientKWHom (k, 1) y = y := by
      refine Additive.ofMul.injective (α.injective ?_)
      rw [hμ (k, 1) y]
      have : μ (k, 1) = 1 := hk1
      rw [this, Units.val_one, one_mul]
    rwa [hyp.quotientKWHom_apply, map_one, mul_one] at hfix
  -- `|W|` divides `q + 1`, so `μ (1, v)^{q+1} = 1`
  have hWnorm : ∀ v : ↥hyp.W, μ (1, v) ^ (2 ^ m + 1) = 1 := by
    intro v
    obtain ⟨c, hc⟩ := hWdvd
    have hv : v ^ (2 ^ m + 1) = 1 := by
      rw [hc, pow_mul, pow_card_eq_one', one_pow]
    have hp : ((1, v) : ↥hyp.actualKActor × ↥hyp.W) ^ (2 ^ m + 1) = 1 := by
      rw [Prod.pow_mk, hv, one_pow, Prod.mk_one_one]
    rw [← map_pow, hp, map_one]
  exact ⟨{ E := E, card := hcardE.trans hMcard, mu := μ, coord := α
           coord_act := hμ, mu_K_frobFixed := hKfix, mu_K_injective := hKinj
           mu_W_normOne := hWnorm }⟩


end Hypothesis

/-! ## Step (2) of the Proposition when `θ = 1`

The book's `σ` in the case `θ = 1` is the `q`-power Frobenius: it fixes `F` — hence
`K₁ = μ(K)` — pointwise, and it inverts `W₁ = μ(W)`.  Both are immediate from the
`QuotientFieldModel` fields, so this branch of step (2) needs no further input. -/

namespace Hypothesis.QuotientFieldModel

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  {hyp : Hypothesis G Ω} {m : ℕ} (M : hyp.QuotientFieldModel m)

/-- `E` is a `ZMod 2`-algebra, since it has characteristic `2`.

Not derivable by instance search (`ZMod.algebra` is a `def`, deliberately — see the
implementation note in `Mathlib/Data/ZMod/Defs.lean`), but canonical, so it is
registered here once for every `QuotientFieldModel`.  This is what puts
`QuadraticMap (ZMod 2) E E` — the home of the Appendix III Lemma 2(c) expansion
used in step (2) — in scope. -/
noncomputable instance instAlgebraZModTwo : Algebra (ZMod 2) M.E := ZMod.algebra M.E 2

/-- The book's bar operation `x ↦ x̄ = x^q` on `E`. -/
noncomputable def bar : RingAut M.E := OddOrder.FiniteField.qFrobenius M.E 2 m

@[simp] theorem bar_apply (x : M.E) : M.bar x = x ^ 2 ^ m :=
  OddOrder.FiniteField.qFrobenius_apply M.E 2 m x

/-- **`K₁` lies in the fixed field `F` of the bar operation.** -/
theorem bar_mu_K (k : ↥hyp.actualKActor) :
    M.bar ((M.mu (k, 1) : M.Eˣ) : M.E) = ((M.mu (k, 1) : M.Eˣ) : M.E) := by
  rw [bar_apply]
  exact M.mu_K_frobFixed k

/-- **The bar operation inverts `W₁`** — the book's `x^σ = x^{-1}` for `x ∈ W₁`
in the case `θ = 1` (p. 120, step (2)). -/
theorem bar_mu_W (v : ↥hyp.W) :
    M.bar ((M.mu (1, v) : M.Eˣ) : M.E) = (((M.mu (1, v) : M.Eˣ) : M.E))⁻¹ := by
  have h := OddOrder.FiniteField.qFrobenius_eq_inv_of_pow_succ_eq_one
    (E := M.E) (p := 2) (n := m) (M.mu_W_normOne v)
  rw [bar, h]
  simp

end Hypothesis.QuotientFieldModel

end OddOrder.Peterfalvi.Appendices.Suzuki
