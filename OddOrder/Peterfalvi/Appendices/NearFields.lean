/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki
import OddOrder.Peterfalvi.Appendices.SemilinearField

/-!
# Peterfalvi Appendix C: On Near-Fields

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix C, pp. 137--138.

The appendix uses finite near-fields to describe the 2-rank one case of the
Suzuki theorem and records the special Zassenhaus classification needed there.

## Honesty status

Every statement in this file is a genuine assertion about near-fields: there are
no opaque `Prop` fields and no self-carried `_holds` proofs anywhere.

**What was opaque before (2026-07-18 de-opacification).**

* `FiniteNearField` was a structure whose fields `finite`, `additive_group`,
  `multiplicative_group`, `right_distrib` were arbitrary `Prop`s carrying their
  own proofs.  It is **deleted**: the file already contains the real `NearField`
  class (`AddCommGroup` + `GroupWithZero` + right distributivity), which is what
  every statement now uses.
* `RankOneNearFieldData` had `affine_model`, `Q_identification`,
  `D_identification`, `unique_involution_in_H` as free `Prop` + `_holds`.  It is
  replaced by `AffineNearFieldModel`, whose fields are the actual embedding
  `F ↪ G`, normality, the complement `G = F ⋊ H`, the multiplicative
  identification `Q ≃* Fˣ` *with* its conjugation compatibility, the faithful
  action of `D` by near-field automorphisms, uniqueness of the involution in
  `H`, and the order formula for products of distinct involutions.
* `rankOne_affine_nearField` took an **arbitrary `(two_rank_one : Prop)`**
  argument and concluded `∃ data, data.affine_model`, i.e. nothing.  It now
  takes a real `RankOneHypothesis` (Peterfalvi (A1)–(A2) plus the *negation* of
  (A3), which is what "2-rank one" means) and concludes the existence of an
  `AffineNearFieldModel`.  Note the old statement could not even be repaired in
  place: it was phrased over `Suzuki.Hypothesis`, which *contains* (A3)
  (`two_rank_ge_two`), so a genuine 2-rank-one hypothesis added to it would have
  made the theorem vacuous.
* `cyclic_index_two_nearField_classification` took an arbitrary
  `(cyclic_index_two : Prop)` and concluded `∃ classification : Prop,
  classification` — provable by `⟨True, trivial⟩`; its `sorry` hid nothing.  It
  now states the actual dichotomy (field or `F_{r²,2}`, with `|Z(F^*)| = r - 1`).

Per-result status:

| Result | Status |
|---|---|
| near-field basics, Maschke, `F_{r²,2}` twisting | **proved, sorry-free** (unchanged) |
| App. C Prop 2, irreducibility half (`rightMulAction_irreducible_of_index_two`) | **proved** |
| App. C Prop 2, field half (`nearField_field_structure_of_index_two`) | **proved** (unchanged) |
| `NearField.mul_add_of_mul_comm` (commutative ⇒ distributive) | **proved, sorry-free** (new) |
| `exists_field_structure_of_cyclic_index_two` (Prop 2, first half) | **proved, sorry-free** (new) |
| App. C Prop 1 (`rankOne_affine_nearField`) | honest statement, `sorry` |
| App. C Prop 2 headline (`cyclic_index_two_nearField_classification`) | honest statement, `sorry` |
-/

namespace OddOrder.Peterfalvi.Appendices.NearFields

/-- **A finite group acting freely on a finite type divides its cardinality**: if every stabilizer
is trivial, then `|G| ∣ |α|` (each orbit has size `|G|`, and the orbits partition `α`).  General
group-action fact (could live in `Mathlib.GroupTheory.GroupAction`); used here for the orbit
counting `|A| ∣ |U| - 1` in Appendix C, Proposition 2. -/
theorem card_group_dvd_card_of_free {G β : Type*} [Group G] [MulAction G β]
    [Finite G] [Finite β] (hfree : ∀ b : β, MulAction.stabilizer G b = ⊥) :
    Nat.card G ∣ Nat.card β := by
  classical
  haveI : Fintype (MulAction.orbitRel.Quotient G β) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits G β), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  have hc : Nat.card (MulAction.orbit G ω.out) = Nat.card G := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G ω.out), hfree ω.out,
      ← Subgroup.index_eq_card, Subgroup.index_bot]
  exact ⟨1, by rw [hc, mul_one]⟩

/-- A **(right) near-field** (Peterfalvi, Appendix C, p. 137): a set `F` with `+` and `·` such that
`(F, +)` is a commutative group, `(F, ·)` is a group with zero — i.e. `(F ∖ {0}, ·)` is a group —
and the **right** distributive law `(a + b) c = a c + b c` holds.  (Left distributivity and
`·`-commutativity may fail; a field is the special case where both also hold.)

Modeled as `AddCommGroup F` + `GroupWithZero F` + right distributivity, so the full multiplicative
group-with-zero API (`mul_inv_cancel₀`, `zero_mul`, `mul_zero`, `zero_ne_one`, …) is inherited. -/
class NearField (F : Type*) extends AddCommGroup F, GroupWithZero F where
  /-- The right distributive law `(a + b) * c = a * c + b * c`. -/
  protected right_distrib : ∀ a b c : F, (a + b) * c = a * c + b * c

/-- The right distributive law in a near-field. -/
theorem NearField.add_mul {F : Type*} [NearField F] (a b c : F) :
    (a + b) * c = a * c + b * c := NearField.right_distrib a b c

/-- **A near-field with commutative multiplication is a field** (the meaning of the first
alternative in Peterfalvi, Appendix C, Proposition 2).  A near-field only postulates the *right*
distributive law; if multiplication is commutative the left law follows, so `F` is a commutative
division ring, i.e. a field. -/
theorem NearField.mul_add_of_mul_comm {F : Type*} [NearField F]
    (hcomm : ∀ x y : F, x * y = y * x) (a b c : F) : a * (b + c) = a * b + a * c := by
  rw [hcomm a (b + c), NearField.add_mul, hcomm b a, hcomm c a]

section NearFieldBasics

variable {F : Type*} [NearField F]

/-- Right multiplication by a nonzero element is an additive automorphism of a near-field: it is
additive by the right distributive law, and bijective because `a` is invertible. -/
def rightMul (a : F) (ha : a ≠ 0) : F ≃+ F where
  toFun x := x * a
  invFun x := x * a⁻¹
  left_inv x := by change (x * a) * a⁻¹ = x; rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
  right_inv x := by change (x * a⁻¹) * a = x; rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]
  map_add' x y := NearField.add_mul x y a

@[simp] theorem rightMul_apply (a : F) (ha : a ≠ 0) (x : F) : rightMul a ha x = x * a := rfl

/-- All nonzero elements of a near-field have the same additive order: `F^*` acts transitively on
`F^#` by right multiplication (`rightMul`), an additive automorphism. -/
theorem addOrderOf_eq_of_ne_zero (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    addOrderOf x = addOrderOf y := by
  have hne : x⁻¹ * y ≠ 0 := mul_ne_zero (inv_ne_zero hx) hy
  have hxy : y = (rightMul (x⁻¹ * y) hne) x := by
    change y = x * (x⁻¹ * y); rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
  rw [hxy]
  exact (addOrderOf_injective (rightMul (x⁻¹ * y) hne).toAddMonoidHom
    (rightMul (x⁻¹ * y) hne).injective x).symm

/-- **The characteristic of a finite near-field is a prime** (Peterfalvi, Appendix C, p. 137: "`F`
is an elementary abelian `f`-group for some prime `f`"): there is a prime `f` with `f • x = 0` for
all `x ∈ F`.  Since all nonzero elements share one additive order (`addOrderOf_eq_of_ne_zero`),
that order is forced to be prime by the divisor argument; this makes `(F, +)` elementary abelian. -/
theorem exists_prime_char [Finite F] :
    ∃ f : ℕ, f.Prime ∧ ∀ x : F, f • x = 0 := by
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : F)
  set f := addOrderOf x₀ with hf
  have hf0 : f ≠ 0 := (addOrderOf_pos x₀).ne'
  have hf1 : f ≠ 1 := fun h => hx₀ (AddMonoid.addOrderOf_eq_one_iff.mp h)
  obtain ⟨g, hg_prime, hg_dvd⟩ := Nat.exists_prime_and_dvd hf1
  have hdvd2 : f / g ∣ f := Nat.div_dvd_of_dvd hg_dvd
  have hord : addOrderOf ((f / g) • x₀) = g := by
    rw [addOrderOf_nsmul, ← hf, Nat.gcd_eq_right hdvd2, Nat.div_div_self hg_dvd hf0]
  have hgf : g = f := by
    by_contra hne
    have hy0 : (f / g) • x₀ ≠ 0 := by
      intro h
      have h1 : addOrderOf ((f / g) • x₀) = 1 := AddMonoid.addOrderOf_eq_one_iff.mpr h
      rw [hord] at h1; exact hg_prime.ne_one h1
    have hconst := addOrderOf_eq_of_ne_zero ((f / g) • x₀) x₀ hy0 hx₀
    rw [hord, ← hf] at hconst
    exact hne hconst
  refine ⟨f, hgf ▸ hg_prime, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hax : addOrderOf x = f := addOrderOf_eq_of_ne_zero x x₀ hx hx₀
    rw [← hax]; exact addOrderOf_nsmul_eq_zero x

/-- The additive group of a finite near-field, viewed multiplicatively, is elementary abelian for
some prime `f`.  This is the form consumed by Appendix I's `exists_field_semilinear`
(`OddOrder.GroupTheory.IsElementaryAbelian f (Multiplicative F)`). -/
theorem isElementaryAbelian_multiplicative [Finite F] :
    ∃ f : ℕ, f.Prime ∧ OddOrder.GroupTheory.IsElementaryAbelian f (Multiplicative F) := by
  obtain ⟨f, hf, hfx⟩ := exists_prime_char (F := F)
  refine ⟨f, hf, fun x y => mul_comm x y, fun x => ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  exact hfx (Multiplicative.toAdd x)

/-- The right-multiplication action of a commutative subgroup `A ⊆ Fˣ` on `(F, +)` (written
multiplicatively), as a monoid homomorphism into `MulAut (Multiplicative F)`.  Right multiplication
is additive (`rightMul`); the homomorphism property needs `A` commutative (`hcomm`), since right
multiplication is otherwise only an anti-homomorphism.  Together with
`isElementaryAbelian_multiplicative`
this is the data fed to Appendix I's `exists_field_semilinear`. -/
noncomputable def rightMulAction (A : Subgroup Fˣ)
    (hcomm : ∀ u v : A, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ)) :
    A →* MulAut (Multiplicative F) where
  toFun u := (rightMul ((u : Fˣ) : F) (Units.ne_zero _)).toMultiplicative
  map_one' := by
    ext x
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd x * (((1 : A) : Fˣ) : F) = Multiplicative.toAdd x
    rw [OneMemClass.coe_one, Units.val_one, mul_one]
  map_mul' u v := by
    ext x
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd x * (((u * v : A) : Fˣ) : F)
      = Multiplicative.toAdd x * (((v : Fˣ) : F)) * (((u : Fˣ) : F))
    have hc' : ((u : Fˣ) : F) * ((v : Fˣ) : F) = ((v : Fˣ) : F) * ((u : Fˣ) : F) := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm u v]
    rw [Subgroup.coe_mul, Units.val_mul, hc', ← mul_assoc]

/-- The action of `rightMulAction` on additive coordinates: `u` sends `x` to `x * (u : F)`. -/
@[simp] theorem rightMulAction_toAdd (A : Subgroup Fˣ)
    (hcomm : ∀ u v : A, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ)) (u : A) (x : Multiplicative F) :
    Multiplicative.toAdd (rightMulAction A hcomm u x) = Multiplicative.toAdd x * ((u : Fˣ) : F) :=
  rfl

/-- `A ⊆ Fˣ` acts **freely** on `F^#` by right multiplication: a nontrivial element fixes no
nonzero point (group cancellation in the group-with-zero `F`).  This is the input to the orbit
counting that shows the index-2 subgroup `A` acts irreducibly. -/
theorem rightMulAction_eq_self_iff (A : Subgroup Fˣ)
    (hcomm : ∀ u v : A, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ)) (a : A) (x : Multiplicative F)
    (hx : x ≠ 1) (hfix : rightMulAction A hcomm a x = x) : a = 1 := by
  have h1 : Multiplicative.toAdd x * ((a : Fˣ) : F) = Multiplicative.toAdd x := by
    have h := congrArg Multiplicative.toAdd hfix
    rwa [rightMulAction_toAdd] at h
  have hx0 : Multiplicative.toAdd x ≠ 0 := fun h =>
    hx (Multiplicative.toAdd.injective (h.trans toAdd_one.symm))
  have hval : ((a : Fˣ) : F) = 1 := mul_left_cancel₀ hx0 (by rw [h1, mul_one])
  exact OneMemClass.coe_eq_one.mp (Units.val_eq_one.mp hval)

/-- Any subgroup `A ⊆ Fˣ` has order coprime to `|F|`: `|A| ∣ |Fˣ| = |F| - 1` (Lagrange), and
consecutive integers are coprime.  This is the coprimality hypothesis needed for Maschke's theorem
when splitting an `A`-invariant subgroup of `(F, +)`. -/
theorem card_coprime (A : Subgroup Fˣ) [Finite F] :
    Nat.Coprime (Nat.card A) (Nat.card F) := by
  haveI : Nonempty F := ⟨0⟩
  have h1 : Nat.card A ∣ Nat.card Fˣ := Subgroup.card_subgroup_dvd_card A
  rw [Nat.card_units] at h1
  have hcop : ∀ n : ℕ, 0 < n → Nat.Coprime (n - 1) n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_comm]
    exact Nat.coprime_add_self_right.mpr (Nat.coprime_one_right m)
  exact Nat.Coprime.coprime_dvd_left h1 (hcop (Nat.card F) Nat.card_pos)

/-- If `A ⊆ Fˣ` has index `2`, then `|F| = 2|A| + 1` (`|A| · index = |Fˣ| = |F| - 1`).  This is the
cardinality identity behind the `(|A|+1)² > 2|A|+1` contradiction proving `A` acts irreducibly. -/
theorem card_eq_of_index_two (A : Subgroup Fˣ) [Finite F] (hidx : A.index = 2) :
    Nat.card F = 2 * Nat.card A + 1 := by
  haveI : Nonempty F := ⟨0⟩
  have h := Subgroup.card_mul_index A
  rw [hidx, Nat.card_units] at h
  have hpos : 0 < Nat.card F := Nat.card_pos
  omega

/-- **Free-orbit counting bound** (the engine behind irreducibility in Appendix C, Proposition 2).
If a commutative subgroup `A ⊆ Fˣ` acts on `(F, +)` by right multiplication and `U` is a nontrivial
`A`-invariant subgroup, then `|A| + 1 ≤ |U|`.  Indeed `A` acts *freely* on `U ∖ {1}`
(`rightMulAction_eq_self_iff`), so `|A| ∣ |U| - 1` (`card_group_dvd_card_of_free`); as `U ≠ ⊥` the
quotient `|U| - 1` is positive, whence `|A| ≤ |U| - 1`.  Applied to both an invariant subgroup and
its complement, this drives the `(|A|+1)² > 2|A|+1` contradiction. -/
theorem add_one_le_card_of_aInvariant_ne_bot {F : Type*} [NearField F] [Finite F]
    (A : Subgroup Fˣ)
    (hcomm : ∀ u v : A, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ))
    {U : Subgroup (Multiplicative F)}
    (hUinv : OddOrder.Isaacs.Ch03.IsAInvariant (rightMulAction A hcomm) U) (hU : U ≠ ⊥) :
    Nat.card A + 1 ≤ Nat.card U := by
  classical
  letI : MulDistribMulAction A (Multiplicative F) :=
    MulDistribMulAction.compHom _ (rightMulAction A hcomm)
  -- the `A`-stable set `U ∖ {1}` as a `SubMulAction`.
  let sma : SubMulAction A (Multiplicative F) :=
    { carrier := {x | x ∈ U ∧ x ≠ 1}
      smul_mem' := fun a {x} hx => by
        refine ⟨hUinv.smul_mem a hx.1, fun h => hx.2 ?_⟩
        exact (rightMulAction A hcomm a).injective (by rw [map_one]; exact h) }
  -- `A` acts freely on `U ∖ {1}`.
  have hfree : ∀ b : sma, MulAction.stabilizer A b = ⊥ := by
    intro b
    have hb : (b : Multiplicative F) ∈ U ∧ (b : Multiplicative F) ≠ 1 := b.2
    rw [eq_bot_iff]
    intro a ha
    rw [MulAction.mem_stabilizer_iff] at ha
    have hval : (rightMulAction A hcomm a) (b : Multiplicative F) = (b : Multiplicative F) :=
      congrArg Subtype.val ha
    exact Subgroup.mem_bot.mpr (rightMulAction_eq_self_iff A hcomm a _ hb.2 hval)
  have hdvd : Nat.card A ∣ Nat.card sma := card_group_dvd_card_of_free hfree
  -- `|U ∖ {1}| + 1 = |U|`.
  have e : (sma : Type _) ≃ {y : U // y ≠ 1} :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, fun h => x.2.2 (Subtype.ext_iff.mp h)⟩
      invFun := fun y => ⟨y.1.1, y.1.2, fun h => y.2 (Subtype.ext h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : Nat.card sma + 1 = Nat.card U := by
    rw [Nat.card_congr e, ← Finite.card_option]
    exact Nat.card_congr (Equiv.optionSubtypeNe (1 : U))
  -- `|U ∖ {1}| > 0` since `U ≠ ⊥`.
  have hpos : 0 < Nat.card sma := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
    haveI : Nonempty sma := ⟨⟨a.1, a.2, fun h => ha (Subtype.ext h)⟩⟩
    exact Nat.card_pos
  have hle : Nat.card A ≤ Nat.card sma := Nat.le_of_dvd hpos hdvd
  omega

/-- **Maschke's theorem for an elementary abelian operator module** (the splitting step in
Appendix C, Proposition 2).  Let `A` act on an elementary abelian `p`-group `E` via
`φ : A →* MulAut E`, with `(|A|, |E|)` coprime and `p ∣ |E|`.  Then every `A`-invariant subgroup
`U ≤ E` has an `A`-invariant **complement** `W` (`IsCompl U W`, so `E` is the internal direct sum
`U ⊕ W`).  `Additive E` is an `F_p`-vector space on which `A` acts coprimely, so the representation
is semisimple (`ComplementedLattice` on `Subrepresentation`) and the submodule for `U` splits; the
complement is transported back to a subgroup through the order-isomorphisms
`AddSubgroup.toZModSubmodule` and `AddSubgroup.toSubgroup'`.  (Direct elementary-abelian analogue of
`OddOrder.BG.Ch1_Preliminary.exists_aInvariant_complement_in_omega1_quotient`, without the `Ω₁`
quotient wrapping.) -/
theorem exists_aInvariant_complement_of_elementaryAbelian
    {E : Type*} [CommGroup E] [Finite E] {p : ℕ} [Fact p.Prime]
    (hE : OddOrder.GroupTheory.IsElementaryAbelian p E)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut E}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card E)) (hpE : p ∣ Nat.card E)
    {U : Subgroup E} (hUinv : OddOrder.Isaacs.Ch03.IsAInvariant φ U) :
    ∃ W : Subgroup E, OddOrder.Isaacs.Ch03.IsAInvariant φ W ∧ IsCompl U W := by
  classical
  haveI hEcomm : IsMulCommutative E := ⟨⟨mul_comm⟩⟩
  -- `Additive E` is a `ZMod p`-module.
  have hpsmul : ∀ x : Additive E, (p : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hE.pow_eq_one x.toMul
  haveI : Module (ZMod p) (Additive E) := AddCommGroup.zmodModule hpsmul
  haveI : NeZero ((Nat.card A : ZMod p)) :=
    OddOrder.BG.Ch1_Preliminary.neZero_natCast_zmod_of_coprime hcop hpE
  -- the `F_p[A]`-representation carried by `φ`.
  set ρ : Representation (ZMod p) A (Additive E) :=
    (OddOrder.BG.Ch1_Preliminary.mulAutToEnd E p).comp φ with hρ_def
  have key_rho : ∀ (a : A) (v : Additive E),
      Additive.toMul (ρ a v) = (φ a) (Additive.toMul v) := fun _ _ => rfl
  -- `U` as a `ZMod p`-submodule `pU`, and its `ρ`-invariance.
  set pU := AddSubgroup.toZModSubmodule (n := p) (Subgroup.toAddSubgroup U) with hpU_def
  have hmem_pU : ∀ v : Additive E, v ∈ pU ↔ Additive.toMul v ∈ U := by
    intro v
    simp only [hpU_def, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]
  have hpU_invt : pU ∈ ρ.invtSubmodule := by
    rw [ρ.mem_invtSubmodule]; intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro v hv
    rw [hmem_pU] at hv ⊢
    rw [key_rho]
    exact hUinv.smul_mem a hv
  have hpU_sub : ∀ (a : A) ⦃v : Additive E⦄, v ∈ pU → ρ a v ∈ pU := by
    intro a v hv
    have hmem := ρ.mem_invtSubmodule.mp hpU_invt a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hmem
    exact hmem v hv
  -- Maschke: `pU` has an invariant complement `qc`.
  obtain ⟨qcSub, hcompl⟩ :=
    ComplementedLattice.exists_isCompl (⟨pU, hpU_sub⟩ : Subrepresentation ρ)
  set qc : Submodule (ZMod p) (Additive E) := qcSub.toSubmodule with hqc_def
  have hqc_invt : qc ∈ ρ.invtSubmodule := by
    rw [ρ.mem_invtSubmodule]; intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    exact fun v hv => qcSub.apply_mem_toSubmodule a hv
  -- `(⊓/⊔).toSubmodule` and `⊥/⊤.toSubmodule` are defeq projections (wave6 OperatorMaschke パターン).
  have hinf : pU ⊓ qc = ⊥ := congrArg Subrepresentation.toSubmodule hcompl.inf_eq_bot
  have hsup : pU ⊔ qc = ⊤ := congrArg Subrepresentation.toSubmodule hcompl.sup_eq_top
  -- transport `qc` to a subgroup `W` of `E` via the order-iso `Φ`.
  let Φ : Submodule (ZMod p) (Additive E) ≃o Subgroup E :=
    (AddSubgroup.toZModSubmodule (n := p)).symm.trans AddSubgroup.toSubgroup'
  set W : Subgroup E := Φ qc with hW_def
  have hΦpU : Φ pU = U := by
    have h1 : (AddSubgroup.toZModSubmodule (n := p)).symm pU = Subgroup.toAddSubgroup U := by
      rw [hpU_def, OrderIso.symm_apply_apply]
    simp only [Φ, OrderIso.trans_apply, h1]
    exact Subgroup.toAddSubgroup.symm_apply_apply U
  have hmem_W : ∀ h : E, h ∈ W ↔ (Additive.ofMul h) ∈ qc := by
    intro h
    rw [hW_def]
    simp only [Φ, OrderIso.trans_apply, AddSubgroup.mem_toSubgroup',
      AddSubgroup.toZModSubmodule_symm, Submodule.mem_toAddSubgroup]
  have hW_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ W := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a h hh
    rw [hmem_W] at hh ⊢
    have hmem := ρ.mem_invtSubmodule.mp hqc_invt a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hmem
    exact hmem _ hh
  refine ⟨W, hW_inv, ?_, ?_⟩
  · rw [disjoint_iff]
    have h := congrArg Φ hinf
    rwa [Φ.map_inf, Φ.map_bot, hΦpU, ← hW_def] at h
  · rw [codisjoint_iff]
    have h := congrArg Φ hsup
    rwa [Φ.map_sup, Φ.map_top, hΦpU, ← hW_def] at h

/-- **Near-field field structure** (the first half of Peterfalvi Appendix C, Proposition 2, via
Appendix I Proposition 2).  If a commutative subgroup `A ⊆ Fˣ` of a finite near-field acts
*irreducibly* on `(F, +)` by right multiplication, then `(F, +)` is a `1`-dimensional vector space
over a finite field `K` with `|K| = |F|` (i.e. `F` carries a field structure refining its additive
group).  Obtained by feeding the near-field data — `isElementaryAbelian_multiplicative` and
`rightMulAction` — into `exists_field_semilinear`. -/
theorem nearField_field_structure.{u} {F : Type u} [NearField F] [Finite F]
    (A : Subgroup Fˣ)
    (hcomm : ∀ u v : A, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ))
    (hirr : ∀ U : Subgroup (Multiplicative F),
      OddOrder.Isaacs.Ch03.IsAInvariant (rightMulAction A hcomm) U → U = ⊥ ∨ U = ⊤) :
    ∃ (K : Type u) (_ : Field K) (_ : Module K F) (_ : Finite K),
      Module.finrank K F = 1 ∧ Nat.card K = Nat.card F := by
  obtain ⟨f, hf, hE⟩ := isElementaryAbelian_multiplicative (F := F)
  haveI : Fact f.Prime := ⟨hf⟩
  letI : CommGroup A := { (inferInstance : Group A) with
    mul_comm := fun u v => Subtype.ext (by simpa [Subgroup.coe_mul] using hcomm u v) }
  obtain ⟨K, hK, hMod, hKfin, hrank, hcard, _⟩ :=
    OddOrder.Peterfalvi.Appendices.Huppert.exists_field_semilinear (E := Multiplicative F) hE
      (rightMulAction A hcomm) hirr
  exact ⟨K, hK, hMod, hKfin, hrank, hcard⟩

/-- **Index-two subgroups act irreducibly** (Peterfalvi Appendix C, Proposition 2, counting step).
A commutative subgroup `A ⊆ Fˣ` of **index `2`** acts *irreducibly* on `(F, +)` by right
multiplication: the only `A`-invariant subgroups of `(F, +)` are `⊥` and `⊤`.  If a proper
nontrivial invariant `U` existed, the free action of `A` on `U ∖ {1}` and on its Maschke complement
`W ∖ {1}` would force `|U|, |W| ≥ |A| + 1`, whence `|F| = |U|·|W| ≥ (|A|+1)² > 2|A|+1 = |F|`. -/
theorem rightMulAction_irreducible_of_index_two {F : Type*} [NearField F] [Finite F]
    (A : Subgroup Fˣ)
    (hcomm : ∀ u v : A, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ))
    (hidx : A.index = 2) (U : Subgroup (Multiplicative F))
    (hUinv : OddOrder.Isaacs.Ch03.IsAInvariant (rightMulAction A hcomm) U) :
    U = ⊥ ∨ U = ⊤ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hU_ne_bot, hU_ne_top⟩ := hcon
  haveI : Nontrivial (Multiplicative F) := inferInstanceAs (Nontrivial F)
  -- elementary abelian data + coprimality of `|A|` with `|F|`, plus `f ∣ |F|`.
  obtain ⟨f, hf, hE⟩ := isElementaryAbelian_multiplicative (F := F)
  haveI : Fact f.Prime := ⟨hf⟩
  have hMF : Nat.card (Multiplicative F) = Nat.card F := rfl
  have hcop : Nat.Coprime (Nat.card A) (Nat.card (Multiplicative F)) := by
    rw [hMF]; exact card_coprime A
  have hfE : f ∣ Nat.card (Multiplicative F) := by
    obtain ⟨x, hx⟩ := exists_ne (1 : Multiplicative F)
    have hord : orderOf x = f := by
      rcases (Nat.dvd_prime hf).mp (orderOf_dvd_of_pow_eq_one (hE.pow_eq_one x)) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx
      · exact h
    rw [← hord]; exact orderOf_dvd_natCard x
  -- `|U| ≥ |A| + 1`.
  have hU_ge : Nat.card A + 1 ≤ Nat.card U :=
    add_one_le_card_of_aInvariant_ne_bot A hcomm hUinv hU_ne_bot
  -- `A`-invariant Maschke complement `W`; `W ≠ ⊥` since `U ≠ ⊤`, so `|W| ≥ |A| + 1`.
  obtain ⟨W, hWinv, hUW⟩ :=
    exists_aInvariant_complement_of_elementaryAbelian hE hcop hfE hUinv
  have hW_ne_bot : W ≠ ⊥ := fun hW0 =>
    hU_ne_top (by have := hUW.sup_eq_top; rwa [hW0, sup_bot_eq] at this)
  have hW_ge : Nat.card A + 1 ≤ Nat.card W :=
    add_one_le_card_of_aInvariant_ne_bot A hcomm hWinv hW_ne_bot
  -- `|F| = |U| · |W|` from the (lattice) complement, since `(F, +)` is abelian.
  have hcompl' : Subgroup.IsComplement' U W :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hUW.disjoint
      (by rw [← Subgroup.mul_normal, hUW.sup_eq_top, Subgroup.coe_top])
  have hprod : Nat.card U * Nat.card W = Nat.card F := by rw [← hMF]; exact hcompl'.card_mul
  -- `(|A|+1)² ≤ |U|·|W| = |F| = 2|A|+1` with `|A| ≥ 1` is contradictory.
  have hFcard : Nat.card F = 2 * Nat.card A + 1 := card_eq_of_index_two A hidx
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hge : (Nat.card A + 1) * (Nat.card A + 1) ≤ Nat.card U * Nat.card W :=
    Nat.mul_le_mul hU_ge hW_ge
  nlinarith [hge, hprod, hFcard, hApos]

/-- **Unconditional near-field field structure for an index-`2` subgroup** (Peterfalvi Appendix C,
Proposition 2, field-structure half).  If a commutative subgroup `A ⊆ Fˣ` of a finite near-field has
index `2`, then `(F, +)` is a `1`-dimensional vector space over a finite field `K` with `|K| = |F|`.
Combines the index-`2` irreducibility (`rightMulAction_irreducible_of_index_two`) with
`nearField_field_structure`, discharging the irreducibility hypothesis. -/
theorem nearField_field_structure_of_index_two.{u} {F : Type u} [NearField F] [Finite F]
    (A : Subgroup Fˣ)
    (hcomm : ∀ u v : A, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ))
    (hidx : A.index = 2) :
    ∃ (K : Type u) (_ : Field K) (_ : Module K F) (_ : Finite K),
      Module.finrank K F = 1 ∧ Nat.card K = Nat.card F :=
  nearField_field_structure A hcomm (rightMulAction_irreducible_of_index_two A hcomm hidx)

end NearFieldBasics

section TwistedNearField

/-- **Twisting data turning a field into a near-field** (the construction behind `F_{r²,2}`,
Peterfalvi Appendix C, pp. 137--138).  An order-`≤ 2` ring automorphism `σ` of a field `K` together
with a multiplicative *sign* character `χ : Kˣ → ℤ/2` that is invariant under `σ`.  The twisted
multiplication `x ∘ y = σ^{χ(y)}(x) · y` then makes `K` a near-field (in general non-commutative
multiplicatively, so not a field).  For `F_{r²,2}`: `K = 𝔽_{r²}`, `σ : x ↦ x^r` (the order-`2`
Frobenius over `𝔽_r`), and `χ` the quadratic character (`0` on squares, `1` on non-squares). -/
structure TwistData (K : Type*) [Field K] where
  /-- The twisting automorphism (`x ↦ x^r` for `F_{r²,2}`). -/
  σ : RingAut K
  /-- `σ` has order dividing `2`. -/
  σ_sq : σ ^ 2 = 1
  /-- The sign character (quadratic character for `F_{r²,2}`). -/
  χ : Kˣ →* Multiplicative (ZMod 2)
  /-- `χ` is `σ`-invariant (automorphisms preserve squares). -/
  χ_σ : ∀ y : Kˣ, χ (Units.map (σ : K →* K) y) = χ y

namespace TwistData

variable {K : Type*} [Field K] (d : TwistData K)

open scoped Classical in
/-- The twisting exponent of `y`: `0` for `0` and for `χ`-even `y`, `1` for `χ`-odd `y`. -/
noncomputable def twExp (y : K) : ZMod 2 :=
  if h : y = 0 then 0 else Multiplicative.toAdd (d.χ (Units.mk0 y h))

/-- The order-`≤ 2` automorphism selected by `e : ℤ/2`: the identity (`e = 0`) or `σ` (`e = 1`). -/
def twAut (e : ZMod 2) : RingAut K := if e = 0 then 1 else d.σ

/-- The twisted (near-field) multiplication `x ∘ y = σ^{χ(y)}(x) · y`. -/
noncomputable def twMul (x y : K) : K := d.twAut (d.twExp y) x * y

@[simp] theorem twAut_zero : d.twAut 0 = 1 := by simp [twAut]

@[simp] theorem twAut_one : d.twAut 1 = d.σ := by simp [twAut]

/-- `twAut` turns addition in `ℤ/2` into composition: `twAut (a+b) = twAut a * twAut b`
(the `a = b = 1` case is where `σ² = 1` is used). -/
theorem twAut_add (a b : ZMod 2) : d.twAut (a + b) = d.twAut a * d.twAut b := by
  have hσσ : d.σ * d.σ = 1 := by rw [← pow_two]; exact d.σ_sq
  have key : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide
  rcases key a with ha | ha <;> rcases key b with hb | hb <;> subst ha <;> subst hb <;>
    simp only [show (0 : ZMod 2) + 0 = 0 from by decide, show (0 : ZMod 2) + 1 = 1 from by decide,
      show (1 : ZMod 2) + 0 = 1 from by decide, show (1 : ZMod 2) + 1 = 0 from by decide,
      twAut_zero, twAut_one, one_mul, mul_one, hσσ]

@[simp] theorem twExp_zero : d.twExp 0 = 0 := by simp [twExp]

@[simp] theorem twExp_one : d.twExp 1 = 0 := by
  rw [twExp, dif_neg one_ne_zero, show Units.mk0 (1 : K) one_ne_zero = 1 from Units.ext rfl,
    map_one, toAdd_one]

@[simp] theorem twMul_zero (x : K) : d.twMul x 0 = 0 := by simp [twMul]

@[simp] theorem zero_twMul (y : K) : d.twMul 0 y = 0 := by simp [twMul]

@[simp] theorem twMul_one (x : K) : d.twMul x 1 = x := by simp [twMul]

@[simp] theorem one_twMul (y : K) : d.twMul 1 y = y := by simp [twMul]

/-- The twisted product of two nonzero elements is nonzero. -/
theorem twMul_ne_zero {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : d.twMul x y ≠ 0 := by
  simp only [twMul]
  refine mul_ne_zero ?_ hy
  rw [ne_eq, EmbeddingLike.map_eq_zero_iff]
  exact hx

/-- Right distributivity of the twisted multiplication: `(a + b) ∘ c = a ∘ c + b ∘ c`. -/
theorem add_twMul (a b c : K) : d.twMul (a + b) c = d.twMul a c + d.twMul b c := by
  simp [twMul, map_add, add_mul]

/-- Composing the twist automorphisms adds their exponents: `twAut a (twAut b x) = twAut (a+b) x`.
-/
theorem twAut_twAut (a b : ZMod 2) (x : K) : d.twAut a (d.twAut b x) = d.twAut (a + b) x := by
  rw [twAut_add]; rfl

/-- `twExp` is multiplicative on nonzero elements: `twExp (y·z) = twExp y + twExp z`. -/
theorem twExp_mul {y z : K} (hy : y ≠ 0) (hz : z ≠ 0) :
    d.twExp (y * z) = d.twExp y + d.twExp z := by
  have hyz : y * z ≠ 0 := mul_ne_zero hy hz
  rw [twExp, dif_neg hyz, twExp, dif_neg hy, twExp, dif_neg hz,
    show Units.mk0 (y * z) hyz = Units.mk0 y hy * Units.mk0 z hz from Units.ext rfl,
    map_mul, toAdd_mul]

/-- `twExp` is `σ`-invariant on nonzero elements: `twExp (σ y) = twExp y`. -/
theorem twExp_σ {y : K} (hy : y ≠ 0) : d.twExp (d.σ y) = d.twExp y := by
  have hσy : d.σ y ≠ 0 := by rw [ne_eq, EmbeddingLike.map_eq_zero_iff]; exact hy
  rw [twExp, dif_neg hσy, twExp, dif_neg hy,
    show Units.mk0 (d.σ y) hσy = Units.map (d.σ : K →* K) (Units.mk0 y hy) from Units.ext rfl,
    d.χ_σ]

/-- `twExp` is invariant under every twist automorphism on nonzero elements. -/
theorem twExp_twAut {y : K} (hy : y ≠ 0) (e : ZMod 2) :
    d.twExp (d.twAut e y) = d.twExp y := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) e with he | he <;> subst he
  · rw [twAut_zero]; rfl
  · rw [twAut_one]; exact d.twExp_σ hy

/-- The twist exponent of a twisted product (of nonzero elements) adds: a key step for
associativity. -/
theorem twExp_twMul {y z : K} (hy : y ≠ 0) (hz : z ≠ 0) :
    d.twExp (d.twMul y z) = d.twExp y + d.twExp z := by
  have h1 : d.twAut (d.twExp z) y ≠ 0 := by rw [ne_eq, EmbeddingLike.map_eq_zero_iff]; exact hy
  rw [twMul, d.twExp_mul h1 hz, d.twExp_twAut hy]

/-- Associativity of the twisted multiplication: `(x ∘ y) ∘ z = x ∘ (y ∘ z)`. -/
theorem twMul_assoc (x y z : K) : d.twMul (d.twMul x y) z = d.twMul x (d.twMul y z) := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx; simp
  rcases eq_or_ne y 0 with hy | hy
  · subst hy; simp
  rcases eq_or_ne z 0 with hz | hz
  · subst hz; simp
  have key : d.twExp (d.twMul y z) = d.twExp y + d.twExp z := d.twExp_twMul hy hz
  change d.twAut (d.twExp z) (d.twMul x y) * z
     = d.twAut (d.twExp (d.twMul y z)) x * d.twMul y z
  rw [key]
  change d.twAut (d.twExp z) (d.twAut (d.twExp y) x * y) * z
     = d.twAut (d.twExp y + d.twExp z) x * (d.twAut (d.twExp z) y * z)
  rw [map_mul, twAut_twAut, mul_assoc, add_comm (d.twExp z) (d.twExp y)]

/-- The twist exponent is inversion-invariant on nonzero elements (`χ(y⁻¹) = χ(y)` in `ℤ/2`). -/
theorem twExp_inv {y : K} (hy : y ≠ 0) : d.twExp y⁻¹ = d.twExp y := by
  have hy' : y⁻¹ ≠ 0 := inv_ne_zero hy
  rw [twExp, dif_neg hy', twExp, dif_neg hy,
    show Units.mk0 y⁻¹ hy' = (Units.mk0 y hy)⁻¹ from Units.ext rfl, map_inv, toAdd_inv]
  exact (by decide : ∀ a : ZMod 2, -a = a) _

/-- The explicit twisted inverse `y⁻¹∘ = σ^{χ(y)}(y⁻¹)` is a right inverse (no finite-cancellation
needed): `y ∘ σ^{χ(y)}(y⁻¹) = 1`. -/
theorem twMul_twInv {y : K} (hy : y ≠ 0) : d.twMul y (d.twAut (d.twExp y) y⁻¹) = 1 := by
  have hy' : y⁻¹ ≠ 0 := inv_ne_zero hy
  change d.twAut (d.twExp (d.twAut (d.twExp y) y⁻¹)) y * d.twAut (d.twExp y) y⁻¹ = 1
  rw [d.twExp_twAut hy', d.twExp_inv hy, ← map_mul, mul_inv_cancel₀ hy, map_one]

end TwistData

/-- The near-field carried by twisting data `d`: the additive group of the field `K` equipped with
the twisted multiplication `x ∘ y = σ^{χ(y)}(x) · y`.  A type synonym for `K` so the twisted
multiplication does not clash with the field multiplication.  This is the abstract form of the
exceptional near-field `F_{r²,2}` (Peterfalvi, Appendix C). -/
def Twisted {K : Type*} [Field K] (_ : TwistData K) : Type _ := K

namespace Twisted

variable {K : Type*} [Field K] {d : TwistData K}

instance : AddCommGroup (Twisted d) := inferInstanceAs (AddCommGroup K)

/-- `Twisted d` is a near-field under the twisted multiplication. -/
noncomputable instance : NearField (Twisted d) :=
  { (inferInstance : AddCommGroup (Twisted d)) with
    mul := d.twMul
    one := (1 : K)
    inv := fun y => d.twAut (d.twExp y) y⁻¹
    mul_assoc := d.twMul_assoc
    one_mul := d.one_twMul
    mul_one := d.twMul_one
    zero_mul := d.zero_twMul
    mul_zero := d.twMul_zero
    inv_zero := by
      change d.twAut (d.twExp (0 : K)) (0 : K)⁻¹ = (0 : K)
      simp
    mul_inv_cancel := fun a ha => d.twMul_twInv ha
    exists_pair_ne := ⟨(0 : K), (1 : K), (zero_ne_one : (0 : K) ≠ 1)⟩
    right_distrib := d.add_twMul }

end Twisted

end TwistedNearField

section PropositionOne

open scoped Pointwise

/-- **Peterfalvi Appendix C, Proposition 1, hypotheses** (p. 137): the Part II hypotheses
**(A1)** and **(A2)** (p. 97) together with "`G` has 2-rank `1`".

The fields are exactly those of `Suzuki.Hypothesis` *except* (A3), which is replaced by its
negation.  This has to be a separate structure: `Suzuki.Hypothesis` carries
`two_rank_ge_two : ∃ E : Subgroup G, Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1` as a field, so bolting a
genuine 2-rank-one hypothesis onto it would produce contradictory (hence vacuous) hypotheses.

`two_rank_one` says `G` has **no** Klein four subgroup, i.e. 2-rank `≤ 1`; equality holds because
`Q_even` forces an involution to exist (Cauchy).  The hypotheses are satisfiable: e.g.
`G = AGL(1, 3) ≅ S₃` acting on three points, with `Q` of order `2` and `D = 1`. -/
structure RankOneHypothesis (G Ω : Type*) [Group G] [MulAction G Ω] [Finite G] where
  /-- the base point of `Ω`; `H` is its stabilizer -/
  basept : Ω
  /-- (A1): the action is doubly transitive -/
  doubly_transitive : MulAction.IsMultiplyPretransitive G Ω 2
  /-- (A2): the action is faithful -/
  faithful : FaithfulSMul G Ω
  H : Subgroup G
  Q : Subgroup G
  D : Subgroup G
  H_def : H = MulAction.stabilizer G basept
  /-- the distinguished involution `t ∈ G - H` -/
  t : G
  t_sq : t ^ 2 = 1
  t_ne_one : t ≠ 1
  t_not_mem_H : t ∉ H
  D_def : D = H ⊓ H.map (MulAut.conj t).toMonoidHom
  Q_le_H : Q ≤ H
  Q_normal_in_H : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q
  Q_inf_D_eq_bot : Q ⊓ D = ⊥
  Q_mul_D_eq_H : (Q : Set G) * (D : Set G) = (H : Set G)
  Q_even : Even (Nat.card Q)
  D_odd : Odd (Nat.card D)
  /-- `G` has 2-rank one: it contains no elementary abelian subgroup of order `4`.
  This is the negation of Part II's hypothesis (A3). -/
  two_rank_one : ¬ ∃ E : Subgroup G, Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1

/-- **Peterfalvi Appendix C, Proposition 1, conclusion**: the affine near-field model of `G`.

The book asserts an isomorphism `G ≅ 𝓛(F) ⋊ Σ = (F ⋊ F^*) ⋊ Σ` identifying `Q` with `F^*` and `D`
with `Σ`.  Internally this says: `F` sits in `G` as a normal subgroup complemented by `H`
(`G = F ⋊ H`), the conjugation action of `Q` on `F` is right multiplication by `F^*` under an
isomorphism `Q ≃* Fˣ`, and `D` acts faithfully on `F` by near-field automorphisms.  A "near-field
automorphism" is an additive equivalence that is also multiplicative — spelled out as `dAut` +
`dAut_mul` rather than through a bundled automorphism group.

The final two clauses of the proposition ("`H` has only one involution"; "if `u ≠ v` are
involutions of `G` then `|uv|` is the characteristic of `F`") are the last three fields; `char` is
the characteristic in the sense of `exists_prime_char`. -/
structure AffineNearFieldModel {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
    (hyp : RankOneHypothesis G Ω) (F : Type*) [NearField F] where
  /-- `(F, +)` embedded in `G`. -/
  emb : Multiplicative F →* G
  emb_injective : Function.Injective emb
  /-- `F ⊴ G`. -/
  range_normal : (MonoidHom.range emb).Normal
  /-- `G = F ⋊ H`. -/
  isComplement : Subgroup.IsComplement' (MonoidHom.range emb) hyp.H
  /-- `Q` is identified with `F^*`. -/
  qEquiv : ↥hyp.Q ≃* Fˣ
  /-- The identification `Q ≃* F^*` turns conjugation into right multiplication, i.e. it realizes
  `F ⋊ Q ≅ F ⋊ F^* = 𝓛(F)`. -/
  qEquiv_conj : ∀ (q : ↥hyp.Q) (x : F),
    (q : G) * emb (Multiplicative.ofAdd x) * (q : G)⁻¹
      = emb (Multiplicative.ofAdd (x * ((qEquiv q : Fˣ) : F)))
  /-- `D` acts on `F` by additive bijections … -/
  dAut : ↥hyp.D → (F ≃+ F)
  /-- … which are multiplicative, i.e. near-field automorphisms … -/
  dAut_mul : ∀ (g : ↥hyp.D) (x y : F), dAut g (x * y) = dAut g x * dAut g y
  /-- … faithfully, so that `D` *is* a group `Σ` of automorphisms of `F` … -/
  dAut_injective : Function.Injective dAut
  /-- … and the action is the conjugation action inside `G`. -/
  dAut_conj : ∀ (g : ↥hyp.D) (x : F),
    (g : G) * emb (Multiplicative.ofAdd x) * (g : G)⁻¹ = emb (Multiplicative.ofAdd (dAut g x))
  /-- `H` has exactly one involution. -/
  unique_involution_in_H : ∃! u : ↥hyp.H, (u : G) ^ 2 = 1 ∧ (u : G) ≠ 1
  /-- The characteristic of the near-field `F`. -/
  char : ℕ
  char_prime : char.Prime
  char_spec : ∀ x : F, char • x = 0
  /-- If `u ≠ v` are involutions of `G` then `|uv|` is the characteristic of `F`. -/
  orderOf_mul_of_involutions : ∀ u v : G, u ^ 2 = 1 → u ≠ 1 → v ^ 2 = 1 → v ≠ 1 → u ≠ v →
    orderOf (u * v) = char

/-- **Peterfalvi Appendix C, Proposition 1** (p. 137).  If `G` satisfies (A1) and (A2) and has
2-rank `1`, then `G` is the affine group of a finite near-field: there is a near-field `F` and a
group `Σ` of automorphisms of `F` with `G ≅ 𝓛(F) ⋊ Σ = (F ⋊ F^*) ⋊ Σ`, identifying `Q` with `F^*`
and `D` with `Σ`.  Moreover `H` has a unique involution and, for distinct involutions `u, v ∈ G`,
`|uv|` equals the characteristic of `F`.

**Status: honestly stated, not proved.**  Peterfalvi's proof consumes three results that are not
available here: (i) a Sylow 2-subgroup of `G` is cyclic or generalized quaternion (Huppert,
*Endliche Gruppen* I, Kapitel III, Satz 8.2) — 2-rank one is exactly this; (ii) the **Brauer–Suzuki
theorem** `G = O_{2'}(G) C_G(u)`, which is not formalized in this repository; (iii) Huppert Kapitel
II, Satz 3.2, giving the elementary abelian normal complement `G = F ⋊ H` for the solvable
`O_{2'}(G)` (solvable by Feit–Thompson).  With those in hand, the near-field structure on `F` comes
from the regular action of `Q` on `F^#` by the standard transport recorded on p. 137 (choose the
`D`-fixed point of `F^#` as the multiplicative identity), which *is* elementary and would be the
first piece to formalize once (i)–(iii) exist. -/
theorem rankOne_affine_nearField.{u} {G : Type u} {Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
    (hyp : RankOneHypothesis G Ω) :
    ∃ (F : Type u) (_ : NearField F), Nonempty (AffineNearFieldModel hyp F) := by
  sorry

end PropositionOne

section PropositionTwo

/-- **An order-`2` field automorphism forces square cardinality** (the twisted branch of Peterfalvi
Appendix C, Proposition 2).  If `σ : RingAut K` on a finite field `K` satisfies `σ² = 1` and
`σ ≠ 1`, then `|K|` is a perfect square `r²`, where `r = |K^σ|` is a prime power `p^n` (`n ≥ 1`).

By Artin's theorem (`FixedPoints.finrank_eq_card`) the fixed field `K^{⟨σ⟩}` satisfies
`[K : K^{⟨σ⟩}] = |⟨σ⟩| = orderOf σ = 2`, whence `|K| = |K^{⟨σ⟩}|²`; a finite field has prime-power
order.  In the classification `K = 𝔽_{r²}` and `σ : x ↦ x^r`. -/
theorem card_eq_sq_of_orderTwo_ringAut {K : Type*} [Field K] [Finite K]
    (σ : RingAut K) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    ∃ (r p n : ℕ), p.Prime ∧ 0 < n ∧ r = p ^ n ∧ Nat.card K = r ^ 2 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (RingAut K) :=
    Finite.of_injective (DFunLike.coe : RingAut K → (K → K)) DFunLike.coe_injective
  -- `⟨σ⟩ ≤ RingAut K` acts on `K`, has order `2`, and acts faithfully.
  set G := Subgroup.zpowers σ with hG
  haveI : Fintype G := Fintype.ofFinite G
  have hcardG : Fintype.card G = 2 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, orderOf_eq_prime hσ2 hσ1]
  haveI : FaithfulSMul G K :=
    ⟨fun {a b} h => Subtype.ext (RingEquiv.ext fun x => h x)⟩
  -- Artin: `[K : K^G] = |G| = 2`, hence `|K| = |K^G|²`.
  have hfr : Module.finrank (FixedPoints.subfield G K) K = 2 := by
    rw [FixedPoints.finrank_eq_card G K, hcardG]
  haveI : Fintype (FixedPoints.subfield G K) := Fintype.ofFinite _
  have hcardK : Fintype.card K = Fintype.card (FixedPoints.subfield G K) ^ 2 := by
    rw [← hfr]; exact Module.card_eq_pow_finrank
  -- `|K^G| = p^n` is a prime power with `n ≥ 1`.
  obtain ⟨p, _, n, hp, hcardFix⟩ := FiniteField.card' (FixedPoints.subfield G K)
  exact ⟨Fintype.card (FixedPoints.subfield G K), p, (n : ℕ), hp, n.pos, hcardFix, by
    rw [Nat.card_eq_fintype_card, hcardK]⟩

/-- **Peterfalvi Appendix C, Proposition 2, first half** (proved, sorry-free), stated with the
book's hypothesis: if the multiplicative group `F^*` of a finite near-field has a **cyclic**
subgroup `A` of index `2`, then `(F, +)` is a `1`-dimensional vector space over a finite field `K`
with `|K| = |F|`.

This is `nearField_field_structure_of_index_two` with the commutativity hypothesis discharged from
cyclicity; the index-`2` irreducibility (free-orbit counting + Maschke) and Appendix I's
`exists_field_semilinear` do the work. -/
theorem exists_field_structure_of_cyclic_index_two.{u} {F : Type u} [NearField F] [Finite F]
    (A : Subgroup Fˣ) (hcyc : IsCyclic ↥A) (hidx : A.index = 2) :
    ∃ (K : Type u) (_ : Field K) (_ : Module K F) (_ : Finite K),
      Module.finrank K F = 1 ∧ Nat.card K = Nat.card F := by
  have hcomm : ∀ u v : ↥A, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ) := by
    letI : CommGroup ↥A := hcyc.commGroup
    intro u v
    simpa using congrArg Subtype.val (mul_comm u v)
  exact nearField_field_structure_of_index_two A hcomm hidx

/-- **Peterfalvi Appendix C, Proposition 2** (pp. 137--138).  Let `F` be a finite near-field whose
multiplicative group `F^*` has a **cyclic** subgroup `A` of index `2`.  Then either `F` is a field
(equivalently, by `NearField.mul_add_of_mul_comm`, its multiplication is commutative), or there is
an `r` which is a power of an odd prime such that `F ≅ F_{r²,2}` — the twisted near-field carried by
`TwistData` on `K = 𝔽_{r²}` — and in that case `|Z(F^*)| = r - 1`.

An isomorphism of near-fields is an additive equivalence that is also multiplicative, spelled out
here rather than bundled.

**Status: honestly stated, `sorry`.**  The first half of Peterfalvi's proof is **proved**, in this
file, sorry-free: `rightMulAction_irreducible_of_index_two` is the counting argument
`|F| = 2|A| + 1 ≥ (|A|+1)²` ruling out a proper invariant decomposition, and
`exists_field_structure_of_cyclic_index_two` (cited in the proof below) is the resulting field
structure via Appendix I, Proposition 2.

What remains is the *tail*: normalize the field `K` obtained from `exists_field_semilinear` so that
its unit `1` is the near-field unit and `x ∘ y = x·y` for `y ∈ A` (the module structure only gives
`finrank = 1`, so the normalization is the choice of basis vector `1`), then run the semilinearity
clause of `exists_field_semilinear` to produce the homomorphism `y ↦ σ_y` from `F^*` to `Aut K`
whose kernel contains `A`, split on whether that kernel is all of `F^*` (field case) or of index `2`
(then `σ_y : x ↦ x^r` and `F ≅ F_{r²,2}`), and finally compute `Z(F^*) = 𝔽_r^*` from
`x ∈ Z(F^*) ↔ x^r = x`.  The missing formal prerequisite is the normalized transport of the
`exists_field_semilinear` output onto the near-field `F` itself (a `Module K F` with `finrank 1` has
to be converted into a *field structure on `F`* sharing `+` and `1` with the near-field); no piece
of this is in the repository yet. -/
theorem cyclic_index_two_nearField_classification.{u} {F : Type u} [NearField F] [Finite F]
    (A : Subgroup Fˣ) (hcyc : IsCyclic ↥A) (hidx : A.index = 2) :
    (∀ x y : F, x * y = y * x) ∨
      ∃ (r : ℕ) (K : Type u) (_ : Field K) (_ : Finite K) (d : TwistData K),
        (∃ p n : ℕ, p.Prime ∧ Odd p ∧ 0 < n ∧ r = p ^ n) ∧
        Nat.card K = r ^ 2 ∧
        (∃ e : F ≃+ Twisted d, ∀ x y : F, e (x * y) = e x * e y) ∧
        Nat.card ↥(Subgroup.center Fˣ) = r - 1 := by
  classical
  -- `A` is commutative (cyclic) and acts irreducibly on `(F,+) = Multiplicative F` by right mult.
  have hcomm : ∀ u v : ↥A, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ) := by
    letI : CommGroup ↥A := hcyc.commGroup
    intro u v
    simpa using congrArg Subtype.val (mul_comm u v)
  letI : CommGroup ↥A := hcyc.commGroup
  have hirr := rightMulAction_irreducible_of_index_two A hcomm hidx
  obtain ⟨f, hf, hE⟩ := isElementaryAbelian_multiplicative (F := F)
  haveI : Fact f.Prime := ⟨hf⟩
  haveI : Nontrivial (Multiplicative F) := inferInstanceAs (Nontrivial F)
  -- the semilinear field `K` with the scalar realization `μ` of the `A`-action
  obtain ⟨K, hKfield, hKmod, hKfin, hrank, hcardKE, ⟨μ, hμ⟩, hσfam⟩ :=
    OddOrder.Peterfalvi.Appendices.Huppert.exists_field_semilinear_with_scalar
      (E := Multiplicative F) hE (rightMulAction A hcomm) hirr
  letI : Module K F := hKmod
  -- scalar clause in near-field terms: `(μ a) • x = x * (a : F)` for `a ∈ A`, `x ∈ F`
  have hμ' : ∀ (a : ↥A) (x : F), (μ a : K) • x = x * ((a : Fˣ) : F) := fun a x => hμ a x
  -- the `K`-linear iso `Θ : K ≃ₗ[K] F`, `a ↦ a • 1`; `Θ 1 = 1` normalizes the unit.
  have hrankF : Module.finrank K F = 1 := hrank
  have h1ne : (1 : F) ≠ 0 := one_ne_zero
  set L : K →ₗ[K] F := LinearMap.toSpanSingleton K F (1 : F) with hL
  have hLinj : Function.Injective L :=
    LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton (R := K) h1ne)
  have hLsurj : Function.Surjective L := by
    intro w
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : F) h1ne).mp hrankF w
    exact ⟨c, hc⟩
  set Θ : K ≃ₗ[K] F := LinearEquiv.ofBijective L ⟨hLinj, hLsurj⟩ with hΘdef
  have hΘ : ∀ a : K, Θ a = a • (1 : F) := fun a => rfl
  have hΘ1 : Θ 1 = 1 := by rw [hΘ, one_smul]
  -- `μ` is injective and `μ a` is the `K`-coordinate of `a : A`, i.e. `Θ (μ a) = (a : F)`.
  have hμcoord : ∀ a : ↥A, Θ (μ a) = ((a : Fˣ) : F) := by
    intro a; rw [hΘ, hμ' a 1, one_mul]
  have hμinj : Function.Injective μ := by
    intro a b hab
    have : ((a : Fˣ) : F) = ((b : Fˣ) : F) := by rw [← hμcoord a, ← hμcoord b, hab]
    exact Subtype.ext (Units.ext (by exact_mod_cast this))
  -- right-multiplication as an automorphism, and its value on `F`.
  have hR : ∀ (u : ↥A) (x : F), (rightMulAction A hcomm u) x = x * ((u : Fˣ) : F) :=
    fun _ _ => rfl
  -- `A` is normal (index 2); choose `y₀ ∉ A` and the right-multiplication automorphism `g₀`.
  haveI hAnormal : A.Normal := Subgroup.normal_of_index_eq_two hidx
  have hAne : A ≠ ⊤ := fun h => by rw [h, Subgroup.index_top] at hidx; exact absurd hidx (by norm_num)
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Fˣ, y₀ ∉ A := by
    by_contra h; push_neg at h; exact hAne (eq_top_iff.mpr fun x _ => h x)
  set g₀ : MulAut (Multiplicative F) :=
    (rightMul ((y₀ : Fˣ) : F) (Units.ne_zero y₀)).toMultiplicative with hg₀def
  have hg₀toAdd : ∀ x : Multiplicative F,
      Multiplicative.toAdd (g₀ x) = Multiplicative.toAdd x * ((y₀ : Fˣ) : F) := fun _ => rfl
  set c₀ : ↥A ≃* ↥A := OddOrder.RepresentationTheory.conjNormalMulAut A y₀⁻¹ with hc₀def
  have hc₀coe : ∀ t : ↥A, ((c₀ t : Fˣ) : F) = ((y₀⁻¹ * (t : Fˣ) * y₀ : Fˣ) : F) := by
    intro t
    have h : (c₀ t : Fˣ) = y₀⁻¹ * (t : Fˣ) * y₀ := by
      rw [hc₀def, OddOrder.RepresentationTheory.conjNormalMulAut_apply_coe, inv_inv]
    rw [h]
  -- the normalization hypothesis `ψ (c₀ t) = g₀ ψ t g₀⁻¹`, via near-field associativity.
  have hconj : ∀ t : ↥A, g₀ * rightMulAction A hcomm t = rightMulAction A hcomm (c₀ t) * g₀ := by
    intro t
    refine MulEquiv.ext (fun x => Multiplicative.toAdd.injective ?_)
    simp only [MulAut.mul_apply, hg₀toAdd, rightMulAction_toAdd, hc₀coe]
    push_cast
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero y₀), one_mul]
  have hcond : ∀ t : ↥A, rightMulAction A hcomm (c₀ t) = g₀ * rightMulAction A hcomm t * g₀⁻¹ :=
    fun t => by rw [hconj t]; group
  -- extract the field automorphism `σ` realizing right multiplication by `y₀`.
  obtain ⟨σ, hσ⟩ := hσfam g₀ c₀ hcond
  have htoAddg₀ : ∀ x : F, (MulEquiv.toAdditive g₀) x = x * ((y₀ : Fˣ) : F) := fun _ => rfl
  -- semilinearity in near-field terms: `(a • x) * y₀ = σ(a) • (x * y₀)`.
  have hσNF : ∀ (a : K) (x : F), (a • x) * ((y₀ : Fˣ) : F) = σ a • (x * ((y₀ : Fˣ) : F)) := by
    intro a x
    have := hσ a x
    rw [htoAddg₀, htoAddg₀] at this
    exact this
  -- scaling by a nonzero vector is injective (finrank-1 ⟹ no zero divisors).
  have hsmul_inj : ∀ (w : F), w ≠ 0 → ∀ a b : K, a • w = b • w → a = b := by
    intro w hw a b hab
    have h0 : (a - b) • w = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw
  -- `y₀² ∈ A` (index 2), so right multiplication by `y₀²` is a scalar.
  have hy₀sq : (y₀ * y₀ : Fˣ) ∈ A := by
    haveI : Fintype (Fˣ ⧸ A) := Fintype.ofFinite _
    have hcard : Fintype.card (Fˣ ⧸ A) = 2 := by rw [← Nat.card_eq_fintype_card]; exact hidx
    have hmk : (QuotientGroup.mk (y₀ * y₀) : Fˣ ⧸ A) = 1 := by
      rw [QuotientGroup.mk_mul, ← sq, ← hcard]; exact pow_card_eq_one
    exact (QuotientGroup.eq_one_iff _).mp hmk
  -- `σ² = 1`: applying `hσNF` twice equals the scalar action of `y₀²`.
  have hdouble : ∀ (s : K) (x : F),
      (s • x) * ((y₀ : Fˣ) : F) * ((y₀ : Fˣ) : F)
        = σ (σ s) • (x * ((y₀ : Fˣ) : F) * ((y₀ : Fˣ) : F)) := by
    intro s x
    rw [hσNF s x, hσNF (σ s) (x * ((y₀ : Fˣ) : F))]
  have hσσ : ∀ s : K, σ (σ s) = s := by
    intro s
    have hwne : ((y₀ : Fˣ) : F) * ((y₀ : Fˣ) : F) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
    have hzw : ∀ z : F,
        z * (((y₀ : Fˣ) : F) * ((y₀ : Fˣ) : F)) = (μ ⟨y₀ * y₀, hy₀sq⟩ : K) • z := by
      intro z
      have h := hμ' ⟨y₀ * y₀, hy₀sq⟩ z
      have hcoe : (((⟨y₀ * y₀, hy₀sq⟩ : ↥A) : Fˣ) : F) = ((y₀ : Fˣ) : F) * ((y₀ : Fˣ) : F) :=
        Units.val_mul y₀ y₀
      rw [hcoe] at h; exact h.symm
    have hLHS : (s • (1 : F)) * ((y₀ : Fˣ) : F) * ((y₀ : Fˣ) : F)
        = s • (((y₀ : Fˣ) : F) * ((y₀ : Fˣ) : F)) := by
      rw [mul_assoc, hzw (s • 1), ← mul_smul, mul_comm _ s, mul_smul, ← hzw (1 : F), one_mul]
    have hd := hdouble s 1
    rw [one_mul, hLHS] at hd
    exact (hsmul_inj _ hwne _ _ hd).symm
  have hσ2 : σ ^ 2 = 1 := by
    ext s; rw [pow_two]; exact hσσ s
  -- right multiplication by a unit is `id`-semilinear for `y ∈ A`, `σ`-semilinear for `y ∉ A`.
  have hUmulA : ∀ (s : K) (x : F) (a : ↥A),
      (s • x) * ((a : Fˣ) : F) = s • (x * ((a : Fˣ) : F)) := by
    intro s x a
    rw [← hμ' a (s • x), ← mul_smul, mul_comm _ s, mul_smul, hμ' a x]
  have hUmulNA : ∀ (s : K) (x : F) (y : Fˣ), y ∉ A →
      (s • x) * ((y : Fˣ) : F) = σ s • (x * ((y : Fˣ) : F)) := by
    intro s x y hy
    have ha : y₀⁻¹ * y ∈ A :=
      (Subgroup.mul_mem_iff_of_index_two hidx).mpr
        (iff_of_false (fun h => hy₀ (by simpa using inv_mem h)) hy)
    have hyval : ((y : Fˣ) : F) = ((y₀ : Fˣ) : F) * (((⟨y₀⁻¹ * y, ha⟩ : ↥A) : Fˣ) : F) := by
      show ((y : Fˣ) : F) = ((y₀ : Fˣ) : F) * ((y₀⁻¹ * y : Fˣ) : F)
      rw [← Units.val_mul]; congr 1; group
    rw [hyval, ← mul_assoc, hσNF s x, hUmulA (σ s) (x * ((y₀ : Fˣ) : F)) ⟨y₀⁻¹ * y, ha⟩, mul_assoc]
  -- dichotomy on whether `σ` is trivial.
  rcases eq_or_ne σ 1 with hσeq | hσne
  · -- **Field case** (`σ = 1`): every right multiplication is `K`-linear, so `F` is commutative.
    left
    have hlin : ∀ (s : K) (x : F) (y : Fˣ),
        (s • x) * ((y : Fˣ) : F) = s • (x * ((y : Fˣ) : F)) := by
      intro s x y
      by_cases hy : y ∈ A
      · exact hUmulA s x ⟨y, hy⟩
      · rw [hUmulNA s x y hy, hσeq]; rfl
    have hΘmul : ∀ (a : K) (y : F), y ≠ 0 → Θ a * y = a • y := by
      intro a y hy
      have h := hlin a 1 (Units.mk0 y hy)
      simp only [Units.val_mk0, one_mul] at h
      rw [hΘ a]; exact h
    have hxy : ∀ x y : F, y ≠ 0 → x * y = Θ (Θ.symm x * Θ.symm y) := by
      intro x y hy
      rw [hΘ (Θ.symm x * Θ.symm y), mul_smul, ← hΘ (Θ.symm y), Θ.apply_symm_apply,
        ← hΘmul (Θ.symm x) y hy, Θ.apply_symm_apply]
    intro x y
    rcases eq_or_ne y 0 with rfl | hy
    · rw [mul_zero, zero_mul]
    rcases eq_or_ne x 0 with rfl | hx
    · rw [zero_mul, mul_zero]
    rw [hxy x y hy, hxy y x hx, mul_comm (Θ.symm x) (Θ.symm y)]
  · -- **Twisted case** (`σ ≠ 1`): `F ≅ F_{r²,2}`.
    right
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨r, p, n, hp, hn, hrpn, hcardKr⟩ := card_eq_sq_of_orderTwo_ringAut σ hσ2 hσne
    have hKF : Nat.card K = Nat.card F := hcardKE
    have hFodd : Odd (Nat.card F) := by
      rw [card_eq_of_index_two A hidx]; exact ⟨Nat.card ↥A, by ring⟩
    have hpodd : Odd p := by
      rcases hp.eq_two_or_odd' with h2 | hodd
      · exfalso
        have he : Even (Nat.card K) := by
          rw [hcardKr, hrpn, h2, ← pow_mul]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
        rw [hKF] at he
        obtain ⟨m, hm⟩ := he; obtain ⟨k, hk⟩ := hFodd; omega
      · exact hodd
    -- `B := range μ` is an index-2 subgroup of `Kˣ`.
    set B : Subgroup Kˣ := MonoidHom.range μ with hBdef
    have hBcard : Nat.card ↥B = Nat.card ↥A :=
      (Nat.card_congr (MonoidHom.ofInjective hμinj).toEquiv).symm
    have hKxcard : Nat.card Kˣ = 2 * Nat.card ↥A := by
      rw [Nat.card_units, hKF, card_eq_of_index_two A hidx]; omega
    have hBindex : B.index = 2 := by
      have h := Subgroup.card_mul_index B
      rw [hBcard, hKxcard, mul_comm 2 (Nat.card ↥A)] at h
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
    haveI : B.Normal := Subgroup.normal_of_index_eq_two hBindex
    -- `χ : Kˣ →* Multiplicative (ZMod 2)` via the order-2 quotient `Kˣ ⧸ B`.
    have hQcard : Nat.card (Kˣ ⧸ B) = 2 := hBindex
    have hM2card : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]; rfl
    set φ : Kˣ ⧸ B ≃* Multiplicative (ZMod 2) :=
      mulEquivOfPrimeCardEq (p := 2) hQcard hM2card with hφdef
    set χ : Kˣ →* Multiplicative (ZMod 2) := φ.toMonoidHom.comp (QuotientGroup.mk' B) with hχdef
    have hχone : ∀ u : Kˣ, χ u = 1 ↔ u ∈ B := by
      intro u
      rw [hχdef]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.coe_mk']
      rw [map_eq_one_iff φ (EquivLike.injective φ), QuotientGroup.eq_one_iff]
    -- `mk0 c ∈ B` iff `Θ c`'s `F`-unit lies in `A`.
    have hBA : ∀ (c : K) (hc : c ≠ 0),
        Units.mk0 c hc ∈ B ↔ ∃ a : ↥A, ((a : Fˣ) : F) = Θ c := by
      intro c hc
      constructor
      · rintro ⟨a, ha⟩
        refine ⟨a, ?_⟩
        have hac : (μ a : K) = c := by rw [ha]; rfl
        rw [← hμcoord a, hac]
      · rintro ⟨a, ha⟩
        refine ⟨a, ?_⟩
        have hΘeq : Θ ((μ a : K)) = Θ c := by rw [hμcoord a, ha]
        exact Units.ext (Θ.injective hΘeq)
    -- `σ` preserves `B = range μ` via `σ(μ a) = μ(y₀⁻¹ a y₀)`, giving `χ_σ`.
    have hZ2 : ∀ z : ZMod 2, z ≠ 0 → z = 1 := fun z hz => by
      fin_cases z
      · exact absurd rfl hz
      · rfl
    have hσμ : ∀ a : ↥A, ∃ a' : ↥A, σ (μ a : K) = (μ a' : K) := by
      intro a
      have hca : y₀⁻¹ * (a : Fˣ) * y₀ ∈ A := by
        have := hAnormal.conj_mem (a : Fˣ) a.2 y₀⁻¹; rwa [inv_inv] at this
      refine ⟨⟨y₀⁻¹ * (a : Fˣ) * y₀, hca⟩, ?_⟩
      apply hsmul_inj ((1 : F) * ((y₀ : Fˣ) : F)) (by rw [one_mul]; exact Units.ne_zero _)
      rw [← hσNF (μ a) 1, hμ' a 1, hμ' ⟨y₀⁻¹ * (a : Fˣ) * y₀, hca⟩ ((1 : F) * ((y₀ : Fˣ) : F)),
        one_mul, one_mul]
      have hbcoe : ((⟨y₀⁻¹ * (a : Fˣ) * y₀, hca⟩ : ↥A) : Fˣ) = y₀⁻¹ * (a : Fˣ) * y₀ := rfl
      rw [hbcoe, ← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    have hmemB : ∀ y : Kˣ, y ∈ B → Units.map (σ : K →* K) y ∈ B := by
      intro y hy
      obtain ⟨a, ha⟩ := hy
      obtain ⟨a', ha'⟩ := hσμ a
      refine ⟨a', ?_⟩
      apply Units.ext
      show (μ a' : K) = σ (y : K)
      rw [← ha', ha]
    have hσU2 : ∀ y : Kˣ, Units.map (σ : K →* K) (Units.map (σ : K →* K) y) = y := by
      intro y; apply Units.ext
      show σ (σ (y : K)) = (y : K)
      exact hσσ (y : K)
    have hpres : ∀ y : Kˣ, Units.map (σ : K →* K) y ∈ B ↔ y ∈ B := by
      intro y
      refine ⟨fun h => ?_, hmemB y⟩
      have := hmemB _ h; rwa [hσU2 y] at this
    have hkey2 : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by
      intro a b ha hb
      apply Multiplicative.toAdd.injective
      rw [hZ2 _ (fun h => ha (Multiplicative.toAdd.injective (h.trans toAdd_one.symm))),
        hZ2 _ (fun h => hb (Multiplicative.toAdd.injective (h.trans toAdd_one.symm)))]
    have hχσ : ∀ y : Kˣ, χ (Units.map (σ : K →* K) y) = χ y := by
      intro y
      by_cases hy : y ∈ B
      · rw [(hχone _).mpr ((hpres y).mpr hy), (hχone _).mpr hy]
      · exact hkey2 _ _ (fun h => hy ((hpres y).mp ((hχone _).mp h)))
          (fun h => hy ((hχone _).mp h))
    -- the twisting data and the near-field isomorphism.
    let d : TwistData K := ⟨σ, hσ2, χ, hχσ⟩
    have hΘc_ne : ∀ c : K, c ≠ 0 → Θ c ≠ 0 := fun c hc h => hc (Θ.injective (by rw [h, map_zero]))
    have hZ2 : ∀ z : ZMod 2, z ≠ 0 → z = 1 := fun z hz => by
      fin_cases z
      · exact absurd rfl hz
      · rfl
    have hmulΘ : ∀ a c : K, Θ a * Θ c = Θ (d.twMul a c) := by
      intro a c
      rcases eq_or_ne c 0 with rfl | hc
      · rw [map_zero, mul_zero, TwistData.twMul_zero, map_zero]
      · have hexp : d.twExp c = Multiplicative.toAdd (χ (Units.mk0 c hc)) := by
          unfold TwistData.twExp; rw [dif_neg hc]
        by_cases hmem : ∃ a' : ↥A, ((a' : Fˣ) : F) = Θ c
        · obtain ⟨a', ha'⟩ := hmem
          have hχ1 : χ (Units.mk0 c hc) = 1 := (hχone _).mpr ((hBA c hc).mpr ⟨a', ha'⟩)
          have hlhs : Θ a * Θ c = Θ (a * c) := by
            rw [hΘ a, ← ha', hUmulA a 1 a', one_mul, ha', hΘ c, ← mul_smul, hΘ]
          have htw : d.twMul a c = a * c := by
            show d.twAut (d.twExp c) a * c = a * c
            rw [hexp, hχ1, toAdd_one, TwistData.twAut_zero]; rfl
          rw [hlhs, htw]
        · have hΘc := hΘc_ne c hc
          have hyNA : (Units.mk0 (Θ c) hΘc) ∉ A := fun hA => hmem ⟨⟨_, hA⟩, rfl⟩
          have hχn1 : χ (Units.mk0 c hc) ≠ 1 :=
            fun h => hmem ((hBA c hc).mp ((hχone _).mp h))
          have hexp1 : d.twExp c = 1 := by
            rw [hexp]
            exact hZ2 _ (fun h => hχn1 (Multiplicative.toAdd.injective (h.trans toAdd_one.symm)))
          have hlhs : Θ a * Θ c = Θ (σ a * c) := by
            have hu := hUmulNA a 1 (Units.mk0 (Θ c) hΘc) hyNA
            simp only [Units.val_mk0, one_mul] at hu
            rw [hΘ a, hu, hΘ c, ← mul_smul, hΘ]
          have htw : d.twMul a c = σ a * c := by
            show d.twAut (d.twExp c) a * c = σ a * c
            rw [hexp1, TwistData.twAut_one]
          rw [hlhs, htw]
    have hiso : ∀ x y : F, Θ.symm (x * y) = d.twMul (Θ.symm x) (Θ.symm y) := by
      intro x y
      have h := hmulΘ (Θ.symm x) (Θ.symm y)
      rw [Θ.apply_symm_apply, Θ.apply_symm_apply] at h
      rw [h, Θ.symm_apply_apply]
    refine ⟨r, K, hKfield, hKfin, d, ⟨p, n, hp, hpodd, hn, hrpn⟩, hcardKr,
      ⟨(Θ.symm.toAddEquiv : F ≃+ Twisted d), fun x y => hiso x y⟩, ?_⟩
    -- `|Z(Fˣ)| = r - 1`.
    sorry

end PropositionTwo

end OddOrder.Peterfalvi.Appendices.NearFields
