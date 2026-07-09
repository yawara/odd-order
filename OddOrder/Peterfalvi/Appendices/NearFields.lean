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
-/

namespace OddOrder.Peterfalvi.Appendices.NearFields
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

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

section NearFieldBasics

variable {F : Type*} [NearField F]

/-- Right multiplication by a nonzero element is an additive automorphism of a near-field: it is
additive by the right distributive law, and bijective because `a` is invertible. -/
def rightMul (a : F) (ha : a ≠ 0) : F ≃+ F where
  toFun x := x * a
  invFun x := x * a⁻¹
  left_inv x := by show (x * a) * a⁻¹ = x; rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
  right_inv x := by show (x * a⁻¹) * a = x; rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]
  map_add' x y := NearField.add_mul x y a

@[simp] theorem rightMul_apply (a : F) (ha : a ≠ 0) (x : F) : rightMul a ha x = x * a := rfl

/-- All nonzero elements of a near-field have the same additive order: `F^*` acts transitively on
`F^#` by right multiplication (`rightMul`), an additive automorphism. -/
theorem addOrderOf_eq_of_ne_zero (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    addOrderOf x = addOrderOf y := by
  have hne : x⁻¹ * y ≠ 0 := mul_ne_zero (inv_ne_zero hx) hy
  have hxy : y = (rightMul (x⁻¹ * y) hne) x := by
    show y = x * (x⁻¹ * y); rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
  rw [hxy]
  exact (addOrderOf_injective (rightMul (x⁻¹ * y) hne).toAddMonoidHom
    (rightMul (x⁻¹ * y) hne).injective x).symm

/-- **The characteristic of a finite near-field is a prime** (Peterfalvi, Appendix C, p. 137: "`F`
is an elementary abelian `f`-group for some prime `f`"): there is a prime `f` with `f • x = 0` for
all `x ∈ F`.  Since all nonzero elements share one additive order (`addOrderOf_eq_of_ne_zero`),
that order is forced to be prime by the divisor argument; this makes `(F, +)` elementary abelian. -/
theorem exists_prime_char [Finite F] [Nontrivial F] :
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
theorem isElementaryAbelian_multiplicative [Finite F] [Nontrivial F] :
    ∃ f : ℕ, f.Prime ∧ OddOrder.GroupTheory.IsElementaryAbelian f (Multiplicative F) := by
  obtain ⟨f, hf, hfx⟩ := exists_prime_char (F := F)
  refine ⟨f, hf, fun x y => mul_comm x y, fun x => ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  exact hfx (Multiplicative.toAdd x)

/-- The right-multiplication action of a commutative subgroup `A ⊆ Fˣ` on `(F, +)` (written
multiplicatively), as a monoid homomorphism into `MulAut (Multiplicative F)`.  Right multiplication
is additive (`rightMul`); the homomorphism property needs `A` commutative (`hcomm`), since right
multiplication is otherwise only an anti-homomorphism.  Together with `isElementaryAbelian_multiplicative`
this is the data fed to Appendix I's `exists_field_semilinear`. -/
noncomputable def rightMulAction (A : Subgroup Fˣ)
    (hcomm : ∀ u v : A, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ)) :
    A →* MulAut (Multiplicative F) where
  toFun u := (rightMul ((u : Fˣ) : F) (Units.ne_zero _)).toMultiplicative
  map_one' := by
    ext x
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd x * (((1 : A) : Fˣ) : F) = Multiplicative.toAdd x
    rw [OneMemClass.coe_one, Units.val_one, mul_one]
  map_mul' u v := by
    ext x
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd x * (((u * v : A) : Fˣ) : F)
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
theorem nearField_field_structure.{u} {F : Type u} [NearField F] [Finite F] [Nontrivial F]
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
theorem rightMulAction_irreducible_of_index_two {F : Type*} [NearField F] [Finite F] [Nontrivial F]
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
    [Nontrivial F] (A : Subgroup Fˣ)
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

/-- Composing the twist automorphisms adds their exponents: `twAut a (twAut b x) = twAut (a+b) x`. -/
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
      show d.twAut (d.twExp (0 : K)) (0 : K)⁻¹ = (0 : K)
      simp
    mul_inv_cancel := fun a ha => d.twMul_twInv ha
    exists_pair_ne := ⟨(0 : K), (1 : K), (zero_ne_one : (0 : K) ≠ 1)⟩
    right_distrib := d.add_twMul }

end Twisted

end TwistedNearField

variable {G Ω F : Type*} [Group G]

/-- A lightweight carrier for finite near-field structure.  The algebraic laws
are proposition fields until a reusable near-field API is introduced. -/
structure FiniteNearField where
  carrier_nonempty : Nonempty F
  finite : Prop
  finite_holds : finite
  additive_group : Prop
  additive_group_holds : additive_group
  multiplicative_group : Prop
  multiplicative_group_holds : multiplicative_group
  right_distrib : Prop
  right_distrib_holds : right_distrib

/-- **Peterfalvi Appendix C, Proposition 1**: a 2-rank one group satisfying
Suzuki hypotheses (A1)--(A2) is an affine group over a finite near-field. -/
structure RankOneNearFieldData
    (hyp : Suzuki.Hypothesis (G := G) (Ω := Ω)) where
  nearField : FiniteNearField (F := F)
  Sigma : Type*
  affine_model : Prop
  affine_model_holds : affine_model
  Q_identification : Prop
  Q_identification_holds : Q_identification
  D_identification : Prop
  D_identification_holds : D_identification
  unique_involution_in_H : Prop
  unique_involution_in_H_holds : unique_involution_in_H

/-- **Peterfalvi Appendix C, Proposition 1**. -/
theorem rankOne_affine_nearField [Finite G]
    (hyp : Suzuki.Hypothesis (G := G) (Ω := Ω))
    (two_rank_one : Prop) :
    two_rank_one → ∃ data : RankOneNearFieldData (F := F) hyp,
      data.affine_model := by
  sorry

/-- **Peterfalvi Appendix C, Proposition 2**: a finite near-field whose
multiplicative group has a cyclic subgroup of index two is either a field or the
exceptional near-field `F_{r^2,2}`. -/
theorem cyclic_index_two_nearField_classification
    (nearField : FiniteNearField (F := F)) (cyclic_index_two : Prop) :
    cyclic_index_two → ∃ classification : Prop, classification := by
  sorry

end OddOrder.Peterfalvi.Appendices.NearFields
