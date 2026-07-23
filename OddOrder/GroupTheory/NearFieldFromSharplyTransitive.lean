/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Abel
import OddOrder.Peterfalvi.Appendices.NearFieldClass

/-!
# Near-field from a sharply transitive additive action

Peterfalvi, *Character Theory for the Odd Order Theorem*, Appendix C, p. 137 (the "transport"
recorded in the proof of Proposition 1): if a group `M` acts on an additive abelian group `A` by
*additive* automorphisms, **regularly on the nonzero elements** `A ∖ {0}` (sharply transitive),
then `A` carries a near-field structure whose multiplicative group `A∖{0}` is isomorphic to `M`.

Concretely, fix an element `e ≠ 0` (the multiplicative identity — in the group case, the `D`-fixed
point of `F#`).  For `y ≠ 0` let `m_y ∈ M` be the *unique* element with `m_y • e = y`; define

`x * y := m_y • x`   (and `x * 0 := 0`).

Then `(A, +, *)` is a near-field (`NearField`):

* associativity `(x*y)*z = x*(y*z)` follows from `m_{m_z • y} = m_z * m_y` (uniqueness of `m`);
* `e` is a two-sided identity (`m_e = 1`);
* every `y ≠ 0` is invertible (`y⁻¹ := m_y⁻¹ • e`);
* the **right** distributive law `(x + y)*z = x*z + y*z` is exactly additivity of `z ↦ m_z • ·`.

The construction is packaged through `SharplyTransitiveData`.  This is the elementary core of the
affine near-field model (`AffineNearFieldModel`) of Appendix C, Proposition 1.
-/

open OddOrder.Peterfalvi.Appendices.NearFields (NearField)

namespace OddOrder.GroupTheory

/-- A `MulDistribMulAction M α` on a commutative group `α` (a monoid `M` acting by group
automorphisms) transports to a `DistribMulAction` of `M` on the additive type tag `Additive α`:
the action fixes `0 = Additive.ofMul 1` and is additive because it is multiplicative on `α`.

This is the bridge that turns a conjugation action of a group `Q` on a normal *abelian* subgroup
`F` into the `[DistribMulAction Q (Additive F)]` that `SharplyTransitiveData` consumes. -/
@[reducible] def MulDistribMulAction.toDistribMulActionAdditive {M α : Type*} [Monoid M]
    [CommGroup α] [MulDistribMulAction M α] : DistribMulAction M (Additive α) where
  smul m a := Additive.ofMul (m • a.toMul)
  one_smul a := by
    change Additive.ofMul ((1 : M) • a.toMul) = a
    rw [one_smul]; rfl
  mul_smul m n a := by
    change Additive.ofMul ((m * n) • a.toMul)
      = Additive.ofMul (m • (Additive.ofMul (n • a.toMul)).toMul)
    rw [mul_smul]; rfl
  smul_zero m := by
    change Additive.ofMul (m • (1 : α)) = (0 : Additive α)
    rw [smul_one]; rfl
  smul_add m a b := by
    change Additive.ofMul (m • (a.toMul * b.toMul))
      = Additive.ofMul (m • a.toMul) + Additive.ofMul (m • b.toMul)
    rw [smul_mul']; rfl

open scoped IsMulCommutative in
/-- The **conjugation action** of a subgroup `Q ≤ G` on the additive group `Additive ↥F` of a
normal *abelian* subgroup `F ⊴ G`: `q • Additive.ofMul f = Additive.ofMul (q f q⁻¹)`.

This is the `DistribMulAction` that feeds `SharplyTransitiveData` in the affine near-field transport
(Peterfalvi App. C, Prop 1): `F ⋊ Q` with `Q` sharply transitive on `F ∖ {1}` becomes the affine
near-field group `𝓛(F) = F ⋊ F^*`. -/
@[reducible] noncomputable def conjAdditiveAction {G : Type*} [Group G] (F Q : Subgroup G)
    [F.Normal] [IsMulCommutative ↥F] : DistribMulAction ↥Q (Additive ↥F) :=
  letI : DistribMulAction (ConjAct G) (Additive ↥F) :=
    MulDistribMulAction.toDistribMulActionAdditive
  DistribMulAction.compHom (Additive ↥F)
    ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp Q.subtype)

open scoped IsMulCommutative in
/-- Unfolding the conjugation action: `(q • a)` is conjugation of `a` by `q` inside `G`. -/
theorem conjAdditiveAction_val_toMul {G : Type*} [Group G] {F Q : Subgroup G} [F.Normal]
    [IsMulCommutative ↥F] (q : ↥Q) (a : Additive ↥F) :
    letI := conjAdditiveAction F Q
    (((q • a).toMul : ↥F) : G) = (q : G) * ((a.toMul : ↥F) : G) * (q : G)⁻¹ := rfl

variable {M A : Type*} [Group M] [AddCommGroup A] [DistribMulAction M A]

/-- **Data for the near-field transport** (Peterfalvi App. C, p. 137): a group `M` acting on the
additive abelian group `A` by additive automorphisms (`DistribMulAction`), *regularly on the
nonzero elements* — for every `y ≠ 0` there is a unique `m ∈ M` sending the chosen identity `e` to
`y`. -/
structure SharplyTransitiveData (M A : Type*) [Group M] [AddCommGroup A] [DistribMulAction M A]
    where
  /-- The multiplicative identity of the near-field (the `D`-fixed point of `F#`). -/
  e : A
  /-- `e ≠ 0`, so the near-field is nontrivial. -/
  e_ne_zero : e ≠ 0
  /-- `M` acts sharply transitively on `A ∖ {0}`: each nonzero `y` is `m • e` for a unique `m`. -/
  reg : ∀ y : A, y ≠ 0 → ∃! m : M, m • e = y

namespace SharplyTransitiveData

variable (d : SharplyTransitiveData M A)

/-- The unique `m ∈ M` with `m • e = y`, for `y ≠ 0` (and `1` for `y = 0`, an unused convention). -/
noncomputable def coord (y : A) : M := by
  classical exact if hy : y = 0 then 1 else (d.reg y hy).choose

theorem coord_smul_e {y : A} (hy : y ≠ 0) : d.coord y • d.e = y := by
  rw [coord, dif_neg hy]; exact (d.reg y hy).choose_spec.1

/-- Uniqueness: any `m` with `m • e = y` equals `coord y` (for `y ≠ 0`). -/
theorem coord_unique {y : A} (hy : y ≠ 0) {m : M} (hm : m • d.e = y) : m = d.coord y := by
  rw [coord, dif_neg hy]; exact (d.reg y hy).choose_spec.2 m hm

/-- `m • e ≠ 0` for any `m` (as `e ≠ 0` and `m` is invertible). -/
theorem smul_e_ne_zero (m : M) : m • d.e ≠ 0 := by
  intro h
  exact d.e_ne_zero (by rw [← smul_zero m⁻¹, ← h, inv_smul_smul])

/-- The near-field multiplication `x * y = (coord y) • x` (and `x * 0 = 0`). -/
noncomputable def mul (x y : A) : A := by
  classical exact if _hy : y = 0 then 0 else d.coord y • x

theorem mul_def {x y : A} (hy : y ≠ 0) : d.mul x y = d.coord y • x := dif_neg hy

@[simp] theorem mul_zero (x : A) : d.mul x 0 = 0 := dif_pos rfl

@[simp] theorem zero_mul (x : A) : d.mul 0 x = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [d.mul_def hx, smul_zero]

theorem coord_e : d.coord d.e = 1 := (d.coord_unique d.e_ne_zero (one_smul M d.e)).symm

@[simp] theorem mul_e (x : A) : d.mul x d.e = x := by rw [d.mul_def d.e_ne_zero, coord_e, one_smul]

@[simp] theorem e_mul (x : A) (hx : x ≠ 0) : d.mul d.e x = x := by
  rw [d.mul_def hx, coord_smul_e d hx]

/-- `x * y = 0 ↔ x = 0 ∨ y = 0` (no zero divisors): `(coord y) • x = 0` forces `x = 0`. -/
theorem mul_eq_zero_iff {x y : A} : d.mul x y = 0 ↔ x = 0 ∨ y = 0 := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [d.mul_def hy]
    constructor
    · intro h
      refine Or.inl ?_
      rw [← inv_smul_smul (d.coord y) x, h, smul_zero]
    · rintro (hx | hx)
      · rw [hx, smul_zero]
      · exact absurd hx hy

theorem mul_ne_zero {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) : d.mul x y ≠ 0 := by
  rw [Ne, mul_eq_zero_iff]; exact fun h => h.elim hx hy

/-- The key group-theoretic identity: `coord (z • y) = coord z * coord y` for `y ≠ 0`
(so `coord` is an anti-homomorphism; this drives associativity of `mul`). -/
theorem coord_smul {y : A} (hy : y ≠ 0) (m : M) :
    d.coord (m • y) = m * d.coord y := by
  refine (d.coord_unique (by
    intro h; exact hy (by rw [← inv_smul_smul m y, h, smul_zero])) ?_).symm
  rw [mul_smul, coord_smul_e d hy]

/-- **Associativity** `(x * y) * z = x * (y * z)`. -/
theorem mul_assoc' (x y z : A) : d.mul (d.mul x y) z = d.mul x (d.mul y z) := by
  by_cases hz : z = 0
  · simp [hz]
  by_cases hy : y = 0
  · simp [hy]
  · rw [d.mul_def hz, d.mul_def hy, d.mul_def (d.mul_ne_zero hy hz), d.mul_def hz,
      d.coord_smul hy, mul_smul]

/-- `e` is a left identity: `e * x = x`. -/
@[simp] theorem one_mul' (x : A) : d.mul d.e x = x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact d.e_mul x hx

/-- **Right multiplication is the action**: `x * (m • e) = m • x`.  This is the bridge between the
near-field multiplication and the group action — the identity that turns the conjugation action of
the acting group into right multiplication by `F^*` (Peterfalvi's `𝓛(F) = F ⋊ F^*`). -/
theorem mul_smul_e (m : M) (x : A) : d.mul x (m • d.e) = m • x := by
  rw [d.mul_def (d.smul_e_ne_zero m), ← d.coord_unique (d.smul_e_ne_zero m) rfl]

/-- The product of two "coordinate" elements is *anti*-multiplicative in `M`:
`(m₁ • e) * (m₂ • e) = (m₂ * m₁) • e`.  Hence `m ↦ m • e` is an anti-homomorphism `M → Aˣ`, and a
genuine isomorphism `M ≃* Aˣ` must pre-compose with inversion (see `mulEquivUnits`). -/
theorem smul_e_mul (m₁ m₂ : M) : d.mul (m₁ • d.e) (m₂ • d.e) = (m₂ * m₁) • d.e := by
  rw [d.mul_smul_e, mul_smul]

/-- **Right distributivity** `(a + b) * c = a * c + b * c` — exactly additivity of `· • x`. -/
theorem right_distrib' (a b c : A) : d.mul (a + b) c = d.mul a c + d.mul b c := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [d.mul_def hc, d.mul_def hc, d.mul_def hc, smul_add]

/-- The multiplicative inverse `y⁻¹ := (coord y)⁻¹ • e` (and `0⁻¹ = 0`). -/
noncomputable def inv (y : A) : A := by
  classical exact if _hy : y = 0 then 0 else (d.coord y)⁻¹ • d.e

theorem inv_def {y : A} (hy : y ≠ 0) : d.inv y = (d.coord y)⁻¹ • d.e := dif_neg hy

@[simp] theorem inv_zero' : d.inv 0 = 0 := dif_pos rfl

theorem inv_ne_zero {y : A} (hy : y ≠ 0) : d.inv y ≠ 0 := by
  rw [d.inv_def hy]; exact d.smul_e_ne_zero _

theorem coord_inv {y : A} (hy : y ≠ 0) : d.coord (d.inv y) = (d.coord y)⁻¹ := by
  rw [d.inv_def hy, d.coord_smul d.e_ne_zero, coord_e, mul_one]

/-- Every nonzero element is invertible: `y * y⁻¹ = e`. -/
theorem mul_inv_cancel' {y : A} (hy : y ≠ 0) : d.mul y (d.inv y) = d.e := by
  rw [d.mul_def (d.inv_ne_zero hy), d.coord_inv hy, inv_smul_eq_iff]
  exact (d.coord_smul_e hy).symm

/-- **The near-field structure transported from the sharply transitive action** (Peterfalvi
App. C, p. 137).  The additive group is `A`; multiplication is `x * y = (coord y) • x`; the
multiplicative identity is `e`. -/
@[reducible] noncomputable def nearField : NearField A where
  __ := (inferInstance : AddCommGroup A)
  mul := d.mul
  one := d.e
  inv := d.inv
  mul_assoc := d.mul_assoc'
  one_mul := d.one_mul'
  mul_one := d.mul_e
  zero_mul := d.zero_mul
  mul_zero := d.mul_zero
  inv_zero := d.inv_zero'
  mul_inv_cancel := fun _ ha => d.mul_inv_cancel' ha
  exists_pair_ne := ⟨0, d.e, fun h => d.e_ne_zero h.symm⟩
  right_distrib := d.right_distrib'

/-- **The multiplicative group of the near-field is the acting group** `M`: the map
`m ↦ m⁻¹ • e` is a group isomorphism `M ≃* Aˣ` (onto the units `A ∖ {0}` of the near-field).

The inverse `m ↦ m⁻¹` (rather than `m ↦ m • e`) is what makes this a *homomorphism*: right
multiplication is `x * y = (coord y) • x`, so `(m₁⁻¹ • e) * (m₂⁻¹ • e) = (m₁ m₂)⁻¹ • e` — i.e.
`m ↦ m • e` is an *anti*-homomorphism, and pre-composing with inversion fixes the direction.  This
realizes the identification `Q ≃* F^*` of Peterfalvi Appendix C, Proposition 1. -/
noncomputable def mulEquivUnits :
    letI := d.nearField
    M ≃* Aˣ :=
  letI := d.nearField
  { toFun := fun m => Units.mk0 (m⁻¹ • d.e) (d.smul_e_ne_zero _)
    invFun := fun u => (d.coord (u : A))⁻¹
    left_inv := fun m => by
      simp only [Units.val_mk0]
      rw [← d.coord_unique (d.smul_e_ne_zero m⁻¹) rfl, inv_inv]
    right_inv := fun u => by
      have hu : (u : A) ≠ 0 := u.ne_zero
      apply Units.ext
      simp only [Units.val_mk0, inv_inv]
      exact d.coord_smul_e hu
    map_mul' := fun m₁ m₂ => by
      apply Units.ext
      simp only [Units.val_mk0, Units.val_mul]
      change (m₁ * m₂)⁻¹ • d.e = d.mul (m₁⁻¹ • d.e) (m₂⁻¹ • d.e)
      rw [d.mul_smul_e, smul_smul, mul_inv_rev] }

/-- The underlying element of `mulEquivUnits m` is `m⁻¹ • e`. -/
@[simp] theorem mulEquivUnits_val (m : M) :
    letI := d.nearField
    ((d.mulEquivUnits m : Aˣ) : A) = m⁻¹ • d.e := rfl

/-- Right multiplication by `mulEquivUnits q⁻¹` **is** the action of `q` (the near-field form of the
conjugation-to-right-multiplication identity, `qEquiv_conj` after issue 9406 fix (A)):
`x * (mulEquivUnits q⁻¹) = q • x`. -/
theorem mul_mulEquivUnits_inv (q : M) (x : A) :
    letI := d.nearField
    d.mul x ((d.mulEquivUnits q⁻¹ : Aˣ) : A) = q • x := by
  rw [d.mulEquivUnits_val, inv_inv, d.mul_smul_e]

end SharplyTransitiveData

end OddOrder.GroupTheory

/-! ### The affine group of a near-field (forward direction of the correspondence)

Peterfalvi, Appendix C, p. 137 records the correspondence in *both* directions.  The structure
`SharplyTransitiveData` above does the backward half (a sharply transitive action produces a
near-field).  Here is the
forward half: *from* a near-field `F` one builds the **affine group** `𝓛(F) = F ⋊ F^*`, realized as
the group of affine permutations `x ↦ x * u + t` (`u ∈ F^*`, `t ∈ F`) of `F`, and shows that it
**acts sharply `2`-transitively** on `F` — any ordered pair of distinct points maps to any ordered
pair of distinct points under a *unique* affine map.  This is the Zassenhaus near-field ↔
sharply-`2`-transitive-group correspondence going the other way. -/

namespace OddOrder.Peterfalvi.Appendices.NearFields

variable {F : Type*} [NearField F]

/-- Right multiplication distributes over negation in a near-field: `(-a) * c = -(a * c)`
(from the right distributive law, since `(-a) * c + a * c = (-a + a) * c = 0`).  Named to avoid the
clash with the ring lemma `_root_.neg_mul`, which does not apply to a near-field. -/
theorem nearField_neg_mul (a c : F) : (-a) * c = -(a * c) := by
  rw [eq_neg_iff_add_eq_zero, ← NearField.add_mul, neg_add_cancel, zero_mul]

/-- Right multiplication distributes over subtraction in a near-field: `(a - b) * c = a*c - b*c`. -/
theorem nearField_sub_mul (a b c : F) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg, NearField.add_mul, nearField_neg_mul, ← sub_eq_add_neg]

end OddOrder.Peterfalvi.Appendices.NearFields

namespace OddOrder.GroupTheory

open OddOrder.Peterfalvi.Appendices.NearFields

variable {F : Type*} [NearField F]

/-- The **affine permutation** `x ↦ x * u + t` of a near-field `F` (`u ∈ F^*`, `t ∈ F`).  It is a
bijection because `u` is invertible; the inverse is `y ↦ (y - t) * u⁻¹`.  These permutations are the
elements of the affine group `𝓛(F) = F ⋊ F^*`. -/
def nearFieldAffinePerm (u : Fˣ) (t : F) : Equiv.Perm F where
  toFun x := x * (u : F) + t
  invFun y := (y - t) * ((u⁻¹ : Fˣ) : F)
  left_inv x := by
    change ((x * (u : F) + t) - t) * ((u⁻¹ : Fˣ) : F) = x
    rw [add_sub_cancel_right, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  right_inv y := by
    change ((y - t) * ((u⁻¹ : Fˣ) : F)) * (u : F) + t = y
    rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one, sub_add_cancel]

@[simp] theorem nearFieldAffinePerm_apply (u : Fˣ) (t x : F) :
    nearFieldAffinePerm u t x = x * (u : F) + t := rfl

/-- **Sharp `2`-transitivity of the affine maps of a near-field** (arithmetic core): for distinct
`a ≠ b` and distinct `c ≠ d` there is a *unique* pair `(u, t) ∈ F^* × F` whose affine map
`x ↦ x*u + t` sends `a ↦ c` and `b ↦ d`.  Existence solves `(b-a)*u = d-c` (possible since
`b-a ≠ 0` and the nonzero elements form a group) then sets `t = c - a*u`; uniqueness cancels the
nonzero factor `b - a`. -/
theorem nearField_affine_existsUnique {a b c d : F} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃! p : Fˣ × F, a * (p.1 : F) + p.2 = c ∧ b * (p.1 : F) + p.2 = d := by
  have hw : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hv : d - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hcd)
  -- solve `(b - a) * u = d - c` for a unit `u`; `obtain` keeps `u` opaque (so `abel` treats `↑u`
  -- as an atom, which a `set`-let-binding would zeta-expand inconsistently)
  obtain ⟨u, hbau⟩ : ∃ u : Fˣ, (b - a) * (u : F) = d - c := by
    refine ⟨(Units.mk0 (b - a) hw)⁻¹ * Units.mk0 (d - c) hv, ?_⟩
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0,
      ← mul_assoc, mul_inv_cancel₀ hw, one_mul]
  refine ⟨(u, c - a * (u : F)), ⟨?_, ?_⟩, ?_⟩
  · -- a * u + (c - a * u) = c  (`change` forces the `Prod.fst` projection to reduce so `abel`'s
    -- atoms match)
    change a * (u : F) + (c - a * (u : F)) = c
    abel
  · -- b * u + (c - a * u) = d
    change b * (u : F) + (c - a * (u : F)) = d
    have hstep : b * (u : F) - a * (u : F) = d - c := by rw [← nearField_sub_mul]; exact hbau
    have hrw : b * (u : F) + (c - a * (u : F)) = (b * (u : F) - a * (u : F)) + c := by abel
    rw [hrw, hstep]; abel
  · -- uniqueness
    rintro ⟨u', t'⟩ ⟨h1, h2⟩
    simp only at h1 h2
    -- from h1, h2 : (b - a) * u' = d - c
    have hq : (b - a) * (u' : F) = d - c := by
      rw [nearField_sub_mul]
      have e1 : b * (u' : F) = d - t' := by rw [← h2]; abel
      have e2 : a * (u' : F) = c - t' := by rw [← h1]; abel
      rw [e1, e2]; abel
    have huval : (u' : F) = (u : F) := mul_left_cancel₀ hw (by rw [hq, hbau])
    have hut : u' = u := Units.val_injective huval
    have ht' : t' = c - a * (u : F) := by rw [← huval, ← h1]; abel
    exact Prod.ext hut ht'

/-- The identity is the affine permutation `x ↦ x * 1 + 0`. -/
theorem nearFieldAffinePerm_one_zero : nearFieldAffinePerm (1 : Fˣ) (0 : F) = 1 := by
  ext x; simp [nearFieldAffinePerm_apply]

/-- Composition of affine permutations: `(x ↦ x*u₂ + t₂) ∘ (x ↦ x*u₁ + t₁) = (x ↦ x*(u₁u₂) +
(t₁*u₂ + t₂))`.  (`Equiv.Perm` multiplication is `(f * g) x = f (g x)`.) -/
theorem nearFieldAffinePerm_mul (u₁ u₂ : Fˣ) (t₁ t₂ : F) :
    nearFieldAffinePerm u₂ t₂ * nearFieldAffinePerm u₁ t₁
      = nearFieldAffinePerm (u₁ * u₂) (t₁ * (u₂ : F) + t₂) := by
  ext x
  simp only [Equiv.Perm.mul_apply, nearFieldAffinePerm_apply, Units.val_mul]
  rw [NearField.add_mul, mul_assoc x (u₁ : F) (u₂ : F)]
  abel

/-- The inverse of an affine permutation is affine: `(x ↦ x*u + t)⁻¹ = (x ↦ x*u⁻¹ - t*u⁻¹)`. -/
theorem nearFieldAffinePerm_inv (u : Fˣ) (t : F) :
    (nearFieldAffinePerm u t)⁻¹ = nearFieldAffinePerm u⁻¹ (-(t * ((u⁻¹ : Fˣ) : F))) := by
  refine inv_eq_of_mul_eq_one_left ?_
  rw [nearFieldAffinePerm_mul, mul_inv_cancel, add_neg_cancel, nearFieldAffinePerm_one_zero]

/-- The **affine group** `𝓛(F) = F ⋊ F^*` of a near-field `F`, realized as the subgroup of
`Equiv.Perm F` consisting of the affine permutations `x ↦ x * u + t` (`u ∈ F^*`, `t ∈ F`).  Closure
under multiplication and inverses is the affine composition/inversion law
(`nearFieldAffinePerm_mul`, `nearFieldAffinePerm_inv`). -/
def nearFieldAffineGroup (F : Type*) [NearField F] : Subgroup (Equiv.Perm F) where
  carrier := {g | ∃ u t, nearFieldAffinePerm u t = g}
  one_mem' := ⟨1, 0, nearFieldAffinePerm_one_zero⟩
  mul_mem' := by
    rintro _ _ ⟨ua, ta, rfl⟩ ⟨ub, tb, rfl⟩
    exact ⟨ub * ua, tb * (ua : F) + ta, (nearFieldAffinePerm_mul ub ua tb ta).symm⟩
  inv_mem' := by
    rintro _ ⟨u, t, rfl⟩
    exact ⟨u⁻¹, -(t * ((u⁻¹ : Fˣ) : F)), (nearFieldAffinePerm_inv u t).symm⟩

@[simp] theorem mem_nearFieldAffineGroup {g : Equiv.Perm F} :
    g ∈ nearFieldAffineGroup F ↔ ∃ u t, nearFieldAffinePerm u t = g := Iff.rfl

/-- **The affine group of a near-field acts sharply `2`-transitively** (Peterfalvi, Appendix C,
p. 137, forward direction of the Zassenhaus correspondence): for distinct `a ≠ b` and distinct
`c ≠ d` there is a *unique* element of `𝓛(F) = F ⋊ F^*` sending `a ↦ c` and `b ↦ d`.  This packages
the arithmetic core `nearField_affine_existsUnique` at the level of the permutation group. -/
theorem nearFieldAffineGroup_existsUnique {a b c d : F} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃! g : nearFieldAffineGroup F, (g : Equiv.Perm F) a = c ∧ (g : Equiv.Perm F) b = d := by
  obtain ⟨⟨u, t⟩, ⟨hc, hd⟩, huniq⟩ := nearField_affine_existsUnique hab hcd
  refine ⟨⟨nearFieldAffinePerm u t, u, t, rfl⟩, ⟨?_, ?_⟩, ?_⟩
  · simpa using hc
  · simpa using hd
  · rintro ⟨g, ug, tg, rfl⟩ ⟨hgc, hgd⟩
    apply Subtype.ext
    simp only [nearFieldAffinePerm_apply] at hgc hgd
    have heq : (ug, tg) = (u, t) := huniq (ug, tg) ⟨hgc, hgd⟩
    rw [Prod.mk.injEq] at heq
    rw [heq.1, heq.2]

end OddOrder.GroupTheory
