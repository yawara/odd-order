/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basis
import Mathlib.Tactic.Abel
import OddOrder.GroupTheory.PRank
import OddOrder.Isaacs.Ch04_Commutators.Main.BaerTrick

/-!
# Peterfalvi Appendix III: central extensions from quadratic maps

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Lemma 1(b), pp. 139--140.

Given a bilinear map `B : V × V → W`, this file puts the twisted group law

`(v, w) * (v', w') = (v + v', B v v' + w + w')`

on `V × W`.  A quadratic map `q : V → W` over `F₂`, together with an ordered
basis of `V`, supplies such a bilinear lift through `q.toBilin`.  The resulting
short exact sequence has central kernel `W`, quotient `V`, and its squaring map
is exactly `q`.

The converse **Lemma 1(a)** (`centralSquareQuadraticMap` below): for a central
subgroup `W ≤ Z(P)` with `W` and `P ⧸ W` elementary abelian `2`-groups, squaring
descends to a quadratic map `P ⧸ W → W` whose polar form is the commutator
pairing.  (The book states this for `P` a `2`-group; only `W ≤ Z(P)` and the
exponent-`2` conditions are used, so we formalize the general statement.)
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

noncomputable section

open LinearMap (BilinMap)
open Module

universe uR uV uW uI

section BilinearTwistedProduct

variable {R : Type uR} {V : Type uV} {W : Type uW}
  [CommRing R] [AddCommGroup V] [AddCommGroup W]
  [Module R V] [Module R W]

/-- The twisted product associated with a bilinear map `B : V × V → W`.

The first coordinate is the quotient coordinate and the second coordinate is
the central-kernel coordinate. -/
@[ext]
structure BilinearTwistedProduct (B : BilinMap R V W) where
  quotient : V
  central : W

namespace BilinearTwistedProduct

variable {B : BilinMap R V W}

instance : Mul (BilinearTwistedProduct B) where
  mul x y :=
    ⟨x.quotient + y.quotient,
      B x.quotient y.quotient + x.central + y.central⟩

instance : One (BilinearTwistedProduct B) where
  one := ⟨0, 0⟩

instance : Inv (BilinearTwistedProduct B) where
  inv x := ⟨-x.quotient, B x.quotient x.quotient - x.central⟩

/-- Multiplication in twisted-product coordinates. -/
theorem mul_def (x y : BilinearTwistedProduct B) :
    x * y =
      ⟨x.quotient + y.quotient,
        B x.quotient y.quotient + x.central + y.central⟩ :=
  rfl

/-- The identity in twisted-product coordinates. -/
theorem one_def : (1 : BilinearTwistedProduct B) = ⟨0, 0⟩ :=
  rfl

/-- Inversion in twisted-product coordinates. -/
theorem inv_def (x : BilinearTwistedProduct B) :
    x⁻¹ = ⟨-x.quotient, B x.quotient x.quotient - x.central⟩ :=
  rfl

@[simp]
theorem quotient_mul (x y : BilinearTwistedProduct B) :
    (x * y).quotient = x.quotient + y.quotient :=
  rfl

@[simp]
theorem central_mul (x y : BilinearTwistedProduct B) :
    (x * y).central = B x.quotient y.quotient + x.central + y.central :=
  rfl

@[simp]
theorem quotient_one : (1 : BilinearTwistedProduct B).quotient = 0 :=
  rfl

@[simp]
theorem central_one : (1 : BilinearTwistedProduct B).central = 0 :=
  rfl

@[simp]
theorem quotient_inv (x : BilinearTwistedProduct B) :
    x⁻¹.quotient = -x.quotient :=
  rfl

@[simp]
theorem central_inv (x : BilinearTwistedProduct B) :
    x⁻¹.central = B x.quotient x.quotient - x.central :=
  rfl

/-- Bilinearity is precisely the cocycle identity needed for associativity. -/
instance : Group (BilinearTwistedProduct B) where
  mul_assoc x y z := by
    ext
    · exact add_assoc _ _ _
    · simp only [central_mul, quotient_mul, map_add, LinearMap.add_apply]
      abel
  one_mul x := by
    ext <;> simp
  mul_one x := by
    ext <;> simp
  inv_mul_cancel x := by
    ext
    · simp
    · simp only [central_mul, central_inv, quotient_inv, map_neg,
        LinearMap.neg_apply, central_one]
      abel

/-- The central-coordinate inclusion. -/
def centralEmbedding (B : BilinMap R V W) :
    Multiplicative W →* BilinearTwistedProduct B where
  toFun w := ⟨0, w.toAdd⟩
  map_one' := by ext <;> rfl
  map_mul' x y := by ext <;> simp

@[simp]
theorem centralEmbedding_quotient (w : Multiplicative W) :
    (centralEmbedding B w).quotient = 0 :=
  rfl

@[simp]
theorem centralEmbedding_central (w : Multiplicative W) :
    (centralEmbedding B w).central = w.toAdd :=
  rfl

/-- The central-coordinate inclusion is injective. -/
theorem centralEmbedding_injective :
    Function.Injective (centralEmbedding B) := by
  intro x y h
  exact Multiplicative.toAdd.injective
    (congrArg BilinearTwistedProduct.central h)

/-- The image of the kernel coordinate is central. -/
theorem centralEmbedding_range_le_center :
    (centralEmbedding B).range ≤ Subgroup.center (BilinearTwistedProduct B) := by
  rintro x ⟨w, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  ext
  · simp
  · simp [mul_def, add_comm]

/-- Projection to the quotient coordinate. -/
def projection (B : BilinMap R V W) :
    BilinearTwistedProduct B →* Multiplicative V where
  toFun x := Multiplicative.ofAdd x.quotient
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem projection_apply (x : BilinearTwistedProduct B) :
    (projection B x).toAdd = x.quotient :=
  rfl

/-- Projection onto the quotient coordinate is surjective. -/
theorem projection_surjective : Function.Surjective (projection B) := by
  intro v
  exact ⟨⟨v.toAdd, 0⟩, rfl⟩

/-- The central coordinate is exactly the kernel of the quotient projection. -/
theorem range_centralEmbedding_eq_ker_projection :
    (centralEmbedding B).range = (projection B).ker := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    rfl
  · intro hx
    have hx0 : x.quotient = 0 := by
      have h := congrArg Multiplicative.toAdd hx
      simpa using h
    refine ⟨Multiplicative.ofAdd x.central, ?_⟩
    ext
    · exact hx0.symm
    · rfl

/-- The twisted product is a short exact sequence
`1 → W → V ×_B W → V → 1`. -/
def groupExtension (B : BilinMap R V W) :
    GroupExtension (Multiplicative W) (BilinearTwistedProduct B)
      (Multiplicative V) where
  inl := centralEmbedding B
  rightHom := projection B
  inl_injective := centralEmbedding_injective
  range_inl_eq_ker_rightHom := range_centralEmbedding_eq_ker_projection
  rightHom_surjective := projection_surjective

/-- **A compatible pair of coordinate automorphisms is an automorphism of the
twisted product.**

If `f` acts on the quotient coordinate and `g` on the central one, and they are
compatible with the cocycle — `B (f x) (f y) = g (B x y)` — then `(x, w) ↦ (f x, g w)`
is a group automorphism.

This is how the scalars act on Peterfalvi's model `S₁` in Part II, Ch. III §3,
p. 120: `(x, y)^a = (a x, a^{1+σ} y)`, whose compatibility condition is exactly the
diagonal scaling `φ (a x) (a y) = a^{1+σ} φ (x, y)` of the cocycle. -/
def congrEquiv (f : V ≃+ V) (g : W ≃+ W)
    (h : ∀ x y : V, B (f x) (f y) = g (B x y)) :
    BilinearTwistedProduct B ≃* BilinearTwistedProduct B where
  toFun p := ⟨f p.quotient, g p.central⟩
  invFun p := ⟨f.symm p.quotient, g.symm p.central⟩
  left_inv p := by
    ext
    · exact f.symm_apply_apply _
    · exact g.symm_apply_apply _
  right_inv p := by
    ext
    · exact f.apply_symm_apply _
    · exact g.apply_symm_apply _
  map_mul' p q := by
    ext
    · exact map_add f _ _
    · change g (B p.quotient q.quotient + p.central + q.central)
        = B (f p.quotient) (f q.quotient) + g p.central + g q.central
      rw [map_add, map_add, h]

@[simp] theorem congrEquiv_quotient (f : V ≃+ V) (g : W ≃+ W)
    (h : ∀ x y : V, B (f x) (f y) = g (B x y)) (p : BilinearTwistedProduct B) :
    (congrEquiv f g h p).quotient = f p.quotient :=
  rfl

@[simp] theorem congrEquiv_central (f : V ≃+ V) (g : W ≃+ W)
    (h : ∀ x y : V, B (f x) (f y) = g (B x y)) (p : BilinearTwistedProduct B) :
    (congrEquiv f g h p).central = g p.central :=
  rfl

end BilinearTwistedProduct

end BilinearTwistedProduct

section TwistedSquare

variable {V : Type uV} {W : Type uW}
  [AddCommGroup V] [AddCommGroup W]
  [Module (ZMod 2) V] [Module (ZMod 2) W]

/-- Addition is self-cancelling in a module over `F₂`. -/
theorem zmodTwo_add_self (w : W) : w + w = 0 := by
  calc
    w + w = 2 • w := (two_nsmul w).symm
    _ = (2 : ZMod 2) • w :=
      (Nat.cast_smul_eq_nsmul (ZMod 2) 2 w).symm
    _ = 0 := by
      rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_smul]

/-- **Squaring in a twisted product over `F₂` is the diagonal of the cocycle.**

The general form of `QuadraticExtension.sq_eq_inl_q`: the square map of
`BilinearTwistedProduct B` depends on `B` only through `v ↦ B v v`, which is why
Appendix III Lemma 1(c) makes any two bilinear lifts of the same quadratic map
give isomorphic extensions.  Peterfalvi uses this in Part II, Ch. III §3, p. 121,
where the model `S₁` is built from an explicit cocycle `φ` rather than from a
basis lift. -/
theorem BilinearTwistedProduct.sq_eq_inl_diag (B : LinearMap.BilinMap (ZMod 2) V W)
    (x : BilinearTwistedProduct B) :
    x ^ 2 = (BilinearTwistedProduct.groupExtension B).inl
      (Multiplicative.ofAdd (B x.quotient x.quotient)) := by
  rw [pow_two]
  ext
  · change x.quotient + x.quotient = 0
    exact zmodTwo_add_self x.quotient
  · change B x.quotient x.quotient + x.central + x.central =
      B x.quotient x.quotient
    rw [add_assoc, zmodTwo_add_self, add_zero]

end TwistedSquare

section QuadraticExtension

variable {V : Type uV} {W : Type uW} {ι : Type uI}
  [AddCommGroup V] [AddCommGroup W]
  [Module (ZMod 2) V] [Module (ZMod 2) W]
  [LinearOrder ι]

/-- Peterfalvi's central extension attached to `q`, using the upper-triangular
bilinear lift selected by the ordered basis `basis`. -/
abbrev QuadraticExtension (q : QuadraticMap (ZMod 2) V W)
    (basis : Basis ι (ZMod 2) V) :=
  BilinearTwistedProduct (q.toBilin basis)

namespace QuadraticExtension

variable (q : QuadraticMap (ZMod 2) V W)
  (basis : Basis ι (ZMod 2) V)

/-- The chosen bilinear lift has diagonal equal to the original quadratic map. -/
theorem toBilin_self (v : V) : q.toBilin basis v v = q v := by
  have h := QuadraticMap.congr_fun
    (QuadraticMap.toQuadraticMap_toBilin q basis) v
  simpa only [LinearMap.BilinMap.toQuadraticMap_apply] using h

/-- **Peterfalvi Appendix III, Lemma 1(b).**  The explicit twisted product is
a central extension of the additive groups of `W` and `V`. -/
def extension :
    GroupExtension (Multiplicative W) (QuadraticExtension q basis)
      (Multiplicative V) :=
  BilinearTwistedProduct.groupExtension (q.toBilin basis)

/-- The kernel in the quadratic extension is central. -/
theorem range_inl_le_center :
    (extension q basis).inl.range ≤ Subgroup.center (QuadraticExtension q basis) :=
  BilinearTwistedProduct.centralEmbedding_range_le_center

/-- The twisted product is the product of its two coordinates as a set. -/
theorem _root_.OddOrder.Peterfalvi.Appendices.Suzuki2Groups.BilinearTwistedProduct.natCard
    {V' W' : Type*} [AddCommGroup V'] [AddCommGroup W'] [Module (ZMod 2) V']
    [Module (ZMod 2) W'] [Finite V'] [Finite W']
    (B : LinearMap.BilinMap (ZMod 2) V' W') :
    Nat.card (BilinearTwistedProduct B) = Nat.card V' * Nat.card W' := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun x => (x.quotient, x.central)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun x => rfl
      right_inv := fun p => rfl }

/-- **Peterfalvi Appendix III, Lemma 1(b).**  Squaring in the constructed
central extension recovers `q` under the kernel embedding. -/
theorem sq_eq_inl_q (x : QuadraticExtension q basis) :
    x ^ 2 = (extension q basis).inl (Multiplicative.ofAdd (q x.quotient)) := by
  rw [BilinearTwistedProduct.sq_eq_inl_diag (q.toBilin basis) x, toBilin_self]
  rfl

/-- **The involutions of an anisotropic quadratic extension are exactly its
kernel.**  `x² = 1` says `q(x.quotient) = 0`, which for an anisotropic `q` says
`x.quotient = 0`. -/
theorem sq_eq_one_iff (hq : q.Anisotropic) (x : QuadraticExtension q basis) :
    x ^ 2 = 1 ↔ x.quotient = 0 := by
  rw [sq_eq_inl_q]
  constructor
  · intro h
    refine hq _ ?_
    have h1 : Multiplicative.ofAdd (q x.quotient) = 1 :=
      (extension q basis).inl_injective (by rw [h, map_one])
    simpa using h1
  · intro h
    rw [h, map_zero]
    simp

/-- **The order of an anisotropic quadratic extension is `|V| · |W|`, and its
involutions together with `1` number `|W|`.**

For the Appendix III models this is the source of the two possible orders of a
Suzuki `2`-group: type A has `V = W = F`, so `|P| = |F|²`, while types B, C
and D have `V = F × F` and `W = F`, so `|P| = |F|³`; in both `Ω₁(P)` has order
`|F|`. -/
theorem natCard_sq_eq_one [Finite V] [Finite W] (hq : q.Anisotropic) :
    Nat.card {x : QuadraticExtension q basis // x ^ 2 = 1} = Nat.card W := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => x.1.central
      invFun := fun w => ⟨⟨0, w⟩, (sq_eq_one_iff q basis hq _).mpr rfl⟩
      left_inv := ?_
      right_inv := fun w => rfl }
  rintro ⟨x, hx⟩
  have hx0 : x.quotient = 0 := (sq_eq_one_iff q basis hq x).mp hx
  exact Subtype.ext (by
    cases x
    simp only at hx0 ⊢
    rw [hx0])

/-- **The two Appendix III orders, in transported form.**  A group isomorphic to
the quadratic extension of an anisotropic `q` has order `|V| · |W|` and exactly
`|W|` elements of order dividing `2`.

Type A has `V = W = F`, so `|P| = |F|²`; types B, C and D have `V = F × F` and
`W = F`, so `|P| = |F|³`.  In every case `Ω₁(P)` has order `|F|`, which is what
identifies `|F|` with `|Q₀|` in Peterfalvi Part II. -/
theorem natCard_and_natCard_sq_eq_one_of_mulEquiv
    {P : Type*} [Group P] [Finite V] [Finite W]
    (hq : q.Anisotropic) (e : P ≃* QuadraticExtension q basis) :
    Nat.card P = Nat.card V * Nat.card W ∧
      Nat.card {x : P // x ^ 2 = 1} = Nat.card W := by
  constructor
  · rw [Nat.card_congr e.toEquiv]
    exact BilinearTwistedProduct.natCard _
  · rw [← natCard_sq_eq_one q basis hq]
    have hx : ∀ x : P, e.toEquiv x = e x := fun _ => rfl
    refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)
    rw [hx]
    constructor
    · intro h
      rw [← map_pow, h, map_one]
    · intro h
      apply e.injective
      rw [map_pow, h, map_one]

end QuadraticExtension

end QuadraticExtension

section CentralSquareQuadratic

/-! ### Lemma 1(a): squaring in a central elementary extension is quadratic

`W ≤ Z(P)` with `W` and `P ⧸ W` elementary abelian `2`-groups.  Squaring
descends to `centralSquare : P ⧸ W → ↥W`; its polarization
`centralCommPairing` (defined as the multiplicative polar defect of
`centralSquare`, hence well defined for free) computes to the descended
commutator pairing `⁅y, x⁆` and is biadditive by the class-`≤ 2` commutator
identities. -/

open OddOrder.GroupTheory
open scoped commutatorElement IsMulCommutative

variable {P : Type uV} [Group P] {W : Subgroup P} [W.Normal]

section Descend

/-- The square of any element lies in `W` (exponent `2` of the quotient). -/
theorem sq_mem_of_quotient_elementaryAbelian
    (hV : IsElementaryAbelian 2 (P ⧸ W)) (x : P) : x ^ 2 ∈ W := by
  have h : ((x : P ⧸ W)) ^ 2 = 1 := hV.pow_eq_one _
  rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h

/-- Every commutator lies in `W` (commutativity of the quotient). -/
theorem commutatorElement_mem_of_quotient_elementaryAbelian
    (hV : IsElementaryAbelian 2 (P ⧸ W)) (x y : P) : ⁅x, y⁆ ∈ W := by
  rw [← QuotientGroup.eq_one_iff]
  have h : ((⁅x, y⁆ : P) : P ⧸ W) = ⁅(x : P ⧸ W), (y : P ⧸ W)⁆ := rfl
  rw [h, commutatorElement_def, hV.comm (x : P ⧸ W) (y : P ⧸ W)]
  group

/-- The commutator subgroup lies in `W`. -/
theorem commutator_le_of_quotient_elementaryAbelian
    (hV : IsElementaryAbelian 2 (P ⧸ W)) : _root_.commutator P ≤ W := by
  rw [_root_.commutator, Subgroup.commutator_le]
  exact fun g₁ _ g₂ _ => commutatorElement_mem_of_quotient_elementaryAbelian hV g₁ g₂

/-- **Peterfalvi Appendix III, Lemma 1(a) (raw map).**  Squaring descends to
`P ⧸ W → ↥W`: representatives differ by a central element of square one. -/
noncomputable def centralSquare (hWc : W ≤ Subgroup.center P)
    (hW : IsElementaryAbelian 2 ↥W) (hV : IsElementaryAbelian 2 (P ⧸ W)) :
    P ⧸ W → ↥W :=
  Quotient.lift
    (fun x => (⟨x ^ 2, sq_mem_of_quotient_elementaryAbelian hV x⟩ : ↥W))
    (by
      intro x y hxy
      have hw : x⁻¹ * y ∈ W := QuotientGroup.leftRel_apply.mp hxy
      have hcen := Subgroup.mem_center_iff.mp (hWc hw)
      have hsq1 : (x⁻¹ * y) ^ 2 = 1 :=
        congrArg Subtype.val (hW.pow_eq_one (⟨x⁻¹ * y, hw⟩ : ↥W))
      apply Subtype.ext
      change x ^ 2 = y ^ 2
      have hc : Commute x (x⁻¹ * y) := hcen x
      have hy : (x * (x⁻¹ * y)) ^ 2 = x ^ 2 * (x⁻¹ * y) ^ 2 := hc.mul_pow 2
      rw [show x * (x⁻¹ * y) = y by group, hsq1, mul_one] at hy
      exact hy.symm)

@[simp] theorem centralSquare_mk (hWc : W ≤ Subgroup.center P)
    (hW : IsElementaryAbelian 2 ↥W) (hV : IsElementaryAbelian 2 (P ⧸ W)) (x : P) :
    centralSquare hWc hW hV (x : P ⧸ W) =
      ⟨x ^ 2, sq_mem_of_quotient_elementaryAbelian hV x⟩ :=
  rfl

/-- The polar defect of the square map.  Defined directly from `centralSquare`,
so it is well defined with no further quotient argument; `centralCommPairing_mk`
identifies it with the commutator pairing. -/
noncomputable def centralCommPairing (hWc : W ≤ Subgroup.center P)
    (hW : IsElementaryAbelian 2 ↥W) (hV : IsElementaryAbelian 2 (P ⧸ W))
    (a b : P ⧸ W) : ↥W :=
  (centralSquare hWc hW hV a * centralSquare hWc hW hV b)⁻¹ *
    centralSquare hWc hW hV (a * b)

/-- **The polarization identity** `q(ab) = q(a) q(b) · B(a,b)`. -/
theorem centralSquare_mul (hWc : W ≤ Subgroup.center P)
    (hW : IsElementaryAbelian 2 ↥W) (hV : IsElementaryAbelian 2 (P ⧸ W))
    (a b : P ⧸ W) :
    centralSquare hWc hW hV (a * b) =
      centralSquare hWc hW hV a * centralSquare hWc hW hV b *
        centralCommPairing hWc hW hV a b := by
  rw [centralCommPairing, ← mul_assoc, mul_inv_cancel, one_mul]

/-- **The polar form is the commutator pairing**: `B(x̄, ȳ) = ⁅y, x⁆`
(from `(xy)² = x² y² ⁅y, x⁆` after central rearrangement). -/
theorem centralCommPairing_mk (hWc : W ≤ Subgroup.center P)
    (hW : IsElementaryAbelian 2 ↥W) (hV : IsElementaryAbelian 2 (P ⧸ W))
    (x y : P) :
    centralCommPairing hWc hW hV (x : P ⧸ W) (y : P ⧸ W) =
      ⟨⁅y, x⁆, commutatorElement_mem_of_quotient_elementaryAbelian hV y x⟩ := by
  have hcomm : ⁅y, x⁆ ∈ W := commutatorElement_mem_of_quotient_elementaryAbelian hV y x
  have hcen := Subgroup.mem_center_iff.mp (hWc hcomm)
  have hmk : ((x : P ⧸ W)) * (y : P ⧸ W) = ((x * y : P) : P ⧸ W) := rfl
  rw [centralCommPairing, hmk, centralSquare_mk, centralSquare_mk, centralSquare_mk]
  apply Subtype.ext
  change ((x ^ 2 * y ^ 2 : P))⁻¹ * (x * y) ^ 2 = ⁅y, x⁆
  have hyx : y * x = ⁅y, x⁆ * x * y := by
    rw [commutatorElement_def]; group
  have hsq : (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅y, x⁆ := by
    calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
      _ = x * (⁅y, x⁆ * x * y) * y := by rw [hyx]
      _ = x * ⁅y, x⁆ * (x * (y * y)) := by group
      _ = ⁅y, x⁆ * (x * (x * (y * y))) := by rw [hcen x]; group
      _ = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by rw [pow_two, pow_two]; group
      _ = x ^ 2 * y ^ 2 * ⁅y, x⁆ := by rw [← hcen (x ^ 2 * y ^ 2)]
  rw [hsq]
  group

/-- The pairing is biadditive in the left slot (class-`≤ 2` commutator
identity `⁅z, ab⁆ = ⁅z, a⁆ ⁅z, b⁆` through the descended form). -/
theorem centralCommPairing_mul_left (hWc : W ≤ Subgroup.center P)
    (hW : IsElementaryAbelian 2 ↥W) (hV : IsElementaryAbelian 2 (P ⧸ W))
    (a b c : P ⧸ W) :
    centralCommPairing hWc hW hV (a * b) c =
      centralCommPairing hWc hW hV a c * centralCommPairing hWc hW hV b c := by
  have hC : _root_.commutator P ≤ Subgroup.center P :=
    (commutator_le_of_quotient_elementaryAbelian hV).trans hWc
  induction a using Quotient.inductionOn with
  | h x =>
  induction b using Quotient.inductionOn with
  | h y =>
  induction c using Quotient.inductionOn with
  | h z =>
  have hmk : ((x : P ⧸ W)) * (y : P ⧸ W) = ((x * y : P) : P ⧸ W) := rfl
  rw [hmk, centralCommPairing_mk, centralCommPairing_mk, centralCommPairing_mk]
  apply Subtype.ext
  change ⁅z, x * y⁆ = ⁅z, x⁆ * ⁅z, y⁆
  exact OddOrder.Isaacs.Ch04.commutatorElement_mul_right_of_class_le_two hC z x y

/-- The pairing is biadditive in the right slot. -/
theorem centralCommPairing_mul_right (hWc : W ≤ Subgroup.center P)
    (hW : IsElementaryAbelian 2 ↥W) (hV : IsElementaryAbelian 2 (P ⧸ W))
    (a b c : P ⧸ W) :
    centralCommPairing hWc hW hV a (b * c) =
      centralCommPairing hWc hW hV a b * centralCommPairing hWc hW hV a c := by
  have hC : _root_.commutator P ≤ Subgroup.center P :=
    (commutator_le_of_quotient_elementaryAbelian hV).trans hWc
  induction a using Quotient.inductionOn with
  | h x =>
  induction b using Quotient.inductionOn with
  | h y =>
  induction c using Quotient.inductionOn with
  | h z =>
  have hmk : ((y : P ⧸ W)) * (z : P ⧸ W) = ((y * z : P) : P ⧸ W) := rfl
  rw [hmk, centralCommPairing_mk, centralCommPairing_mk, centralCommPairing_mk]
  apply Subtype.ext
  change ⁅y * z, x⁆ = ⁅y, x⁆ * ⁅z, x⁆
  exact OddOrder.Isaacs.Ch04.commutatorElement_mul_left_of_class_le_two hC y z x

end Descend

section Bundled

variable (hWc : W ≤ Subgroup.center P) (hW : IsElementaryAbelian 2 ↥W)
  (hV : IsElementaryAbelian 2 (P ⧸ W))

/-- **Peterfalvi Appendix III, Lemma 1(a)** (p. 139, bundled form): for a
central subgroup `W ≤ Z(P)` with `W` and `P ⧸ W` elementary abelian `2`-groups,
`x ↦ x²` induces a quadratic mapping `P ⧸ W → W` of `𝔽₂`-vector spaces.  The
companion bilinear form is the commutator pairing
(`centralCommPairing_mk`). -/
noncomputable def centralSquareQuadraticMap :
    letI : IsMulCommutative (P ⧸ W) := IsMulCommutative.of_comm hV.comm
    letI : IsMulCommutative ↥W := IsMulCommutative.of_comm hW.comm
    letI : Module (ZMod 2) (Additive (P ⧸ W)) := hV.zmodModule
    letI : Module (ZMod 2) (Additive ↥W) := hW.zmodModule
    QuadraticMap (ZMod 2) (Additive (P ⧸ W)) (Additive ↥W) :=
  letI : IsMulCommutative (P ⧸ W) := IsMulCommutative.of_comm hV.comm
  letI : IsMulCommutative ↥W := IsMulCommutative.of_comm hW.comm
  letI : Module (ZMod 2) (Additive (P ⧸ W)) := hV.zmodModule
  letI : Module (ZMod 2) (Additive ↥W) := hW.zmodModule
  { toFun := fun a => Additive.ofMul (centralSquare hWc hW hV a.toMul)
    toFun_smul := by
      intro r a
      rcases (by decide : ∀ r : ZMod 2, r = 0 ∨ r = 1) r with h | h <;> subst h
      · rw [zero_smul, show ((0 : ZMod 2) * 0) = 0 by decide, zero_smul]
        have h1 : (Additive.toMul (0 : Additive (P ⧸ W))) = ((1 : P) : P ⧸ W) := rfl
        rw [h1, centralSquare_mk]
        refine congrArg Additive.ofMul (Subtype.ext ?_)
        exact one_pow 2
      · rw [one_smul, show ((1 : ZMod 2) * 1) = 1 by decide, one_smul]
    exists_companion' := by
      classical
      refine ⟨?_, ?_⟩
      · -- the commutator pairing, additivized and made `ZMod 2`-linear
        refine
          (AddMonoidHom.mk'
            (fun a =>
              ((AddMonoidHom.mk'
                (fun b =>
                  Additive.ofMul
                    (centralCommPairing hWc hW hV a.toMul b.toMul))
                (by
                  intro b c
                  exact congrArg Additive.ofMul
                    (centralCommPairing_mul_right hWc hW hV
                      a.toMul b.toMul c.toMul))).toZModLinearMap 2))
            (by
              intro a b
              refine LinearMap.ext fun c => ?_
              exact congrArg Additive.ofMul
                (centralCommPairing_mul_left hWc hW hV
                  a.toMul b.toMul c.toMul))).toZModLinearMap 2
      · intro a b
        exact congrArg Additive.ofMul
          (centralSquare_mul hWc hW hV a.toMul b.toMul) }

end Bundled

end CentralSquareQuadratic

end


end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
