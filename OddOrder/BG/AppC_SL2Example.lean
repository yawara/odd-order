/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import OddOrder.BG.AppC_FinalContradiction

/-!
# BG Appendix C, Remark (II): Peterfalvi's `SL(2, 2^q)` example

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix C, Remark (II), p. 146.

Theorem C says that two primes `p, q` satisfying condition (A), together with a group `G`
satisfying hypothesis (B), force `p ≤ q`.  Remark (II), attributed to T. Peterfalvi, records that
these hypotheses are **not vacuous**: for *every* `q`, taking `p = 2` and `G = SL(2, 2^q)` works,
with

* `σ(P)  = {[[1, a], [0, 1]]   | a ∈ 𝔽_{2^q}}`,
* `σ(P₀) = ⟨[[1, 1], [0, 1]]⟩`,
* `σ(U)  = {[[a, 0], [0, a⁻¹]] | a ∈ 𝔽_{2^q}ˣ}`,
* `y = [[0, 1], [1, 1]]` and `Q = ⟨y⟩`.

Remark (IV) records that S. P. Norton and Glauberman later sharpened Theorem C to `p ≤ 3`, and
that Example (II) is what shows `p = 2` does occur (whether `p = 3` occurs was open).

## Main results

* `SL2.upperHom`, `SL2.torusHom` — the two Borel one-parameter subgroups of `SL(2, F)`.
* `sigmaSL2` — the monomorphism `σ : H = P ⋊ U → SL(2, 2^q)` of Remark (II).
* `map_kernel_sigmaSL2`, `map_primeLine_sigmaSL2`, `map_complement_sigmaSL2` — the three images
  `σ(P)`, `σ(P₀)`, `σ(U)` are exactly the three sets displayed in the book.
* `conditionA_two` — condition (A) holds for `p = 2` and every `q`: it reads `gcd(2^q - 1, 1) = 1`.
* `hypothesisBAbstract_sl2` — **Remark (II)**: `SL(2, 2^q)` satisfies hypothesis (B) for `p = 2`.

## Implementation notes

The book writes `σ(U) = {[[a, 0], [0, a⁻¹]]}` as a *set*; the parametrisation by `u ∈ U` has to be
twisted, because conjugation by `[[v, 0], [0, v⁻¹]]` sends `[[1, a], [0, 1]]` to
`[[1, v²a], [0, 1]]` whereas `u ∈ U` acts on `P` by `a ↦ u·a`.  In characteristic `2` squaring is
bijective on `𝔽_{2^q}ˣ`, so `σ(u) := [[√u, 0], [0, √u⁻¹]]` with `√u = u^(2^(q-1))` is a
monomorphism whose image is exactly the set the book describes.  Note also that for `p = 2` the
norm is `N(x) = x^(2^q - 1)`, so `U = 𝔽_{2^q}ˣ` is the *whole* multiplicative group and `H` is the
affine group `AGL(1, 2^q)`, realised as the Borel subgroup of `SL(2, 2^q)`.
-/

namespace OddOrder.BG.AppC

open Matrix
open scoped Pointwise

/-! ## Normalizer helpers -/

/-- A sufficient criterion for lying in the normalizer of a subgroup: conjugation by `x` and by
`x⁻¹` both map the subgroup into itself. -/
theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (h₁ : ∀ n ∈ H, x * n * x⁻¹ ∈ H) (h₂ : ∀ n ∈ H, x⁻¹ * n * x ∈ H) :
    x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => h₁ n hn, fun hn => ?_⟩
  have := h₂ _ hn
  simpa [mul_assoc] using this

/-- For an involution `x`, one inclusion suffices to be in the normalizer. -/
theorem mem_normalizer_of_inv_self {G : Type*} [Group G] {H : Subgroup G} {x : G} (hx : x⁻¹ = x)
    (h : ∀ n ∈ H, x * n * x⁻¹ ∈ H) : x ∈ Subgroup.normalizer (H : Set G) := by
  refine mem_normalizer_of_conj_mem h fun n hn => ?_
  rw [hx]
  have := h n hn
  rwa [hx] at this

/-- An involution normalizing `⟨g⟩` need only be checked on `g` itself. -/
theorem mem_normalizer_zpowers_of_inv_self {G : Type*} [Group G] {x g : G} (hx : x⁻¹ = x)
    (h : x * g * x⁻¹ ∈ Subgroup.zpowers g) :
    x ∈ Subgroup.normalizer ((Subgroup.zpowers g : Subgroup G) : Set G) := by
  refine mem_normalizer_of_inv_self hx ?_
  rintro n ⟨k, rfl⟩
  have hconj : x * g ^ k * x⁻¹ = (x * g * x⁻¹) ^ k := by
    simp
  rw [hconj]
  exact Subgroup.zpow_mem _ h k

/-! ## Borel elements of `SL(2, F)` -/

namespace SL2

variable {F : Type*} [Field F]

/-- The upper unitriangular matrix `[[1, a], [0, 1]]` as an element of `SL(2, F)`. -/
def upper (a : F) : SpecialLinearGroup (Fin 2) F := ⟨!![1, a; 0, 1], by simp⟩

/-- The diagonal matrix `[[u, 0], [0, u⁻¹]]` as an element of `SL(2, F)`. -/
def torus (u : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![(u : F), 0; 0, ((u⁻¹ : Fˣ) : F)], by simp⟩

@[simp] theorem coe_upper (a : F) :
    (upper a : Matrix (Fin 2) (Fin 2) F) = !![1, a; 0, 1] := rfl

@[simp] theorem coe_torus (u : Fˣ) :
    (torus u : Matrix (Fin 2) (Fin 2) F) = !![(u : F), 0; 0, ((u⁻¹ : Fˣ) : F)] := rfl

theorem upper_mul_upper (a b : F) : upper a * upper b = upper (a + b) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, coe_upper, coe_upper, coe_upper, Matrix.mul_fin_two]
  norm_num [add_comm]

theorem upper_zero : upper (0 : F) = 1 := by
  apply Subtype.ext
  rw [coe_upper, SpecialLinearGroup.coe_one, Matrix.one_fin_two]

/-- The additive group of `F`, embedded in `SL(2, F)` as the unipotent upper triangular
matrices.  This is `σ|_P` of BG Appendix C, Remark (II). -/
def upperHom : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun a := upper a.toAdd
  map_one' := upper_zero
  map_mul' _ _ := (upper_mul_upper _ _).symm

@[simp] theorem upperHom_apply (a : Multiplicative F) : upperHom a = upper a.toAdd := rfl

theorem torus_mul_torus (u v : Fˣ) : torus u * torus v = torus (u * v) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, coe_torus, coe_torus, coe_torus, Matrix.mul_fin_two]
  simp [Units.val_inv_eq_inv_val, mul_comm]

theorem torus_one : torus (1 : Fˣ) = 1 := by
  apply Subtype.ext
  rw [coe_torus, SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  simp

/-- The split torus of `SL(2, F)`.  This is `σ|_U` of BG Appendix C, Remark (II), up to the
square-root twist explained in the module docstring. -/
def torusHom : Fˣ →* SpecialLinearGroup (Fin 2) F where
  toFun := torus
  map_one' := torus_one
  map_mul' u v := (torus_mul_torus u v).symm

@[simp] theorem torusHom_apply (u : Fˣ) : torusHom u = torus u := rfl

theorem torus_inv (u : Fˣ) : (torus u)⁻¹ = torus u⁻¹ := (map_inv torusHom u).symm

/-- Conjugating the unipotent `[[1, a], [0, 1]]` by the torus element `[[u, 0], [0, u⁻¹]]`
multiplies `a` by `u²`.  This is why the parametrisation of `σ|_U` has to be twisted by a square
root; see the module docstring. -/
theorem torus_mul_upper_mul_torus_inv (u : Fˣ) (a : F) :
    torus u * upper a * (torus u)⁻¹ = upper ((u : F) * (u : F) * a) := by
  apply Subtype.ext
  rw [torus_inv, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_torus, coe_upper,
    coe_torus, Matrix.mul_fin_two, Matrix.mul_fin_two, coe_upper]
  simp only [Units.val_inv_eq_inv_val, inv_inv, mul_zero, zero_mul, add_zero, zero_add, mul_one]
  rw [mul_inv_cancel₀ u.ne_zero, inv_mul_cancel₀ u.ne_zero,
    show (u : F) * a * (u : F) = (u : F) * (u : F) * a by ring]

/-- The product `[[1, a], [0, 1]] * [[u, 0], [0, u⁻¹]]` is trivial only in the trivial case: this
is the injectivity computation for `σ` of Remark (II). -/
theorem upper_mul_torus_eq_one_iff (a : F) (u : Fˣ) :
    upper a * torus u = 1 ↔ a = 0 ∧ u = 1 := by
  constructor
  · intro h
    have h' : (upper a * torus u : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← SpecialLinearGroup.coe_mul, h, SpecialLinearGroup.coe_one]
    rw [coe_upper, coe_torus, Matrix.mul_fin_two, Matrix.one_fin_two] at h'
    have h00 := congrFun (congrFun h' 0) 0
    have h01 := congrFun (congrFun h' 0) 1
    simp only [one_mul, mul_zero, add_zero, Units.val_inv_eq_inv_val, zero_add, zero_mul,
      Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, Units.val_eq_one,
      cons_val_one, mul_eq_zero, inv_eq_zero, Units.ne_zero, or_false] at h00 h01
    exact ⟨h01, h00⟩
  · rintro ⟨rfl, rfl⟩
    rw [upper_zero, torus_one, one_mul]

section CharTwo

variable [CharP F 2]

/-- The element `y = [[0, 1], [1, 1]]` of BG Appendix C, Remark (II); it has order `3`. -/
def elemY : SpecialLinearGroup (Fin 2) F := ⟨!![0, 1; 1, 1], by simp [CharTwo.neg_eq]⟩

/-- The Weyl element `w = [[0, 1], [1, 0]]` of `SL(2, F)`; it inverts the split torus. -/
def elemW : SpecialLinearGroup (Fin 2) F := ⟨!![0, 1; 1, 0], by simp [CharTwo.neg_eq]⟩

@[simp] theorem coe_elemY :
    ((elemY : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 1] := rfl

@[simp] theorem coe_elemW :
    ((elemW : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl

theorem coe_elemY_sq :
    ((elemY (F := F) ^ 2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 1; 1, 0] := by
  rw [sq, SpecialLinearGroup.coe_mul, coe_elemY, Matrix.mul_fin_two]
  simp [CharTwo.add_self_eq_zero]

/-- `y³ = 1`. -/
theorem elemY_pow_three : (elemY (F := F)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, SpecialLinearGroup.coe_mul, coe_elemY_sq,
    coe_elemY, SpecialLinearGroup.coe_one, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [CharTwo.add_self_eq_zero]

theorem elemY_ne_one : (elemY (F := F)) ≠ 1 := by
  intro h
  have h' : (elemY (F := F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [h, SpecialLinearGroup.coe_one]
  rw [coe_elemY, Matrix.one_fin_two] at h'
  have h00 := congrFun (congrFun h' 0) 0
  simp at h00

theorem orderOf_elemY : orderOf (elemY (F := F)) = 3 :=
  orderOf_eq_prime elemY_pow_three elemY_ne_one

theorem elemY_inv_eq_sq : (elemY (F := F))⁻¹ = elemY ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact elemY_pow_three (F := F))

theorem elemW_mul_elemW : (elemW (F := F)) * elemW = 1 := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, coe_elemW, SpecialLinearGroup.coe_one, Matrix.mul_fin_two,
    Matrix.one_fin_two]
  norm_num

theorem elemW_inv : (elemW (F := F))⁻¹ = elemW :=
  inv_eq_of_mul_eq_one_right elemW_mul_elemW

theorem upper_one_mul_upper_one : upper (1 : F) * upper 1 = 1 := by
  rw [upper_mul_upper, CharTwo.add_self_eq_zero, upper_zero]

theorem upper_one_inv : (upper (1 : F))⁻¹ = upper 1 :=
  inv_eq_of_mul_eq_one_right upper_one_mul_upper_one

/-- `s y s⁻¹ = y²` for `s = [[1, 1], [0, 1]]`: the prime-field line normalizes `Q = ⟨y⟩`. -/
theorem upper_one_conj_elemY :
    upper (1 : F) * elemY * (upper (1 : F))⁻¹ = elemY ^ 2 := by
  apply Subtype.ext
  rw [upper_one_inv, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_elemY_sq,
    coe_upper, coe_elemY, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [CharTwo.add_self_eq_zero]

/-- The prime-field line normalizes `Q = ⟨y⟩`, the first half of hypothesis (B). -/
theorem upper_one_mem_normalizer_zpowers_elemY :
    upper (1 : F) ∈ Subgroup.normalizer
      ((Subgroup.zpowers (elemY (F := F))) : Set (SpecialLinearGroup (Fin 2) F)) := by
  refine mem_normalizer_zpowers_of_inv_self upper_one_inv ?_
  rw [upper_one_conj_elemY]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2

/-- `y⁻¹ s y = w` for `s = [[1, 1], [0, 1]]`: the book's `σ(P₀)^y` is the Weyl element, which
normalizes the split torus `σ(U)`. -/
theorem elemY_inv_conj_upper_one :
    (elemY (F := F))⁻¹ * upper (1 : F) * elemY = elemW := by
  apply Subtype.ext
  rw [elemY_inv_eq_sq, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_elemY_sq,
    coe_upper, coe_elemY, coe_elemW, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [CharTwo.add_self_eq_zero]

/-- The Weyl element inverts the split torus: `w [[u, 0], [0, u⁻¹]] w⁻¹ = [[u⁻¹, 0], [0, u]]`. -/
theorem elemW_conj_torus (u : Fˣ) :
    elemW * torus u * (elemW (F := F))⁻¹ = torus u⁻¹ := by
  apply Subtype.ext
  rw [elemW_inv, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_elemW, coe_torus,
    coe_torus, Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num [Units.val_inv_eq_inv_val]

end CharTwo

end SL2

/-! ## The monomorphism `σ : H → SL(2, 2^q)` -/

section Model

variable (q : ℕ)

/-- Inverse of the squaring automorphism of `𝔽_{2^q}ˣ`: `u ↦ u^(2^(q-1))`, a square root because
`u^(2^q) = u`.  See the module docstring for why `σ|_U` needs this twist. -/
noncomputable def sqrtHom : (GaloisField 2 q)ˣ →* (GaloisField 2 q)ˣ :=
  powMonoidHom (2 ^ (q - 1))

@[simp] theorem sqrtHom_apply (u : (GaloisField 2 q)ˣ) :
    sqrtHom q u = u ^ (2 ^ (q - 1)) := rfl

/-- `√u` really is a square root of `u`. -/
theorem sqrtHom_sq (hq : q ≠ 0) (u : (GaloisField 2 q)ˣ) :
    sqrtHom q u * sqrtHom q u = u := by
  have : Fintype (GaloisField 2 q) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 q) = 2 ^ q := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 q hq
  have hpow : (2 : ℕ) ^ (q - 1) * 2 = 2 ^ q := by
    rw [← pow_succ]
    congr 1
    omega
  refine Units.ext ?_
  rw [Units.val_mul, sqrtHom_apply, Units.val_pow_eq_pow_val, ← pow_add,
    show 2 ^ (q - 1) + 2 ^ (q - 1) = 2 ^ (q - 1) * 2 by ring, hpow, ← hcard]
  exact FiniteField.pow_card _

/-- The square-root relation on the level of field elements. -/
theorem sqrtHom_val_mul_val (hq : q ≠ 0) (u : (GaloisField 2 q)ˣ) :
    ((sqrtHom q u : (GaloisField 2 q)ˣ) : GaloisField 2 q) *
        ((sqrtHom q u : (GaloisField 2 q)ˣ) : GaloisField 2 q) =
      (u : GaloisField 2 q) := by
  rw [← Units.val_mul, sqrtHom_sq q hq]

/-- The compatibility condition making `σ` of Remark (II) a homomorphism on `H = P ⋊ U`. -/
theorem sigmaSL2_compat (hq : q ≠ 0) (u : NormSet.normOneUnits 2 q) :
    (SL2.upperHom : Multiplicative (GaloisField 2 q) →* _).comp
        ((NormSet.normOneMulAction 2 q u).toMonoidHom) =
      (MulAut.conj
          ((SL2.torusHom.comp
            ((sqrtHom q).comp (NormSet.normOneUnits 2 q).subtype)) u)).toMonoidHom.comp
        SL2.upperHom := by
  refine MonoidHom.ext fun a => ?_
  have hsq := sqrtHom_val_mul_val q hq (u : (GaloisField 2 q)ˣ)
  have hact : ((NormSet.normOneMulAction 2 q u) a).toAdd =
      ((u : (GaloisField 2 q)ˣ) : GaloisField 2 q) * a.toAdd :=
    NormSet.normOneMulAction_apply 2 q u a.toAdd
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, SL2.upperHom_apply, SL2.torusHom_apply, Subgroup.coe_subtype]
  rw [SL2.torus_mul_upper_mul_torus_inv, hsq, hact]

/-- **BG Appendix C, Remark (II)**, the monomorphism `σ : H = P ⋊ U → SL(2, 2^q)`.

On the kernel `P = 𝔽_{2^q}` it is `a ↦ [[1, a], [0, 1]]`; on the complement `U` it is
`u ↦ [[√u, 0], [0, √u⁻¹]]`, whose image is the full split torus `{[[a, 0], [0, a⁻¹]]}`. -/
noncomputable def sigmaSL2 (hq : q ≠ 0) :
    NormSet.normOneFrobeniusGroup 2 q →* SpecialLinearGroup (Fin 2) (GaloisField 2 q) :=
  SemidirectProduct.lift SL2.upperHom
    (SL2.torusHom.comp ((sqrtHom q).comp (NormSet.normOneUnits 2 q).subtype))
    (sigmaSL2_compat q hq)

@[simp] theorem sigmaSL2_inl (hq : q ≠ 0) (a : GaloisField 2 q) :
    sigmaSL2 q hq (SemidirectProduct.inl (Multiplicative.ofAdd a)) = SL2.upper a :=
  SemidirectProduct.lift_inl _ _ _ _

@[simp] theorem sigmaSL2_inr (hq : q ≠ 0) (u : NormSet.normOneUnits 2 q) :
    sigmaSL2 q hq (SemidirectProduct.inr u) =
      SL2.torus (sqrtHom q (u : (GaloisField 2 q)ˣ)) :=
  SemidirectProduct.lift_inr _ _ _ _

theorem sigmaSL2_apply (hq : q ≠ 0) (g : NormSet.normOneFrobeniusGroup 2 q) :
    sigmaSL2 q hq g =
      SL2.upper g.left.toAdd * SL2.torus (sqrtHom q (g.right : (GaloisField 2 q)ˣ)) := rfl

theorem sigmaSL2_injective (hq : q ≠ 0) : Function.Injective (sigmaSL2 q hq) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [sigmaSL2_apply] at hg
  obtain ⟨ha, hu⟩ := (SL2.upper_mul_torus_eq_one_iff _ _).mp hg
  have hright : g.right = 1 := by
    refine Subtype.ext (Units.ext ?_)
    have hval := sqrtHom_val_mul_val q hq (g.right : (GaloisField 2 q)ˣ)
    rw [hu] at hval
    simpa using hval.symm
  have hleft : g.left = 1 := by
    refine Multiplicative.toAdd.injective ?_
    simpa using ha
  exact SemidirectProduct.ext hleft hright

/-- Every element of the prime-field line `P₀` is trivial or the generator `ofAdd 1`.

For `p = 2` the prime field is `𝔽_2 = {0, 1}`, so `σ(P₀) = ⟨[[1, 1], [0, 1]]⟩` has order `2`,
as stated in BG Appendix C, Remark (II). -/
theorem mem_primeLine_two {g : NormSet.normOneFrobeniusGroup 2 q}
    (hg : g ∈ primeLine 2 q) :
    g = 1 ∨ g = SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField 2 q)) := by
  rw [primeLine, NormSet.normOneFrobeniusSubspaceKernel] at hg
  obtain ⟨z, hz, rfl⟩ := hg
  have hzmem : z.toAdd ∈
      Submodule.span (ZMod 2) ({(1 : GaloisField 2 q)} : Set (GaloisField 2 q)) := hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzmem
  have hc2 : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
  rcases hc2 c with rfl | rfl
  · left
    rw [zero_smul] at hc
    have hz1 : z = 1 := Multiplicative.toAdd.injective (by simpa using hc.symm)
    rw [hz1, map_one]
  · right
    rw [one_smul] at hc
    congr 1
    exact Multiplicative.toAdd.injective (by simpa using hc.symm)

/-! ### The images `σ(P)`, `σ(U)` as displayed in the book -/

/-- For `p = 2` the norm `N(x) = x^(2^q - 1)` is identically `1` on units, so `U` is the whole
multiplicative group `𝔽_{2^q}ˣ` and `H = P ⋊ U` is the affine group `AGL(1, 2^q)`. -/
theorem normOneUnits_two_eq_top (hq : q ≠ 0) : NormSet.normOneUnits 2 q = ⊤ := by
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [NormSet.normOneUnits_card 2 q hq, Nat.card_units, GaloisField.card 2 q hq]
  norm_num

/-- The square-root map `u ↦ u^(2^(q-1))` is a bijection of `𝔽_{2^q}ˣ`; this is why the image of
`σ|_U` is the *full* split torus. -/
theorem sqrtHom_bijective (hq : q ≠ 0) : Function.Bijective (sqrtHom q) := by
  have hinj : Function.Injective (sqrtHom q) := fun u v huv => by
    rw [← sqrtHom_sq q hq u, ← sqrtHom_sq q hq v, huv]
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

theorem sigmaSL2_comp_inl (hq : q ≠ 0) :
    (sigmaSL2 q hq).comp
        (SemidirectProduct.inl : NormSet.additiveFieldGroup 2 q →* _) = SL2.upperHom :=
  MonoidHom.ext fun a => sigmaSL2_inl q hq a.toAdd

/-- **BG Appendix C, Remark (II)**: `σ(P) = {[[1, a], [0, 1]] | a ∈ 𝔽_{2^q}}`. -/
theorem map_kernel_sigmaSL2 (hq : q ≠ 0) :
    (NormSet.normOneFrobeniusKernel 2 q).map (sigmaSL2 q hq) =
      (SL2.upperHom : Multiplicative (GaloisField 2 q) →* _).range := by
  rw [NormSet.normOneFrobeniusKernel, MonoidHom.map_range, sigmaSL2_comp_inl]

/-- **BG Appendix C, Remark (II)**: `σ(U) = {[[a, 0], [0, a⁻¹]] | a ∈ 𝔽_{2^q}ˣ}`, the full
split torus. -/
theorem map_complement_sigmaSL2 (hq : q ≠ 0) :
    (NormSet.normOneFrobeniusComplement 2 q).map (sigmaSL2 q hq) =
      (SL2.torusHom : (GaloisField 2 q)ˣ →* _).range := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨g, hg, rfl⟩
    rw [NormSet.normOneFrobeniusComplement] at hg
    obtain ⟨u, rfl⟩ := hg
    exact ⟨sqrtHom q (u : (GaloisField 2 q)ˣ), (sigmaSL2_inr q hq u).symm⟩
  · rintro x ⟨v, rfl⟩
    obtain ⟨u, rfl⟩ := (sqrtHom_bijective q hq).2 v
    have hu : u ∈ NormSet.normOneUnits 2 q := by
      rw [normOneUnits_two_eq_top q hq]
      exact Subgroup.mem_top u
    exact ⟨SemidirectProduct.inr ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩, sigmaSL2_inr q hq ⟨u, hu⟩⟩

/-- **BG Appendix C, Remark (II)**: `σ(P₀) = ⟨[[1, 1], [0, 1]]⟩`, of order `2`. -/
theorem map_primeLine_sigmaSL2 (hq : q ≠ 0) :
    (primeLine 2 q).map (sigmaSL2 q hq) =
      Subgroup.zpowers (SL2.upper (1 : GaloisField 2 q)) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨g, hg, rfl⟩
    rcases mem_primeLine_two q hg with rfl | rfl
    · rw [map_one]
      exact Subgroup.one_mem _
    · rw [sigmaSL2_inl]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField 2 q)), ?_,
      sigmaSL2_inl q hq 1⟩
    rw [primeLine]
    exact (NormSet.mem_normOneFrobeniusSubspaceKernel_inl 2 q _ 1).mpr
      (Submodule.mem_span_singleton_self _)

end Model

/-! ## Condition (A) and hypothesis (B) for `p = 2` -/

/-- **BG Appendix C, condition (A) for `p = 2`**: it reads `gcd((2^q - 1)/1, 1) = 1`, so it holds
for every `q`.  This is also immediate from Remark (I): condition (A) says `q ∤ p - 1`, and
`p - 1 = 1` has no prime divisor. -/
theorem conditionA_two (q : ℕ) : conditionA 2 q := by
  unfold conditionA
  norm_num

/-- The Weyl element normalizes `σ(U)`, the split torus. -/
theorem elemW_mem_normalizer_complement (q : ℕ) (hq : q ≠ 0) :
    SL2.elemW ∈ Subgroup.normalizer
      (((NormSet.normOneFrobeniusComplement 2 q).map (sigmaSL2 q hq) :
          Subgroup (SpecialLinearGroup (Fin 2) (GaloisField 2 q))) :
        Set (SpecialLinearGroup (Fin 2) (GaloisField 2 q))) := by
  refine mem_normalizer_of_inv_self SL2.elemW_inv ?_
  rintro n ⟨g, hg, rfl⟩
  rw [NormSet.normOneFrobeniusComplement] at hg
  obtain ⟨u, rfl⟩ := hg
  refine ⟨SemidirectProduct.inr u⁻¹, ⟨u⁻¹, rfl⟩, ?_⟩
  rw [sigmaSL2_inr, sigmaSL2_inr, SL2.elemW_conj_torus, Subgroup.coe_inv, map_inv]

set_option backward.isDefEq.respectTransparency false in
/-- **BG Appendix C, Remark (II)** (T. Peterfalvi).  For every `q ≠ 0` the group `SL(2, 2^q)`
satisfies hypothesis (B) of Theorem C with `p = 2`.

Together with `conditionA_two` this shows that the hypotheses of Theorem C are satisfiable, so
Theorem C is not vacuous, and that its bound `p ≤ q` is attained at `p = 2` (Remark (IV)).

The data are exactly the book's: `σ(P) = {[[1, a], [0, 1]]}`, `σ(P₀) = ⟨[[1, 1], [0, 1]]⟩`,
`σ(U) = {[[a, 0], [0, a⁻¹]]}`, `y = [[0, 1], [1, 1]]` and `Q = ⟨y⟩` (cyclic of order `3`, hence
finite abelian of odd order).  The distinguished element of the structure is `y⁻¹`, so that
`MulAut.conj y⁻¹ • σ(P₀) = y⁻¹ σ(P₀) y` is the book's `σ(P₀)^y` verbatim; see
`HypothesisBAbstract`. -/
noncomputable def hypothesisBAbstract_sl2 (q : ℕ) (hq : q ≠ 0) :
    HypothesisBAbstract 2 q (SpecialLinearGroup (Fin 2) (GaloisField 2 q)) where
  sigma := sigmaSL2 q hq
  sigma_injective := sigmaSL2_injective q hq
  Q := Subgroup.zpowers (SL2.elemY (F := GaloisField 2 q))
  Q_finite := inferInstance
  Q_commutative := inferInstance
  Q_pPrime := by
    rw [Nat.card_zpowers, SL2.orderOf_elemY]
    decide
  y := (SL2.elemY (F := GaloisField 2 q))⁻¹
  y_mem_Q := Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  primeLine_normalizes_Q := by
    rintro x ⟨g, hg, rfl⟩
    rcases mem_primeLine_two q hg with rfl | rfl
    · rw [map_one]
      exact Subgroup.one_mem _
    · rw [sigmaSL2_inl]
      exact SL2.upper_one_mem_normalizer_zpowers_elemY
  primeLine_conj_normalizes_U := by
    intro x hx
    rw [Subgroup.pointwise_smul_def] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := hz
    rcases mem_primeLine_two q hg with rfl | rfl
    · rw [map_one, map_one]
      exact Subgroup.one_mem _
    · rw [sigmaSL2_inl]
      change (MulAut.conj (SL2.elemY (F := GaloisField 2 q))⁻¹) (SL2.upper 1) ∈ _
      rw [MulAut.conj_apply, inv_inv, SL2.elemY_inv_conj_upper_one]
      exact elemW_mem_normalizer_complement q hq

/-- **Theorem C runs on Remark (II)**: applying `theoremC_of_hypothesisBAbstract` to the
`SL(2, 2^q)` witness of hypothesis (B) gives `2 ≤ q`.

The conclusion is of course immediate for a prime `q`; the content is that the route
*(A) + (B) ⟹ `p ≤ q`* really is closed on a configuration having nothing to do with the
Feit--Thompson spine.  Hypothesis (B) is therefore not vacuous, and Theorem C is not secretly
using Section 16 data. -/
theorem theoremC_sl2 (q : ℕ) (hq : q.Prime) : 2 ≤ q :=
  theoremC_of_hypothesisBAbstract (hypothesisBAbstract_sl2 q hq.ne_zero) hq (conditionA_two q)

end OddOrder.BG.AppC
