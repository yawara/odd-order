/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.RegularWreathProduct

/-!
# Isaacs §3A: general wreath product over a `G`-set (pp. 73-76)

**Isaacs Def §3A (wreath product, general form)**: 群 `D` と, 集合 `Ω` に作用する群 `Q`
に対し, wreath product `D ≀[Ω] Q` は台 `(Ω → D) × Q` に
`⟨a₁, a₂⟩ * ⟨b₁, b₂⟩ = ⟨a₁ * (b₁ ∘ (a₂⁻¹ • ·)), a₂ * b₂⟩` を入れた群
(= base 群 `Ω → D` と座標置換作用の半直積).

mathlib は **regular** wreath product (`Ω = Q` の左正則作用, `D ≀ᵣ Q`,
`Mathlib/GroupTheory/RegularWreathProduct.lean`) のみ収載のため, 教科書の一般形を
ここに実装する. 実装は mathlib の `RegularWreathProduct` を作用 `•` で一般化した
ミラー (upstream しやすい形). `wreathEquivRegular` で `Ω = Q` (左正則作用) の場合が
mathlib の `D ≀ᵣ Q` と同型であることを記録する.
-/

namespace OddOrder.Isaacs.Ch03

variable (D Q Ω : Type*) [Group D] [Group Q] [MulAction Q Ω]

/-- **Isaacs §3A (general wreath product)**: `Q`-集合 `Ω` 上の wreath product.
台は `(Ω → D) × Q`, 積は `⟨a₁, a₂⟩ * ⟨b₁, b₂⟩ = ⟨a₁ * (b₁ ∘ (a₂⁻¹ • ·)), a₂ * b₂⟩`.
mathlib `RegularWreathProduct` の `Ω = Q` (左正則作用) を一般の作用に置換した形. -/
@[ext]
structure WreathProduct where
  /-- The base component `Ω → D`. -/
  left : Ω → D
  /-- The permuting component in `Q`. -/
  right : Q

@[inherit_doc] notation:65 D " ≀[" Ω "] " Q => WreathProduct D Q Ω

namespace WreathProduct

variable {D Q Ω}

instance : Mul (D ≀[Ω] Q) where
  mul a b := ⟨a.1 * fun ω => b.1 (a.2⁻¹ • ω), a.2 * b.2⟩

@[simp]
theorem mul_left (a b : D ≀[Ω] Q) : (a * b).left = a.1 * fun ω => b.1 (a.2⁻¹ • ω) := rfl

@[simp]
theorem mul_right (a b : D ≀[Ω] Q) : (a * b).right = a.right * b.right := rfl

instance : One (D ≀[Ω] Q) where one := ⟨1, 1⟩

omit [MulAction Q Ω] in
@[simp] theorem one_left : (1 : D ≀[Ω] Q).left = 1 := rfl

omit [MulAction Q Ω] in
@[simp] theorem one_right : (1 : D ≀[Ω] Q).right = 1 := rfl

instance : Inv (D ≀[Ω] Q) where
  inv x := ⟨fun ω => x.1⁻¹ (x.2 • ω), x.2⁻¹⟩

@[simp]
theorem inv_left (a : D ≀[Ω] Q) : a⁻¹.left = fun ω => a.left⁻¹ (a.right • ω) := rfl

@[simp]
theorem inv_right (a : D ≀[Ω] Q) : a⁻¹.right = a.right⁻¹ := rfl

instance : Group (D ≀[Ω] Q) where
  mul_assoc a b c := by ext <;> simp [mul_assoc, mul_smul]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp

instance : Inhabited (D ≀[Ω] Q) := ⟨1⟩

/-- The canonical projection `D ≀[Ω] Q →* Q`. -/
def rightHom : (D ≀[Ω] Q) →* Q where
  toFun := WreathProduct.right
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem rightHom_apply (a : D ≀[Ω] Q) : rightHom a = a.right := rfl

/-- The canonical injection `Q →* D ≀[Ω] Q` onto the permuting component. -/
def inr : Q →* D ≀[Ω] Q where
  toFun q := ⟨1, q⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[simp] theorem left_inr (q : Q) : (inr q : D ≀[Ω] Q).left = 1 := rfl

@[simp] theorem right_inr (q : Q) : (inr q : D ≀[Ω] Q).right = q := rfl

/-- The canonical injection of the base group `(Ω → D) →* D ≀[Ω] Q`. -/
def inl : (Ω → D) →* D ≀[Ω] Q where
  toFun f := ⟨f, 1⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[simp] theorem left_inl (f : Ω → D) : (inl f : D ≀[Ω] Q).left = f := rfl

@[simp] theorem right_inl (f : Ω → D) : (inl f : D ≀[Ω] Q).right = 1 := rfl

theorem inl_injective : Function.Injective (inl : (Ω → D) →* D ≀[Ω] Q) :=
  fun _ _ h => congrArg WreathProduct.left h

theorem inr_injective : Function.Injective (inr : Q →* D ≀[Ω] Q) :=
  fun _ _ h => congrArg WreathProduct.right h

@[simp]
theorem rightHom_comp_inr : (rightHom : (D ≀[Ω] Q) →* Q).comp inr = MonoidHom.id _ := by
  ext; simp

/-- The base subgroup `(Ω → D) × 1` is the kernel of `rightHom`, hence normal. -/
theorem range_inl_eq_ker_rightHom :
    (inl : (Ω → D) →* D ≀[Ω] Q).range = (rightHom : (D ≀[Ω] Q) →* Q).ker := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    simp [MonoidHom.mem_ker, rightHom]
  · intro hx
    rw [MonoidHom.mem_ker, rightHom_apply] at hx
    exact ⟨x.left, by ext <;> simp [hx]⟩

/-- Conjugation of a base element by `inr q` permutes the coordinates:
`inr q * inl f * (inr q)⁻¹ = inl (f ∘ (q⁻¹ • ·))`. -/
theorem inr_mul_inl_mul_inr_inv (q : Q) (f : Ω → D) :
    (inr q : D ≀[Ω] Q) * inl f * (inr q)⁻¹ = inl fun ω => f (q⁻¹ • ω) := by
  ext <;> simp

/-- The underlying equiv with the product type. -/
def equivProd : (D ≀[Ω] Q) ≃ (Ω → D) × Q where
  toFun x := ⟨x.left, x.right⟩
  invFun x := ⟨x.1, x.2⟩

instance [Finite D] [Finite Q] [Finite Ω] : Finite (D ≀[Ω] Q) :=
  Finite.of_equiv _ (equivProd (D := D) (Q := Q) (Ω := Ω)).symm

omit [Group D] [Group Q] in
/-- `|D ≀[Ω] Q| = |D|^|Ω| · |Q|`. -/
theorem card [Finite Ω] : Nat.card (D ≀[Ω] Q) = Nat.card D ^ Nat.card Ω * Nat.card Q := by
  rw [Nat.card_congr (equivProd (D := D) (Q := Q) (Ω := Ω)), Nat.card_prod (Ω → D) Q,
    Nat.card_fun]

/-- **Regular case**: `Ω = Q` に左正則作用を入れた `D ≀[Q] Q` は mathlib の
`RegularWreathProduct D Q` と同型 (作用 `q⁻¹ • x = q⁻¹ * x` が定義ごと一致). -/
def wreathEquivRegular : (D ≀[Q] Q) ≃* RegularWreathProduct D Q where
  toFun x := ⟨x.left, x.right⟩
  invFun x := ⟨x.left, x.right⟩
  map_mul' a b := by
    ext ω
    · change (a.left * fun x => b.left (a.right⁻¹ • x)) ω =
        (a.left * fun x => b.left (a.right⁻¹ * x)) ω
      rfl
    · rfl

end WreathProduct

end OddOrder.Isaacs.Ch03
