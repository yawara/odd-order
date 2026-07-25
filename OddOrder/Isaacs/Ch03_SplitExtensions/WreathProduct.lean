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

/-! ### Problem 3A.9(a) — 推移的作用のとき `C_B(Q)` = 定数関数 -/

/-- **Isaacs Problem 3A.9(a)** (元ごとの形). `Q` の `Ω` への作用が推移的なとき、base group の
元 `inl f` が `inr q` すべてと可換 ⟺ `f` が定数。

共役公式 `inr q * inl f * (inr q)⁻¹ = inl (f ∘ (q⁻¹ • ·))` (`inr_mul_inl_mul_inr_inv`) から、
可換性は `f (q⁻¹ • ω) = f ω` (∀ q, ω)、すなわち `f` が `Q`-軌道上で定数。推移的なら全体で定数。 -/
theorem forall_conj_inr_eq_iff_const [MulAction.IsPretransitive Q Ω] (f : Ω → D) :
    (∀ q : Q, (inr q : D ≀[Ω] Q) * inl f * (inr q)⁻¹ = inl f) ↔ ∀ ω ω' : Ω, f ω = f ω' := by
  constructor
  · intro h ω ω'
    obtain ⟨q, rfl⟩ := MulAction.exists_smul_eq Q ω ω'
    have hf : (fun x => f (q⁻¹ • x)) = f :=
      inl_injective (by rw [← inr_mul_inl_mul_inr_inv]; exact h q)
    have h2 := congrFun hf (q • ω)
    rwa [inv_smul_smul] at h2
  · intro h q
    rw [inr_mul_inl_mul_inr_inv]
    exact congrArg inl (funext fun ω => h _ _)

/-- **Isaacs Problem 3A.9(a)**. `Q` の `Ω` への作用が推移的なとき、base group `B` の元で
`Q` の像 `inr '' Q` に中心化されるものはちょうど定数関数 `Ω → D` の像。 -/
theorem mem_centralizer_range_inr_iff [MulAction.IsPretransitive Q Ω] [Nonempty Ω]
    (f : Ω → D) :
    (inl f : D ≀[Ω] Q) ∈
        Subgroup.centralizer ((inr : Q →* D ≀[Ω] Q).range : Set (D ≀[Ω] Q)) ↔
      ∃ d : D, f = Function.const Ω d := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    obtain ⟨ω₀⟩ := ‹Nonempty Ω›
    refine ⟨f ω₀, funext fun ω => ?_⟩
    refine (forall_conj_inr_eq_iff_const (D := D) (Q := Q) (Ω := Ω) f).mp (fun q => ?_) ω ω₀
    have hq := h (inr q) ⟨q, rfl⟩
    calc (inr q : D ≀[Ω] Q) * inl f * (inr q)⁻¹
        = inl f * inr q * (inr q)⁻¹ := by rw [hq]
      _ = inl f := by group
  · rintro ⟨d, rfl⟩ x hx
    obtain ⟨q, rfl⟩ := hx
    have hc := (forall_conj_inr_eq_iff_const (D := D) (Q := Q) (Ω := Ω)
      (Function.const Ω d)).mpr (fun _ _ => rfl) q
    calc (inr q : D ≀[Ω] Q) * inl (Function.const Ω d)
        = inr q * inl (Function.const Ω d) * (inr q)⁻¹ * inr q := by group
      _ = inl (Function.const Ω d) * inr q := by rw [hc]

/-! ### Problem 3A.9(b) — 正則 wreath product では任意の部分群が base の元の中心化群 -/

/-- **Isaacs Problem 3A.9(b)**. **正則** wreath product `W = D ≀[Q] Q` (`Ω = Q` に左正則作用)
において、`Q` の任意の部分群 `C` に対し base group の元 `b : Q → D` で
「`inl b` を中心化する `Q` の元全体がちょうど `C`」となるものが存在する。

`b` を `C` の指示関数 (`C` 上で `d ≠ 1`、外で `1`) に取ればよい: 共役公式から中心化条件は
`b (g⁻¹ · ω) = b ω` (∀ω)、すなわち `g⁻¹ω ∈ C ↔ ω ∈ C` (∀ω) で、`ω = 1` を入れると
`g⁻¹ ∈ C`、逆に `g ∈ C` なら `Subgroup.mul_mem_cancel_left` で成立。

⚠ `D` の非自明性は必須 (`D = 1` なら base group が自明で中心化群は常に `Q` 全体)。 -/
theorem exists_base_centralizer_eq [Nontrivial D] (C : Subgroup Q) :
    ∃ b : Q → D, ∀ g : Q,
      ((inr g : D ≀[Q] Q) * inl b * (inr g)⁻¹ = inl b ↔ g ∈ C) := by
  classical
  obtain ⟨d, hd⟩ := exists_ne (1 : D)
  refine ⟨fun ω => if ω ∈ C then d else 1, fun g => ?_⟩
  rw [inr_mul_inl_mul_inr_inv]
  constructor
  · intro h
    have hf := congrFun (inl_injective h) 1
    simp only [smul_eq_mul, mul_one] at hf
    by_contra hg
    have hginv : g⁻¹ ∉ C := fun hc => hg (by simpa using C.inv_mem hc)
    rw [if_neg hginv, if_pos C.one_mem] at hf
    exact hd hf.symm
  · intro hg
    refine congrArg inl (funext fun ω => ?_)
    simp only [smul_eq_mul]
    exact if_congr (C.mul_mem_cancel_left (C.inv_mem hg)) rfl rfl

end WreathProduct

end OddOrder.Isaacs.Ch03
