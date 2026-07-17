import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroupsCoprime

/-!
# Isaacs §4D 後半 — Baer trick (Lem 4.37) と応用 (pp. 141-146)

Split from the former monolithic `OddOrder.Isaacs.Ch04_Commutators.Main` (directory split, issue
0103).
-/
namespace OddOrder.Isaacs.Ch04
open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 4D: Coprime action — Fitting + Thompson PxQ + Baer (pp. 138-146) -/

/-! ### Isaacs §4D: Baer trick (Lem 4.37) — odd order class ≤ 2 ⇒ additive group structure

For `G` finite of **odd order** and **nilpotence class ≤ 2**, define
`baerAdd x y := x * y * sqrtOdd ⁅y, x⁆`. Then `(G, baerAdd)` is an abelian group, and:
- (a) commuting elements satisfy `x +' y = x * y`.
- (b) Additive order = multiplicative order.
- (c) Every multiplicative automorphism is also an additive automorphism.

下流: Thm 4.36 (p > 2, p-群 + p'-A fixes order-p elements ⇒ A trivial) で利用. -/

/-- **Square root in groups with odd `Nat.card`**: `sqrtOdd x := x^((|G|+1)/2)`.
For `Odd (Nat.card G)`, `(sqrtOdd x)² = x` (`pow_card_eq_one'` で `x^(|G|+1) = x`). -/
noncomputable def sqrtOdd {G : Type*} [Group G] (x : G) : G :=
  x ^ ((Nat.card G + 1) / 2)

lemma sqrtOdd_def {G : Type*} [Group G] (x : G) :
    sqrtOdd x = x ^ ((Nat.card G + 1) / 2) := rfl

/-- **核補題**: `Odd (Nat.card G) ⇒ (sqrtOdd x)² = x`. -/
lemma sqrtOdd_sq {G : Type*} [Group G] (hOdd : Odd (Nat.card G)) (x : G) :
    (sqrtOdd x) ^ 2 = x := by
  unfold sqrtOdd
  rw [← pow_mul]
  have h_eq : (Nat.card G + 1) / 2 * 2 = Nat.card G + 1 := by
    obtain ⟨k, hk⟩ := hOdd; rw [hk]; omega
  rw [h_eq, pow_succ, pow_card_eq_one', one_mul]

@[simp] lemma sqrtOdd_one {G : Type*} [Group G] : sqrtOdd (1 : G) = 1 := by
  simp [sqrtOdd]

lemma sqrtOdd_inv {G : Type*} [Group G] (x : G) : sqrtOdd x⁻¹ = (sqrtOdd x)⁻¹ := by
  unfold sqrtOdd; rw [← inv_pow]

lemma sqrtOdd_mul_of_commute {G : Type*} [Group G] {x y : G} (h : Commute x y) :
    sqrtOdd (x * y) = sqrtOdd x * sqrtOdd y := by
  unfold sqrtOdd; rw [Commute.mul_pow h]

lemma sqrtOdd_mem_subgroup {G : Type*} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    sqrtOdd x ∈ H := H.pow_mem hx _

/-- `sqrtOdd` の center 保存性. -/
lemma sqrtOdd_mem_center {G : Type*} [Group G] {x : G} (hx : x ∈ Subgroup.center G) :
    sqrtOdd x ∈ Subgroup.center G := sqrtOdd_mem_subgroup hx

/-- `sqrtOdd` is preserved by group homomorphisms (between groups of same cardinality).
For an automorphism `f : G ≃* G`, `f (sqrtOdd x) = sqrtOdd (f x)`. -/
lemma sqrtOdd_apply_mulEquiv {G : Type*} [Group G] (f : G ≃* G) (x : G) :
    f (sqrtOdd x) = sqrtOdd (f x) := by
  unfold sqrtOdd
  rw [map_pow]

/-- `sqrtOdd ⁅x, y⁆⁻¹ = sqrtOdd ⁅y, x⁆`. -/
lemma sqrtOdd_commutator_inv {G : Type*} [Group G] (x y : G) :
    sqrtOdd (⁅x, y⁆⁻¹ : G) = sqrtOdd ⁅y, x⁆ := by
  rw [commutatorElement_inv]

/-- **Baer addition** for class ≤ 2 odd order groups: `x +' y := x * y * sqrtOdd ⁅y, x⁆`. -/
noncomputable def baerAdd {G : Type*} [Group G] (x y : G) : G := x * y * sqrtOdd ⁅y, x⁆

lemma baerAdd_def {G : Type*} [Group G] (x y : G) :
    baerAdd x y = x * y * sqrtOdd ⁅y, x⁆ := rfl

/-- **Lem 4.37 part (a) precursor**: If `x` and `y` commute, then `x +' y = x * y`
(since `⁅y, x⁆ = 1` and `sqrtOdd 1 = 1`). -/
lemma baerAdd_eq_mul_of_commute {G : Type*} [Group G] {x y : G} (h : Commute x y) :
    baerAdd x y = x * y := by
  rw [baerAdd_def, (commutatorElement_eq_one_iff_commute (g₁ := y) (g₂ := x)).mpr h.symm,
      sqrtOdd_one, mul_one]

/-- Identity: `1 +' x = x`. -/
@[simp] lemma baerAdd_one_left {G : Type*} [Group G] (x : G) : baerAdd 1 x = x := by
  rw [baerAdd_def, one_mul, commutatorElement_one_right, sqrtOdd_one, mul_one]

/-- Identity: `x +' 1 = x`. -/
@[simp] lemma baerAdd_one_right {G : Type*} [Group G] (x : G) : baerAdd x 1 = x := by
  rw [baerAdd_def, mul_one, commutatorElement_one_left, sqrtOdd_one, mul_one]

/-- Inverse: `x +' x⁻¹ = 1`. -/
@[simp] lemma baerAdd_inv_right {G : Type*} [Group G] (x : G) : baerAdd x x⁻¹ = 1 := by
  have h1 : ⁅x⁻¹, x⁆ = (1 : G) :=
    commutatorElement_eq_one_iff_commute.mpr (Commute.refl x).inv_left
  rw [baerAdd_def, mul_inv_cancel, h1, sqrtOdd_one, mul_one]

/-- Inverse: `x⁻¹ +' x = 1`. -/
@[simp] lemma baerAdd_inv_left {G : Type*} [Group G] (x : G) : baerAdd x⁻¹ x = 1 := by
  have h1 : ⁅x, x⁻¹⁆ = (1 : G) :=
    commutatorElement_eq_one_iff_commute.mpr (Commute.refl x).inv_right
  rw [baerAdd_def, inv_mul_cancel, h1, sqrtOdd_one, mul_one]

/-- **Lem 4.37 commutativity**: `x +' y = y +' x` for class ≤ 2.

Derivation: `y +' x = y * x * sqrtOdd ⁅x, y⁆ = x * y * ⁅y, x⁆ * sqrtOdd ⁅x, y⁆`
(using `mul_comm_commutator_of_class_le_two`). Now `⁅x, y⁆⁻¹ = ⁅y, x⁆`, so
`sqrtOdd ⁅x, y⁆ = (sqrtOdd ⁅y, x⁆)⁻¹`. Combined:
`y +' x = x * y * ⁅y, x⁆ * (sqrtOdd ⁅y, x⁆)⁻¹ = x * y * sqrtOdd ⁅y, x⁆ = x +' y`
(using `(sqrtOdd ⁅y, x⁆)² = ⁅y, x⁆`). -/
lemma baerAdd_comm {G : Type*} [Group G] (hC : _root_.commutator G ≤ Subgroup.center G)
    (hOdd : Odd (Nat.card G)) (x y : G) :
    baerAdd x y = baerAdd y x := by
  rw [baerAdd_def, baerAdd_def]
  -- Set S := sqrtOdd ⁅y, x⁆. Show x * y * S = y * x * sqrtOdd ⁅x, y⁆.
  set S : G := sqrtOdd ⁅y, x⁆ with hS_def
  have h_yx : y * x = x * y * ⁅y, x⁆ := mul_comm_commutator_of_class_le_two hC x y
  have h_inv : (sqrtOdd ⁅x, y⁆ : G) = S⁻¹ := by
    rw [hS_def, ← sqrtOdd_inv]
    congr 1
    exact (commutatorElement_inv y x).symm
  have h_sq : S * S = ⁅y, x⁆ := by
    have := sqrtOdd_sq hOdd (⁅y, x⁆ : G); rw [sq] at this; exact this
  -- Goal: x * y * S = y * x * sqrtOdd ⁅x, y⁆
  rw [h_inv, h_yx]
  -- Goal: x * y * S = x * y * ⁅y, x⁆ * S⁻¹
  rw [← h_sq]
  -- Goal: x * y * S = x * y * (S * S) * S⁻¹
  group

/-- **Lem 4.37 (a)**: If `x` and `y` commute, then `x +' y = x * y`. -/
lemma baerAdd_eq_mul_of_commute' {G : Type*} [Group G] {x y : G} (h : Commute x y) :
    baerAdd x y = x * y := baerAdd_eq_mul_of_commute h

/-- `sqrtOdd` of a central element is central. -/
lemma sqrtOdd_central_of_central {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) : sqrtOdd z ∈ Subgroup.center G :=
  sqrtOdd_mem_subgroup hz

/-- Right-hom version of commutator in class ≤ 2: `⁅z, a * b⁆ = ⁅z, a⁆ * ⁅z, b⁆`.
Derived from left-hom + `commutatorElement_inv`. -/
lemma commutatorElement_mul_right_of_class_le_two {G : Type*} [Group G]
    (hC : _root_.commutator G ≤ Subgroup.center G) (z a b : G) :
    ⁅z, a * b⁆ = ⁅z, a⁆ * ⁅z, b⁆ := by
  -- ⁅z, a*b⁆ = ⁅a*b, z⁆⁻¹ = (⁅a, z⁆ * ⁅b, z⁆)⁻¹ = ⁅b, z⁆⁻¹ * ⁅a, z⁆⁻¹ = ⁅z, b⁆ * ⁅z, a⁆
  -- In class 2, ⁅z, a⁆ and ⁅z, b⁆ are central, so commute.
  have h_swap : (⁅z, a⁆ : G) * ⁅z, b⁆ = ⁅z, b⁆ * ⁅z, a⁆ := by
    have h_ca : ⁅z, a⁆ ∈ Subgroup.center G := hC (commutatorElement_mem_commutator_top z a)
    exact (Subgroup.mem_center_iff.mp h_ca _).symm
  have h_inv_ab : (⁅a * b, z⁆ : G)⁻¹ = ⁅z, a * b⁆ := commutatorElement_inv (a * b) z
  have h_left : (⁅a * b, z⁆ : G) = ⁅a, z⁆ * ⁅b, z⁆ :=
    commutatorElement_mul_left_of_class_le_two hC a b z
  rw [← h_inv_ab, h_left, mul_inv_rev, commutatorElement_inv, commutatorElement_inv, h_swap]

/-- **Lem 4.37 associativity**: `x +' (y +' z) = (x +' y) +' z` for class ≤ 2 + odd order.

**証明**: 両辺は `x * y * z * sqrtOdd ⁅z, y⁆ * sqrtOdd ⁅y, x⁆ * sqrtOdd ⁅z, x⁆` に等しい
(中心 commutators の積 は順序自由).

LHS = `x * (yz·S_{zy}) * S_{(yz·S_{zy}, x)}`:
- `⁅yz·S_{zy}, x⁆ = ⁅y, x⁆ * ⁅z, x⁆` (left hom + `⁅S_{zy}, x⁆ = 1`)
- `S_{⁅y,x⁆·⁅z,x⁆} = S_{y,x} * S_{z,x}` (sqrtOdd of central commuting product)

RHS = `(xy·S_{yx}) * z * S_{(z, xy·S_{yx})}`:
- `⁅z, xy·S_{yx}⁆ = ⁅z, x⁆ * ⁅z, y⁆` (right hom + `⁅z, S_{yx}⁆ = 1`)
- `z` moves past central `S_{yx}` ⇒ `xyz·S_{yx}·S_{⁅z,x⁆·⁅z,y⁆}`
- `S_{⁅z,x⁆·⁅z,y⁆} = S_{z,x} * S_{z,y}`. -/
lemma baerAdd_assoc {G : Type*} [Group G] (hC : _root_.commutator G ≤ Subgroup.center G)
    (x y z : G) :
    baerAdd x (baerAdd y z) = baerAdd (baerAdd x y) z := by
  -- Notation: S_{ab} = sqrtOdd ⁅a, b⁆
  set Syz : G := sqrtOdd ⁅z, y⁆
  set Sxy : G := sqrtOdd ⁅y, x⁆
  set Sxz : G := sqrtOdd ⁅z, x⁆
  -- Centrality of all sqrtOdd-of-commutator elements
  have h_Sc_zy : Syz ∈ Subgroup.center G :=
    sqrtOdd_central_of_central (hC (commutatorElement_mem_commutator_top z y))
  have h_Sc_yx : Sxy ∈ Subgroup.center G :=
    sqrtOdd_central_of_central (hC (commutatorElement_mem_commutator_top y x))
  have h_Sc_zx : Sxz ∈ Subgroup.center G :=
    sqrtOdd_central_of_central (hC (commutatorElement_mem_commutator_top z x))
  -- Helper: central element commutes with anything (Commute)
  have h_comm_central : ∀ {c : G}, c ∈ Subgroup.center G → ∀ a, Commute c a := fun hc a =>
    (Subgroup.mem_center_iff.mp hc a).symm
  have h_Comm_Syz : ∀ a, Commute Syz a := fun a => h_comm_central h_Sc_zy a
  have h_Comm_Sxy : ∀ a, Commute Sxy a := fun a => h_comm_central h_Sc_yx a
  -- LHS commutator computation: ⁅y * z * Syz, x⁆ = ⁅y, x⁆ * ⁅z, x⁆
  have h_LHS_arg : ⁅y * z * Syz, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ := by
    have h_yz_x : ⁅y * z, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ :=
      commutatorElement_mul_left_of_class_le_two hC y z x
    have h_Syz_x : ⁅Syz, x⁆ = (1 : G) :=
      (commutatorElement_eq_one_iff_commute (g₁ := Syz) (g₂ := x)).mpr (h_Comm_Syz x)
    rw [commutatorElement_mul_left_of_class_le_two hC, h_yz_x, h_Syz_x, mul_one]
  -- RHS commutator computation: ⁅z, x * y * Sxy⁆ = ⁅z, x⁆ * ⁅z, y⁆
  have h_RHS_arg : ⁅z, x * y * Sxy⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
    have h_z_xy : ⁅z, x * y⁆ = ⁅z, x⁆ * ⁅z, y⁆ :=
      commutatorElement_mul_right_of_class_le_two hC z x y
    have h_z_Sxy : ⁅z, Sxy⁆ = (1 : G) :=
      (commutatorElement_eq_one_iff_commute (g₁ := z) (g₂ := Sxy)).mpr (h_Comm_Sxy z).symm
    rw [commutatorElement_mul_right_of_class_le_two hC z (x * y) Sxy, h_z_xy, h_z_Sxy, mul_one]
  -- Distribute sqrtOdd over products of central commutators
  -- sqrtOdd (⁅y, x⁆ * ⁅z, x⁆) = Sxy * Sxz (centrals commute)
  have h_C_xy : (⁅y, x⁆ : G) ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top y x)
  have h_C_zx : (⁅z, x⁆ : G) ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top z x)
  have h_split_LHS : sqrtOdd (⁅y, x⁆ * ⁅z, x⁆ : G) = Sxy * Sxz :=
    sqrtOdd_mul_of_commute ((h_comm_central h_C_xy) ⁅z, x⁆)
  -- sqrtOdd (⁅z, x⁆ * ⁅z, y⁆) = Sxz * Syz
  have h_C_zy : (⁅z, y⁆ : G) ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top z y)
  have h_split_RHS : sqrtOdd (⁅z, x⁆ * ⁅z, y⁆ : G) = Sxz * Syz :=
    sqrtOdd_mul_of_commute ((h_comm_central h_C_zx) ⁅z, y⁆)
  -- Compute LHS and RHS
  -- LHS = x * (y * z * Syz) * sqrtOdd ⁅y * z * Syz, x⁆
  --     = x * y * z * Syz * sqrtOdd (⁅y, x⁆ * ⁅z, x⁆)
  --     = x * y * z * Syz * Sxy * Sxz
  -- RHS = (x * y * Sxy) * z * sqrtOdd ⁅z, x * y * Sxy⁆
  --     = x * y * Sxy * z * sqrtOdd (⁅z, x⁆ * ⁅z, y⁆)
  --     = x * y * Sxy * z * Sxz * Syz
  --     = x * y * z * Sxy * Sxz * Syz  (Sxy commutes with z)
  -- LHS = RHS iff Syz * Sxy * Sxz = Sxy * Sxz * Syz, which holds because all centrals commute.
  rw [baerAdd_def, baerAdd_def, baerAdd_def, baerAdd_def, h_LHS_arg, h_RHS_arg,
      h_split_LHS, h_split_RHS]
  -- Goal: x * (y * z * Syz) * (Sxy * Sxz) = (x * y * Sxy) * z * (Sxz * Syz)
  -- Both sides normalize to `x * y * z * Sxy * Sxz * Syz` via commutativity
  -- of central elements (Syz, Sxy, Sxz).
  have h_Sxy_z := h_Comm_Sxy z
  have h_LHS_norm :
      x * (y * z * Syz) * (Sxy * Sxz) = x * y * z * Sxy * Sxz * Syz := by
    have hC : Commute Syz (Sxy * Sxz) := (h_Comm_Syz Sxy).mul_right (h_Comm_Syz Sxz)
    have h_rearrange :
        x * (y * z * Syz) * (Sxy * Sxz) = (x * y * z) * (Syz * (Sxy * Sxz)) := by group
    rw [h_rearrange, hC.eq]; group
  have h_RHS_norm :
      (x * y * Sxy) * z * (Sxz * Syz) = x * y * z * Sxy * Sxz * Syz := by
    have h_rearrange :
        (x * y * Sxy) * z * (Sxz * Syz) = x * y * (Sxy * z) * (Sxz * Syz) := by group
    rw [h_rearrange, h_Sxy_z.eq]; group
  rw [h_LHS_norm, h_RHS_norm]

/-- **Lem 4.37 part (c)**: Every group homomorphism (between equal-card groups) preserves
`baerAdd`: `f (baerAdd x y) = baerAdd (f x) (f y)`. -/
lemma baerAdd_map_eq {G H : Type*} [Group G] [Group H] (f : G →* H)
    (h_card : Nat.card G = Nat.card H) (x y : G) :
    f (baerAdd x y) = baerAdd (f x) (f y) := by
  rw [baerAdd_def, baerAdd_def, map_mul, map_mul]
  congr 1
  -- f (sqrtOdd ⁅y, x⁆) = sqrtOdd (f ⁅y, x⁆) = sqrtOdd ⁅f y, f x⁆
  rw [sqrtOdd, sqrtOdd, h_card, map_pow, map_commutatorElement]

/-- **Lem 4.37 part (c) for MulEquiv** (Aut preservation): For `f : G ≃* G`,
`f (baerAdd x y) = baerAdd (f x) (f y)`. つまり multiplicative automorphism は
baerAdd を保存. -/
lemma baerAdd_mulEquiv_eq {G : Type*} [Group G] (f : G ≃* G) (x y : G) :
    f (baerAdd x y) = baerAdd (f x) (f y) :=
  baerAdd_map_eq f.toMonoidHom rfl x y

/-! ### Lem 4.37(b) element form + `BaerMul G` 型ラッパー (CommGroup 構造)

Baer trick の "additive group" は実際には Lean 上では type wrapper 経由で実装する.
`BaerMul G := G` (定義的に同型) に `CommGroup` インスタンスを `baerAdd` で与える.
これにより Cor 4.35 (CommGroup 仮定) を そのまま `BaerMul G` に適用できる.

教科書 (Isaacs p.142) (b) 証明の鍵: `nx = x + (n-1)x = x · x^(n-1) = x^n`
(commute case で `baerAdd_eq_mul_of_commute`). 実装では `npow x n := x^n` (G の冪) を直接採用し,
`npow_succ : npow (n+1) x = baerAdd (npow n x) x` を `baerAdd_pow_self_eq_pow_succ` で提供. -/

/-- **Lem 4.37(b) inductive step** (仮定不要): `baerAdd (x^n) x = x^(n+1)`.

`x` と `x^n` は常に commute するので, `baerAdd x^n x = x^n * x * sqrtOdd ⁅x, x^n⁆ = x^n · x · 1 = x^{n+1}`.
これが `BaerMul G` の `npow_succ` フィールドに対応する. -/
lemma baerAdd_pow_self_eq_pow_succ {G : Type*} [Group G] (x : G) (n : ℕ) :
    baerAdd (x ^ n) x = x ^ (n + 1) := by
  have h_comm : Commute (x ^ n) x := Commute.pow_self x n
  rw [baerAdd_eq_mul_of_commute h_comm, ← pow_succ]

/-- **Baer trick type wrapper**: `BaerMul G := G` (定義的に同型).

`G` が奇数位数 + class ≤ 2 のときに `BaerMul G` 上に `baerAdd` を乗法とする `CommGroup` 構造を
与える (Lem 4.37). これにより mathlib の CommGroup 用 API (Cor 4.35 等) を `BaerMul G` に
直接適用できる.

Naming: 乗法的 wrapper として扱う ("multiplicative view of (G, +')"). -/
def BaerMul (G : Type*) : Type _ := G

namespace BaerMul

variable {G : Type*}

/-- Coercion `BaerMul G ≃ G` (identity at runtime). -/
def toG : BaerMul G ≃ G := Equiv.refl _

/-- Coercion `G ≃ BaerMul G` (identity at runtime). -/
def ofG : G ≃ BaerMul G := Equiv.refl _

@[simp] theorem toG_ofG (x : G) : toG (ofG x) = x := rfl
@[simp] theorem ofG_toG (x : BaerMul G) : ofG (toG x) = x := rfl

end BaerMul

/-- `Mul (BaerMul G) = baerAdd`. -/
noncomputable instance BaerMul.instMul {G : Type*} [Group G] : Mul (BaerMul G) where
  mul x y := BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG y))

/-- `1 : BaerMul G = ofG 1`. -/
instance BaerMul.instOne {G : Type*} [One G] : One (BaerMul G) where
  one := BaerMul.ofG 1

/-- `(·)⁻¹ : BaerMul G → BaerMul G` is the same as G's inverse (Lem 4.37 で `baerAdd x⁻¹ x = 1`). -/
instance BaerMul.instInv {G : Type*} [Inv G] : Inv (BaerMul G) where
  inv x := BaerMul.ofG (BaerMul.toG x)⁻¹

/-- **CommGroup instance for `BaerMul G`**: `G` が `Odd (Nat.card G)` + `commutator G ≤ Z(G)`
を満たすとき, `(BaerMul G, baerAdd, 1, ·⁻¹)` は可換群.

実装方針: 基本 `Mul / One / Inv` instance を別途与えて, ここでは **axiom フィールドのみ提供**.
`npow / zpow` フィールドはデフォルト (`npowRec` / `zpowRec`) を使用. `npowRec` は `*`
(我々の baerAdd) を `n` 回反復するので, BaerMul の pow = `baerAdd`-iterate.
G の `x^n` との一致は Lem 4.37(b) (`baerAdd_pow_self_eq_pow_succ`) 経由で別途証明. -/
noncomputable instance BaerMul.instCommGroup {G : Type*} [Group G]
    [hOdd : Fact (Odd (Nat.card G))]
    [hC : Fact (_root_.commutator G ≤ Subgroup.center G)] : CommGroup (BaerMul G) where
  mul_assoc x y z := by
    change BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG
        y))))
        (BaerMul.toG z)) =
      BaerMul.ofG (baerAdd (BaerMul.toG x)
        (BaerMul.toG (BaerMul.ofG (baerAdd (BaerMul.toG y) (BaerMul.toG z)))))
    simp only [BaerMul.toG_ofG]
    exact congr_arg BaerMul.ofG
      (baerAdd_assoc hC.out (BaerMul.toG x) (BaerMul.toG y) (BaerMul.toG z)).symm
  one_mul x := by
    change BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG 1)) (BaerMul.toG x)) = x
    simp only [BaerMul.toG_ofG, baerAdd_one_left]
    rfl
  mul_one x := by
    change BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG (BaerMul.ofG 1))) = x
    simp only [BaerMul.toG_ofG, baerAdd_one_right]
    rfl
  mul_comm x y := by
    change BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG y)) =
      BaerMul.ofG (baerAdd (BaerMul.toG y) (BaerMul.toG x))
    exact congr_arg BaerMul.ofG (baerAdd_comm hC.out hOdd.out _ _)
  inv_mul_cancel x := by
    change BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG (BaerMul.toG x)⁻¹)) (BaerMul.toG x)) =
      BaerMul.ofG 1
    simp only [BaerMul.toG_ofG]
    rw [baerAdd_inv_left]

instance BaerMul.instFinite {G : Type*} [Finite G] : Finite (BaerMul G) :=
  inferInstanceAs (Finite G)

@[simp] lemma BaerMul.nat_card_eq {G : Type*} : Nat.card (BaerMul G) = Nat.card G := rfl

/-- **Lem 4.37(c) wrapped**: G の multiplicative automorphism は `BaerMul G` 上でも
multiplicative automorphism (= baerAdd 保存). 関数本体は同じ (恒等経由). -/
noncomputable def MulAut.toBaerMul {G : Type*} [Group G] (f : G ≃* G) :
    BaerMul G ≃* BaerMul G where
  toFun x := BaerMul.ofG (f (BaerMul.toG x))
  invFun x := BaerMul.ofG (f.symm (BaerMul.toG x))
  left_inv x := by
    change BaerMul.ofG (f.symm (BaerMul.toG (BaerMul.ofG (f (BaerMul.toG x))))) = x
    simp only [BaerMul.toG_ofG, f.symm_apply_apply]
    rfl
  right_inv x := by
    change BaerMul.ofG (f (BaerMul.toG (BaerMul.ofG (f.symm (BaerMul.toG x))))) = x
    simp only [BaerMul.toG_ofG, f.apply_symm_apply]
    rfl
  map_mul' x y := by
    change BaerMul.ofG (f (BaerMul.toG (BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG y))))) =
        BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG (f (BaerMul.toG x))))
          (BaerMul.toG (BaerMul.ofG (f (BaerMul.toG y)))))
    simp only [BaerMul.toG_ofG]
    exact congr_arg BaerMul.ofG (baerAdd_mulEquiv_eq f (BaerMul.toG x) (BaerMul.toG y))

/-- `MulAut.toBaerMul` は群準同型 (composition / 1 を保存). 下の `MonoidHom.toBaerMulLift`
を構成するために使う. -/
noncomputable def MulAut.toBaerMulHom {G : Type*} [Group G] :
    MulAut G →* MulAut (BaerMul G) where
  toFun f := MulAut.toBaerMul f
  map_one' := by
    ext x
    change BaerMul.ofG ((1 : MulAut G) (BaerMul.toG x)) = x
    change BaerMul.ofG (BaerMul.toG x) = x
    exact BaerMul.ofG_toG x
  map_mul' f g := by
    ext x
    change BaerMul.ofG ((f * g) (BaerMul.toG x)) =
        BaerMul.ofG (f (BaerMul.toG (BaerMul.ofG (g (BaerMul.toG x)))))
    simp only [BaerMul.toG_ofG]
    rfl

/-- φ : A →* MulAut G を BaerMul G への作用 φ' : A →* MulAut (BaerMul G) に lift する.
関数本体は同じ (Lem 4.37(c)). -/
noncomputable def MonoidHom.toBaerMulLift {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) : A →* MulAut (BaerMul G) :=
  MulAut.toBaerMulHom.comp φ

@[simp] lemma MonoidHom.toBaerMulLift_apply {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) (a : A) (g : BaerMul G) :
    (MonoidHom.toBaerMulLift φ a) g = BaerMul.ofG ((φ a) (BaerMul.toG g)) := rfl

/-- **Lem 4.37(b) full form**: `BaerMul G` の自然冪 (baerAdd-iterate) = `G` の自然冪.
`npow_succ` の帰納で示す. -/
lemma BaerMul.npow_eq_pow {G : Type*} [Group G]
    [Fact (Odd (Nat.card G))] [Fact (_root_.commutator G ≤ Subgroup.center G)]
    (x : BaerMul G) (n : ℕ) :
    @HPow.hPow (BaerMul G) ℕ _ _ x n = BaerMul.ofG ((BaerMul.toG x) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    rfl
  | succ k ih =>
    rw [pow_succ, ih]
    change BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG ((BaerMul.toG x) ^ k))) (BaerMul.toG x)) =
        BaerMul.ofG ((BaerMul.toG x) ^ (k + 1))
    simp only [BaerMul.toG_ofG]
    rw [baerAdd_pow_self_eq_pow_succ]

/-- `BaerMul G` での `x^n = 1` ↔ `G` での `x^n = 1`. Cor 4.35 適用時の `g^p = 1` 翻訳に使用. -/
lemma BaerMul.pow_eq_one_iff {G : Type*} [Group G]
    [Fact (Odd (Nat.card G))] [Fact (_root_.commutator G ≤ Subgroup.center G)]
    (x : BaerMul G) (n : ℕ) :
    @HPow.hPow (BaerMul G) ℕ _ _ x n = 1 ↔ (BaerMul.toG x) ^ n = 1 := by
  rw [BaerMul.npow_eq_pow]
  change BaerMul.ofG ((BaerMul.toG x) ^ n) = BaerMul.ofG 1 ↔ (BaerMul.toG x) ^ n = 1
  exact BaerMul.ofG.apply_eq_iff_eq

/-- `IsPGroup p (BaerMul G) ↔ IsPGroup p G`. BaerMul の構造を経由しても p-群性は不変. -/
lemma BaerMul.isPGroup_iff {G : Type*} [Group G]
    [Fact (Odd (Nat.card G))] [Fact (_root_.commutator G ≤ Subgroup.center G)] (p : ℕ) :
    IsPGroup p (BaerMul G) ↔ IsPGroup p G := by
  unfold IsPGroup
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨n, hn⟩ := h (BaerMul.ofG x)
    refine ⟨n, ?_⟩
    rw [BaerMul.pow_eq_one_iff] at hn
    simpa [BaerMul.toG_ofG] using hn
  · obtain ⟨n, hn⟩ := h (BaerMul.toG x)
    refine ⟨n, ?_⟩
    rw [BaerMul.pow_eq_one_iff]
    exact hn

/-- **系 of Lem 4.28**: `A` が `actionCommutator φ` (= `[G, A]`) 上で trivial 作用するとき,
coprime + (A or G solvable) 仮定下では `actionCommutator φ = ⊥` (= A trivial on whole G).

**証明**: Lem 4.28 で G = C_G(A) · [G, A]. 各 g = c * x で `c ∈ C_G(A)` ⇒ `(φ a) c = c`,
`x ∈ [G, A]` + 仮定 ⇒ `(φ a) x = x`. 故に `(φ a) g = (φ a)(c·x) = c·x = g`.

Thm 4.36 induction の `[G, A] < G` ケースで使用 (IH ⇒ A trivial on [G, A] ⇒ A trivial on G). -/
theorem actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G)
    (h_triv : ∀ a : A, ∀ h ∈ actionCommutator φ, (φ a) h = h) :
    actionCommutator φ = ⊥ := by
  rw [actionCommutator_eq_bot_iff_acts_trivially]
  intro a g
  have h_top : g ∈ Subgroup.fixedPointsOfMulAut φ ⊔ actionCommutator φ := by
    rw [fixedPoints_sup_actionCommutator_eq_top hCop hSolv]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_sup_of_normal_right] at h_top
  obtain ⟨c, hc_fix, x, hx_ac, h_eq⟩ := h_top
  -- h_eq : c * x = g, hc_fix : c ∈ fixedPoints, hx_ac : x ∈ actionCommutator
  rw [← h_eq, map_mul, hc_fix a, h_triv a x hx_ac]

/-- **Isaacs Thm 4.36 (class ≤ 2 case)** ⭐: A acts on p-群 G of class ≤ 2 (p > 2),
A is p'-group, A fixes every order-p element of G ⇒ A trivial on G.

Baer trick で `BaerMul G` を可換群として扱い, Cor 4.35 を適用. これが Thm 4.36 の核.

`hp_odd : p ≠ 2` から `Odd p` → `Odd (p^k)` → `Odd (Nat.card G)`. `hC : class ≤ 2` を
`Fact` 化して `BaerMul.instCommGroup` を呼び出し可能に. -/
theorem actionCommutator_eq_bot_of_pgroup_class_le_two_fixes_order_p
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    (hC : _root_.commutator G ≤ Subgroup.center G)
    (φ : A →* MulAut G) (hG : IsPGroup p G) (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g) :
    actionCommutator φ = ⊥ := by
  -- Set up Fact (Odd (Nat.card G))
  have hOdd_p : Odd p := hp.out.odd_of_ne_two hp_odd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
  have hOdd_card : Odd (Nat.card G) := by rw [hk]; exact hOdd_p.pow
  haveI : Fact (Odd (Nat.card G)) := ⟨hOdd_card⟩
  haveI : Fact (_root_.commutator G ≤ Subgroup.center G) := ⟨hC⟩
  -- φ' : A →* MulAut (BaerMul G)
  set φ' : A →* MulAut (BaerMul G) := MonoidHom.toBaerMulLift φ with hφ'
  -- IsPGroup p (BaerMul G)
  have hG' : IsPGroup p (BaerMul G) := (BaerMul.isPGroup_iff p).mpr hG
  -- h_fix translated to BaerMul G
  have h_fix' : ∀ g : BaerMul G, g ^ p = 1 → ∀ a : A, (φ' a) g = g := by
    intro g hg a
    have hg_G : (BaerMul.toG g) ^ p = 1 := (BaerMul.pow_eq_one_iff g p).mp hg
    have h_fixed : (φ a) (BaerMul.toG g) = BaerMul.toG g := h_fix _ hg_G a
    change BaerMul.ofG ((φ a) (BaerMul.toG g)) = g
    rw [h_fixed]
    exact BaerMul.ofG_toG g
  -- Apply Cor 4.35 to BaerMul G
  have h_bot_baer : actionCommutator φ' = ⊥ :=
    actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p φ' hG' hA_p' h_fix'
  -- Translate back to G via iff
  rw [actionCommutator_eq_bot_iff_acts_trivially] at h_bot_baer
  rw [actionCommutator_eq_bot_iff_acts_trivially]
  intro a g
  have h_act := h_bot_baer a (BaerMul.ofG g)
  -- h_act : (φ' a) (ofG g) = ofG g
  -- Unfold φ': (φ' a) (ofG g) = ofG ((φ a) (toG (ofG g))) = ofG ((φ a) g)
  -- So: ofG ((φ a) g) = ofG g, hence (φ a) g = g by injectivity
  have h_eq : BaerMul.ofG ((φ a) g) = BaerMul.ofG g := by
    have hkey : (φ' a) (BaerMul.ofG g) = BaerMul.ofG ((φ a) g) := by
      change BaerMul.ofG ((φ a) (BaerMul.toG (BaerMul.ofG g))) = BaerMul.ofG ((φ a) g)
      rw [BaerMul.toG_ofG]
    rw [← hkey]
    exact h_act
  exact BaerMul.ofG.injective h_eq

/-- **強帰納法版** (`Nat.card G ≤ n` パラメータ化). Thm 4.36 本体の補助. -/
private theorem isaacs_thm_4_36_aux {A : Type*} [Group A] [Finite A]
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2) (hA_p' : ¬ p ∣ Nat.card A) :
    ∀ n : ℕ, ∀ {G : Type*} [Group G] [Finite G]
    (φ : A →* MulAut G) (_ : IsPGroup p G)
    (_ : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g),
    Nat.card G ≤ n → actionCommutator φ = ⊥ := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ _ _ h_le
    exfalso
    have h_pos : 0 < Nat.card G := Nat.card_pos
    omega
  | succ m IH =>
    intro G _ _ φ hG h_fix h_le
    -- Case: |G| ≤ m, apply IH
    rcases Nat.lt_or_ge (Nat.card G) (m + 1) with h_lt | h_ge
    · exact IH φ hG h_fix (Nat.le_of_lt_succ h_lt)
    have h_card_G : Nat.card G = m + 1 := le_antisymm h_le h_ge
    -- Subcase: G trivial
    by_cases hG_triv : Nontrivial G
    swap
    · haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG_triv
      rw [actionCommutator_eq_bot_iff_acts_trivially]
      intro a g
      exact Subsingleton.elim _ _
    -- G nontrivial setup
    have hCop : Nat.Coprime (Nat.card A) (Nat.card G) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
      rw [hk]
      exact (Nat.Coprime.pow_right k (Nat.coprime_comm.mp
        (Nat.Prime.coprime_iff_not_dvd hp.out |>.mpr hA_p')))
    haveI hG_nilp : Group.IsNilpotent G := hG.isNilpotent
    have hG_solv : IsSolvable G := IsNilpotent.to_isSolvable
    have hSolv : IsSolvable A ∨ IsSolvable G := Or.inr hG_solv
    -- 補助: H ≠ ⊤ + Finite G ⇒ Nat.card ↥H < Nat.card G
    have card_lt_of_ne_top : ∀ {H : Subgroup G}, H ≠ ⊤ → Nat.card ↥H < Nat.card G := by
      intro H h_ne
      have h_dvd : Nat.card ↥H ∣ Nat.card G :=
        ⟨H.index, by rw [mul_comm, H.index_mul_card]⟩
      have h_le' : Nat.card ↥H ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos h_dvd
      have h_ne' : Nat.card ↥H ≠ Nat.card G := fun heq =>
        h_ne (Subgroup.eq_top_of_card_eq _ heq)
      exact Nat.lt_of_le_of_ne h_le' h_ne'
    -- Case分け: [G, A] < ⊤ vs ⊤
    by_cases h_AC_top : actionCommutator φ = ⊤
    swap
    · -- [G, A] < ⊤: IH を actionCommutator に適用
      set H : Subgroup G := actionCommutator φ
      have hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H :=
        OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator φ
      let φ_H : A →* MulAut ↥H :=
        OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH_inv
      have h_H_card_lt : Nat.card ↥H < Nat.card G := card_lt_of_ne_top h_AC_top
      have hH_pgrp : IsPGroup p ↥H := hG.to_subgroup H
      have h_fix_H : ∀ h : ↥H, h ^ p = 1 → ∀ a : A, (φ_H a) h = h := by
        intro h hh_pow a
        apply Subtype.ext
        change (φ a) h.val = h.val
        apply h_fix
        have := congr_arg (Subtype.val : ↥H → G) hh_pow
        simpa using this
      have h_IH_H := IH φ_H hH_pgrp h_fix_H
        (Nat.le_of_lt_succ (h_H_card_lt.trans_le h_le))
      have h_triv : ∀ a : A, ∀ x ∈ H, (φ a) x = x := by
        intro a x hx
        rw [actionCommutator_eq_bot_iff_acts_trivially] at h_IH_H
        have := h_IH_H a ⟨x, hx⟩
        exact congr_arg Subtype.val this
      exact actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime hCop hSolv h_triv
    -- [G, A] = ⊤: G' < ⊤, IH を G' に適用, Three-subgroups で class ≤ 2
    -- G' = commutator G
    set G' : Subgroup G := commutator G with hG'_def
    have hG'_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ G' :=
      OddOrder.Isaacs.Ch03.IsAInvariant.derivedSeries φ 1
    have h_G'_lt_top : G' < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial G
    have h_G'_card_lt : Nat.card ↥G' < Nat.card G := card_lt_of_ne_top h_G'_lt_top.ne
    let φ_G' : A →* MulAut ↥G' :=
      OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hG'_inv
    have hG'_pgrp : IsPGroup p ↥G' := hG.to_subgroup G'
    have h_fix_G' : ∀ g' : ↥G', g' ^ p = 1 → ∀ a : A, (φ_G' a) g' = g' := by
      intro g' hg'_pow a
      apply Subtype.ext
      change (φ a) g'.val = g'.val
      apply h_fix
      have := congr_arg (Subtype.val : ↥G' → G) hg'_pow
      simpa using this
    have h_IH_G' := IH φ_G' hG'_pgrp h_fix_G'
      (Nat.le_of_lt_succ (h_G'_card_lt.trans_le h_le))
    have h_triv_G' : ∀ a : A, ∀ g' ∈ G', (φ a) g' = g' := by
      intro a g' hg'
      rw [actionCommutator_eq_bot_iff_acts_trivially] at h_IH_G'
      have := h_IH_G' a ⟨g', hg'⟩
      exact congr_arg Subtype.val this
    -- Three-subgroups in Γ で G' ⊆ Z(G) を導く
    have h_class_le_2 : commutator G ≤ Subgroup.center G := by
      -- Γ = G ⋊[φ] A. XG = inl(G), YA = inr(A), XG' = inl(G').
      set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
      set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
      set XG' : Subgroup (G ⋊[φ] A) := G'.map (SemidirectProduct.inl : G →* G ⋊[φ] A)
      -- Step 1: ⁅XG', YA⁆ = ⊥ (h_triv_G' + generator computation)
      have h_G'_YA : ⁅XG', YA⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        rintro _ ⟨k, hk, rfl⟩ _ ⟨a, rfl⟩
        rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
        have h_fix' : (φ a) k = k := h_triv_G' a k hk
        rw [show (φ a) k⁻¹ = ((φ a) k)⁻¹ from map_inv (φ a) k, h_fix', mul_inv_cancel]
        exact map_one _
      -- Step 2: ⁅XG, XG'⁆ ≤ XG' (G' normal in G ⇒ inl の像でも保たれる)
      have h_GG'_le : ⁅XG, XG'⁆ ≤ XG' := by
        rw [Subgroup.commutator_le]
        rintro _ ⟨g, rfl⟩ _ ⟨k, hk, rfl⟩
        -- Goal: ⁅inl g, inl k⁆ ∈ XG' (= inl(G'))
        rw [show (⁅(SemidirectProduct.inl g : G ⋊[φ] A), SemidirectProduct.inl k⁆ :
            G ⋊[φ] A) = SemidirectProduct.inl ⁅g, k⁆ from by
          simp [commutatorElement_def, ← map_mul, ← map_inv]]
        refine ⟨⁅g, k⁆, ?_, rfl⟩
        -- Since G' is normal, both `g * k * g⁻¹` and `k⁻¹` lie in G'.
        have hG'_normal : G'.Normal := inferInstance
        have h_gkg : g * k * g⁻¹ ∈ G' := hG'_normal.conj_mem k hk g
        have h_inv : k⁻¹ ∈ G' := G'.inv_mem hk
        rw [commutatorElement_def]
        exact G'.mul_mem h_gkg h_inv
      -- h12: ⁅⁅XG, XG'⁆, YA⁆ ⊆ ⁅XG', YA⁆ = ⊥
      have h12 : ⁅⁅XG, XG'⁆, YA⁆ = ⊥ := by
        rw [eq_bot_iff]
        calc ⁅⁅XG, XG'⁆, YA⁆ ≤ ⁅XG', YA⁆ := Subgroup.commutator_mono h_GG'_le le_rfl
          _ = ⊥ := h_G'_YA
      -- h23: ⁅⁅XG', YA⁆, XG⁆ = ⁅⊥, XG⁆ = ⊥
      have h23 : ⁅⁅XG', YA⁆, XG⁆ = ⊥ := by
        rw [h_G'_YA]
        exact Subgroup.commutator_bot_left XG
      -- Three-subgroups: ⁅⁅YA, XG⁆, XG'⁆ = ⊥
      have h_three : ⁅⁅YA, XG⁆, XG'⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate h12 h23
      -- ⁅YA, XG⁆ = ⁅XG, YA⁆ = XG (since actionCommutator = ⊤)
      have h_XGYA_eq_XG : ⁅XG, YA⁆ = XG := by
        rw [← actionCommutator_map_inl φ, h_AC_top]
        exact (MonoidHom.range_eq_map _).symm
      have h_YAXG_eq_XG : ⁅YA, XG⁆ = XG := by
        rw [Subgroup.commutator_comm]; exact h_XGYA_eq_XG
      -- So ⁅XG, XG'⁆ = ⊥ in Γ
      have h_XG_XG'_bot : ⁅XG, XG'⁆ = ⊥ := h_YAXG_eq_XG ▸ h_three
      -- Translate back to G: ⁅⊤, G'⁆ = ⊥ ⇒ G' ⊆ Z(G)
      -- inl(⁅⊤, G'⁆) = ⁅inl(⊤), inl(G')⁆ = ⁅XG, XG'⁆ = ⊥, so ⁅⊤, G'⁆ = ⊥ by inl injective
      have h_top_G'_bot : ⁅(⊤ : Subgroup G), G'⁆ = ⊥ := by
        apply Subgroup.map_injective (f := (SemidirectProduct.inl : G →* G ⋊[φ] A))
          SemidirectProduct.inl_injective
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.map_bot]
        exact h_XG_XG'_bot
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h_top_G'_bot
      -- h_top_G'_bot : ⊤ ≤ G'.centralizer
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have := h_top_G'_bot (Subgroup.mem_top y)
      exact (this x hx).symm
    -- Apply class ≤ 2 case
    exact actionCommutator_eq_bot_of_pgroup_class_le_two_fixes_order_p
      hp_odd h_class_le_2 φ hG hA_p' h_fix

/-- **Isaacs Theorem 4.36** ⭐ (= BG Thm 1.11, **FT クリティカル**):
`p > 2`, `G` p-群, `A` p'-群 が `G` に作用. `A` が `G` の全 order-p 要素を fix するならば,
`A` は `G` 上 trivial に作用する (`actionCommutator φ = ⊥`).

**証明** (Isaacs p.142): 強帰納法 on `|G|`.
- 自明 G: 即座.
- `[G, A] < G`: IH を `actionCommutator` に適用 ⇒ A trivial on [G, A] ⇒ Lem 4.28 系で結論.
- `[G, A] = G`: `G' < G` (G nontrivial nilpotent solvable). IH を G' に適用 ⇒ A trivial on G'.
  Three-subgroups in Γ = G ⋊ A ([G', A] = 1, [G, G'] ⊆ G' から) ⇒ `[G, G'] = 1` ⇒ G' ⊆ Z(G)
  ⇒ class ≤ 2. Baer trick + Cor 4.35 (class ≤ 2 case) で結論.

下流: BG §1 Thm 1.11 (BG Cor 1.12 等), Ch.5 Cor 5.30 経由 normal p-complement (5.26). -/
theorem isaacs_thm_4_36 {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    (φ : A →* MulAut G) (hG : IsPGroup p G) (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g) :
    actionCommutator φ = ⊥ :=
  isaacs_thm_4_36_aux hp_odd hA_p' (Nat.card G) φ hG h_fix le_rfl

/-- **Isaacs Lemma 4.32 (後半)** ⭐: `P` p-群 が `G` 非自明 p-群 に作用 ⇒
`C_G(P)` (= fixed point subgroup) は非自明.

**proof**: `MulAction P G` を `φ` 経由で setup. `card_modEq_card_fixedPoints` で
`|G| ≡ |fixedPoints| mod p`. G 非自明 p-群より `p ∣ |G|`. 1 は trivial fixed point.
`exists_fixed_point_of_prime_dvd_card_of_fixed_point` で `1` と異なる fixed point 存在. -/
theorem fixedPoints_ne_bot_of_pgroup_action_pgroup
    {G P : Type*} [Group G] [Group P] [Finite G] [Finite P] [Nontrivial G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (hP : IsPGroup p P)
    (φ : P →* MulAut G) :
    Subgroup.fixedPointsOfMulAut φ ≠ ⊥ := by
  letI : MulAction P G := MulAction.compHom G φ
  -- 1 ∈ fixedPoints (φ p is a group hom, so (φ p) 1 = 1)
  have h1_fix : (1 : G) ∈ MulAction.fixedPoints P G := fun p => by
    change (φ p) 1 = 1
    exact map_one (φ p)
  -- p ∣ |G| since G is a nontrivial p-group
  obtain ⟨n, hn_pos, hn_card⟩ := hG.nontrivial_iff_card.mp inferInstance
  have hp_dvd : p ∣ Nat.card G := by
    rw [hn_card]; exact dvd_pow_self p hn_pos.ne'
  -- ∃ b ∈ fixedPoints, b ≠ 1
  obtain ⟨b, hb_fix, hb_ne⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := G) hp_dvd h1_fix
  -- b ∈ Subgroup.fixedPointsOfMulAut φ via the same definition
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨b, ?_⟩, ?_⟩
  · exact fun p => hb_fix p
  · intro h
    apply hb_ne
    exact (Subtype.ext_iff.mp h).symm

/-- **Isaacs Lemma 4.32 (前半)**: `P` p-群 が `G` 非自明 p-群 に作用 ⇒
`Γ = G ⋊[φ] P` 内で `⁅inl(G), inr(P)⁆ < inl(G)` (strict).

**proof**: Γ = G ⋊ P は p-群 (`IsPGroup.semidirectProduct`) で nilpotent. `inl(G)` は
normal (`SemidirectProduct.inl_range_normal`) かつ G 非自明より ≠ ⊥.
`commutator_lt_self_of_isNilpotent_ambient` を適用.

Isaacs 流の `⁅G, P⁆ < G` (G の中で見た [G, P]) と等価 (inl を介して identify).

C_G(P) > 1 (Lem 4.32 後半) は Γ の center > 1 経由で別途. -/
theorem commutator_inl_inr_lt_inl_of_pgroup_action
    {G P : Type*} [Group G] [Group P] [Finite G] [Finite P] [Nontrivial G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (hP : IsPGroup p P)
    (φ : P →* MulAut G) :
    ⁅(SemidirectProduct.inl : G →* G ⋊[φ] P).range,
      (SemidirectProduct.inr : P →* G ⋊[φ] P).range⁆ <
        (SemidirectProduct.inl : G →* G ⋊[φ] P).range := by
  haveI : Group.IsNilpotent (G ⋊[φ] P) :=
    Group.IsNilpotent.semidirectProduct_of_pGroup hG hP
  haveI : (SemidirectProduct.inl : G →* G ⋊[φ] P).range.Normal :=
    OddOrder.Isaacs.Ch03.inl_range_normal φ
  apply commutator_lt_self_of_isNilpotent_ambient
  -- inl.range ≠ ⊥: inl injective + G nontrivial
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  refine ⟨⟨SemidirectProduct.inl g, g, rfl⟩, ?_⟩
  intro h
  apply hg
  have : SemidirectProduct.inl g = (1 : G ⋊[φ] P) := Subtype.ext_iff.mp h
  exact SemidirectProduct.inl_injective this

/-- The left factor inclusion `P →* P × Q`. -/
def prodLeftHom (P Q : Type*) [Group P] [Group Q] : P →* P × Q where
  toFun p := (p, 1)
  map_one' := rfl
  map_mul' _ _ := by
    ext <;> simp

@[simp]
theorem prodLeftHom_apply {P Q : Type*} [Group P] [Group Q] (p : P) :
    prodLeftHom P Q p = (p, 1) :=
  by simp [prodLeftHom]

/-- The right factor inclusion `Q →* P × Q`. -/
def prodRightHom (P Q : Type*) [Group P] [Group Q] : Q →* P × Q where
  toFun q := (1, q)
  map_one' := rfl
  map_mul' _ _ := by
    ext <;> simp

@[simp]
theorem prodRightHom_apply {P Q : Type*} [Group P] [Group Q] (q : Q) :
    prodRightHom P Q q = (1, q) :=
  by simp [prodRightHom]

/-- In an external direct-product action, `[G, P]` is invariant under the whole
`P × Q` action. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator_prodLeft
    {G P Q : Type*} [Group G] [Group P] [Group Q] (φ : P × Q →* MulAut G) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutator (φ.comp (prodLeftHom P Q))) := by
  apply OddOrder.Isaacs.Ch03.IsAInvariant.closure_of_invariant_set
  intro b
  have key : ∀ g : G, ∀ p : P,
      (φ b) (g * (φ (prodLeftHom P Q p)) g⁻¹) =
        (φ b) g * (φ (prodLeftHom P Q (b.1 * p * b.1⁻¹))) ((φ b) g)⁻¹ := by
    intro g p
    rw [map_mul (φ b)]
    congr 1
    rw [show ((φ b) g)⁻¹ = (φ b) g⁻¹ from (map_inv (φ b) g).symm,
        show φ (prodLeftHom P Q (b.1 * p * b.1⁻¹)) =
            (φ b) * (φ (prodLeftHom P Q p)) * (φ b)⁻¹ from by
          rw [show prodLeftHom P Q (b.1 * p * b.1⁻¹) =
              b * prodLeftHom P Q p * b⁻¹ from by
            ext <;> simp [prodLeftHom, mul_assoc]]
          rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨g, p, rfl⟩, rfl⟩
    exact ⟨(φ b) g, b.1 * p * b.1⁻¹, by simpa using key g p⟩
  · rintro ⟨g, p, hx⟩
    have hx' : x = g * (φ (prodLeftHom P Q p)) g⁻¹ := by simpa using hx
    rw [hx']
    refine ⟨(φ b)⁻¹ g * (φ (prodLeftHom P Q (b.1⁻¹ * p * b.1))) ((φ b)⁻¹ g)⁻¹,
      ⟨(φ b)⁻¹ g, b.1⁻¹ * p * b.1, by simp⟩, ?_⟩
    rw [map_mul (φ b)]
    congr 1
    · exact MulAut.apply_inv_self (M := G) (φ b) g
    rw [show ((φ b)⁻¹ g)⁻¹ = (φ b)⁻¹ g⁻¹ from (map_inv ((φ b)⁻¹) g).symm,
        show φ (prodLeftHom P Q (b.1⁻¹ * p * b.1)) =
            (φ b)⁻¹ * (φ (prodLeftHom P Q p)) * (φ b) from by
          rw [show prodLeftHom P Q (b.1⁻¹ * p * b.1) =
              b⁻¹ * prodLeftHom P Q p * b from by
            ext <;> simp [prodLeftHom, mul_assoc]]
          rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.apply_inv_self]

/-- If `Q ⊴ A`, then `[G,Q]` is invariant under the whole `A`-action. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator_of_normal
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G)
    (Q : Subgroup A) [Q.Normal] :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutator (φ.comp Q.subtype)) := by
  apply OddOrder.Isaacs.Ch03.IsAInvariant.closure_of_invariant_set
  intro b
  have key : ∀ g : G, ∀ q : Q,
      (φ b) (g * (φ q.val) g⁻¹) =
        (φ b) g * (φ (b * q.val * b⁻¹)) ((φ b) g)⁻¹ := by
    intro g q
    rw [map_mul (φ b)]
    congr 1
    rw [show ((φ b) g)⁻¹ = (φ b) g⁻¹ from (map_inv (φ b) g).symm,
        show φ (b * q.val * b⁻¹) = (φ b) * (φ q.val) * (φ b)⁻¹ from by
          rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨g, q, rfl⟩, rfl⟩
    have hbqb : b * q.val * b⁻¹ ∈ Q :=
      (inferInstance : Q.Normal).conj_mem q.val q.property b
    exact ⟨(φ b) g, ⟨b * q.val * b⁻¹, hbqb⟩, by simp⟩
  · rintro ⟨g, q, hx⟩
    have hx' : x = g * (φ q.val) g⁻¹ := by simpa using hx
    rw [hx']
    have hbqb : b⁻¹ * q.val * b ∈ Q := by
      simpa using (inferInstance : Q.Normal).conj_mem q.val q.property b⁻¹
    refine ⟨(φ b)⁻¹ g * (φ (b⁻¹ * q.val * b)) ((φ b)⁻¹ g)⁻¹,
      ⟨(φ b)⁻¹ g, ⟨b⁻¹ * q.val * b, hbqb⟩, by simp⟩, ?_⟩
    rw [map_mul (φ b)]
    congr 1
    · exact MulAut.apply_inv_self (M := G) (φ b) g
    rw [show ((φ b)⁻¹ g)⁻¹ = (φ b)⁻¹ g⁻¹ from (map_inv ((φ b)⁻¹) g).symm,
        show φ (b⁻¹ * q.val * b) = (φ b)⁻¹ * (φ q.val) * (φ b) from by
          rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.apply_inv_self]

/-- Abelian case of Isaacs Theorem 4.38.

Let `P,Q ≤ A`, with `P` a p-group and `Q` normal p'. If every `P`-fixed
point of the abelian p-group `G` is also `Q`-fixed, then `[G,Q]=1`. -/
theorem actionCommutator_eq_bot_of_abelian_pgroup_of_subgroup_fixedPoints
    {A G : Type*} [Group A] [CommGroup G] [Finite A] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (φ : A →* MulAut G) (hG : IsPGroup p G)
    (P Q : Subgroup A) [Q.Normal] (hP : IsPGroup p P) (hQ_p' : ¬ p ∣ Nat.card Q)
    (h_fix : ∀ g : G, (∀ x : P, (φ x.val) g = g) → ∀ y : Q, (φ y.val) g = g) :
    actionCommutator (φ.comp Q.subtype) = ⊥ := by
  let φQ : Q →* MulAut G := φ.comp Q.subtype
  have hCop : Nat.Coprime (Nat.card Q) (Nat.card G) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
    rw [hn]
    exact (Nat.Coprime.pow_right n
      (Nat.coprime_comm.mp (Nat.Prime.coprime_iff_not_dvd hp.out |>.mpr hQ_p')))
  have h_inf_bot := fixedPoints_inf_actionCommutator_eq_bot_of_abelian φQ hCop
  by_contra h_ne_bot
  have h_ne_bot' : actionCommutator φQ ≠ ⊥ := by
    simpa [φQ] using h_ne_bot
  haveI hH_pgrp : IsPGroup p (actionCommutator φQ) := hG.to_subgroup _
  haveI : Nontrivial (actionCommutator φQ) := by
    rw [Subgroup.ne_bot_iff_exists_ne_one] at h_ne_bot'
    obtain ⟨h, hh_ne⟩ := h_ne_bot'
    exact ⟨h, 1, hh_ne⟩
  have hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutator φQ) := by
    simpa [φQ] using OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator_of_normal φ Q
  let φH : A →* MulAut (actionCommutator φQ) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH_inv
  let φP_H : P →* MulAut (actionCommutator φQ) := φH.comp P.subtype
  have hP_fixed_ne :=
    fixedPoints_ne_bot_of_pgroup_action_pgroup hH_pgrp hP φP_H
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hP_fixed_ne
  obtain ⟨h, hh_ne⟩ := hP_fixed_ne
  have hP_fix_G : ∀ x : P, (φ x.val) h.1.val = h.1.val := by
    intro x
    have hx := congr_arg (Subtype.val : actionCommutator φQ → G) (h.property x)
    simpa [φP_H, φH] using hx
  have hQ_fix_G : ∀ y : Q, (φ y.val) h.1.val = h.1.val :=
    h_fix h.1.val hP_fix_G
  have h_mem_inf : h.1.val ∈ Subgroup.fixedPointsOfMulAut φQ ⊓ actionCommutator φQ :=
    Subgroup.mem_inf.mpr ⟨hQ_fix_G, h.1.property⟩
  have h_val_one : h.1.val = 1 := by
    rw [h_inf_bot, Subgroup.mem_bot] at h_mem_inf
    exact h_mem_inf
  apply hh_ne
  apply Subtype.ext
  apply Subtype.ext
  exact h_val_one

/-- Three-subgroups step for Isaacs Theorem 4.31 in external direct-product form.

Let `P × Q` act on `G`. If the `Q`-factor acts trivially on `[G, P]`, then
the `P`-factor acts trivially on `[G, Q]`. This is the semidirect-product
calculation corresponding to `[G,P,Q]=1` and `[P,Q,G]=1`, hence `[Q,G,P]=1`. -/
theorem prodLeft_fixes_actionCommutator_prodRight_of_prodRight_fixes_actionCommutator_prodLeft
    {G P Q : Type*} [Group G] [Group P] [Group Q] (φ : P × Q →* MulAut G)
    (hQ_on_GP : ∀ q : Q, ∀ h ∈ actionCommutator (φ.comp (prodLeftHom P Q)),
      (φ (1, q)) h = h) :
    ∀ p : P, ∀ h ∈ actionCommutator (φ.comp (prodRightHom P Q)),
      (φ (p, 1)) h = h := by
  let iP : P →* P × Q := prodLeftHom P Q
  let iQ : Q →* P × Q := prodRightHom P Q
  set XG : Subgroup (G ⋊[φ] (P × Q)) :=
    (SemidirectProduct.inl : G →* G ⋊[φ] (P × Q)).range
  set YP : Subgroup (G ⋊[φ] (P × Q)) :=
    ((SemidirectProduct.inr : P × Q →* G ⋊[φ] (P × Q)).comp iP).range
  set YQ : Subgroup (G ⋊[φ] (P × Q)) :=
    ((SemidirectProduct.inr : P × Q →* G ⋊[φ] (P × Q)).comp iQ).range
  have h_GP_eq : (actionCommutator (φ.comp iP)).map
      (SemidirectProduct.inl : G →* G ⋊[φ] (P × Q)) = ⁅XG, YP⁆ := by
    simpa [XG, YP, iP] using actionCommutator_map_inl_comp φ iP
  have h_GQ_eq : (actionCommutator (φ.comp iQ)).map
      (SemidirectProduct.inl : G →* G ⋊[φ] (P × Q)) = ⁅XG, YQ⁆ := by
    simpa [XG, YQ, iQ] using actionCommutator_map_inl_comp φ iQ
  have h_GPYQ : ⁅⁅XG, YP⁆, YQ⁆ = ⊥ := by
    rw [← h_GP_eq, eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨k, hk, rfl⟩ _ ⟨q, rfl⟩
    change ⁅(SemidirectProduct.inl k : G ⋊[φ] (P × Q)),
      SemidirectProduct.inr (iQ q)⁆ ∈ (⊥ : Subgroup (G ⋊[φ] (P × Q)))
    rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
    have h_fix : (φ (iQ q)) k = k := by
      simpa [iQ] using hQ_on_GP q k hk
    rw [show (φ (iQ q)) k⁻¹ = ((φ (iQ q)) k)⁻¹ from map_inv (φ (iQ q)) k,
      h_fix, mul_inv_cancel]
    exact map_one _
  have h_PQ : ⁅YP, YQ⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    change ⁅(SemidirectProduct.inr (iP p) : G ⋊[φ] (P × Q)),
      SemidirectProduct.inr (iQ q)⁆ ∈ (⊥ : Subgroup (G ⋊[φ] (P × Q)))
    rw [Subgroup.mem_bot]
    ext <;> simp [commutatorElement_def, iP, iQ]
  have h_PQXG : ⁅⁅YP, YQ⁆, XG⁆ = ⊥ := by
    rw [h_PQ]
    exact Subgroup.commutator_bot_left XG
  have h_three : ⁅⁅YQ, XG⁆, YP⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h_GPYQ h_PQXG
  have h_GQYP : ⁅⁅XG, YQ⁆, YP⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm YQ XG] at h_three
  intro p h hh
  have h_in_GQ : (SemidirectProduct.inl h : G ⋊[φ] (P × Q)) ∈ ⁅XG, YQ⁆ := by
    rw [← h_GQ_eq]
    exact ⟨h, hh, rfl⟩
  have h_comm_mem : ⁅(SemidirectProduct.inl h : G ⋊[φ] (P × Q)),
      SemidirectProduct.inr (iP p)⁆ ∈ ⁅⁅XG, YQ⁆, YP⁆ :=
    Subgroup.commutator_mem_commutator h_in_GQ ⟨p, rfl⟩
  have h_comm_bot : ⁅(SemidirectProduct.inl h : G ⋊[φ] (P × Q)),
      SemidirectProduct.inr (iP p)⁆ ∈ (⊥ : Subgroup (G ⋊[φ] (P × Q))) := by
    rw [← h_GQYP]
    exact h_comm_mem
  rw [Subgroup.mem_bot, SemidirectProduct.commutator_inl_inr] at h_comm_bot
  have h_mul : h * (φ (iP p)) h⁻¹ = 1 :=
    SemidirectProduct.inl_injective (by simpa using h_comm_bot)
  rw [show (φ (iP p)) h⁻¹ = ((φ (iP p)) h)⁻¹ from map_inv (φ (iP p)) h] at h_mul
  rw [mul_inv_eq_one] at h_mul
  simpa [iP] using h_mul.symm

/-- Final coprime-action step for Isaacs Theorem 4.31 in external direct-product form.

If `Q` is a `p'`-group acting on the `p`-group `G`, `Q` acts trivially on
`[G,P]`, and every `P`-fixed element of `G` is `Q`-fixed, then `[G,Q] = 1`.
Together with induction providing the first hypothesis, this is the last
paragraph of Isaacs Thm 4.31. -/
theorem actionCommutator_prodRight_eq_bot_of_prodRight_fixes_actionCommutator_prodLeft
    {G P Q : Type*} [Group G] [Group P] [Group Q] [Finite G] [Finite Q]
    {p : ℕ} [hp : Fact p.Prime] (φ : P × Q →* MulAut G)
    (hG : IsPGroup p G) (hQ_p' : ¬ p ∣ Nat.card Q)
    (hQ_on_GP : ∀ q : Q, ∀ h ∈ actionCommutator (φ.comp (prodLeftHom P Q)),
      (φ (1, q)) h = h)
    (h_fix : ∀ g : G, (∀ x : P, (φ (x, 1)) g = g) → ∀ y : Q, (φ (1, y)) g = g) :
    actionCommutator (φ.comp (prodRightHom P Q)) = ⊥ := by
  let φQ : Q →* MulAut G := φ.comp (prodRightHom P Q)
  have hP_on_GQ :
      ∀ x : P, ∀ h ∈ actionCommutator (φ.comp (prodRightHom P Q)),
        (φ (x, 1)) h = h :=
    prodLeft_fixes_actionCommutator_prodRight_of_prodRight_fixes_actionCommutator_prodLeft
      φ hQ_on_GP
  have h_triv : ∀ q : Q, ∀ h ∈ actionCommutator φQ, (φQ q) h = h := by
    intro q h hh
    have hP_fix : ∀ x : P, (φ (x, 1)) h = h := by
      intro x
      exact hP_on_GQ x h (by simpa [φQ] using hh)
    simpa [φQ] using h_fix h hP_fix q
  have hCop : Nat.Coprime (Nat.card Q) (Nat.card G) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
    rw [hk]
    exact (((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hQ_p').symm).pow_right k
  haveI : Group.IsNilpotent G := hG.isNilpotent
  have hSolv : IsSolvable Q ∨ IsSolvable G := Or.inr IsNilpotent.to_isSolvable
  exact actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime
    (A := Q) (G := G) (φ := φQ) hCop hSolv h_triv

/-- Finite subgroup card strictly drops for a proper subgroup. -/
theorem subgroup_card_lt_of_ne_top {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hH : H ≠ ⊤) :
    Nat.card H < Nat.card G := by
  have h_dvd : Nat.card H ∣ Nat.card G :=
    ⟨H.index, by rw [mul_comm, H.index_mul_card]⟩
  have h_le : Nat.card H ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos h_dvd
  have h_ne : Nat.card H ≠ Nat.card G := fun heq =>
    hH (Subgroup.eq_top_of_card_eq _ heq)
  exact Nat.lt_of_le_of_ne h_le h_ne

/-- Strong-induction form of Isaacs Theorem 4.31 for external direct products. -/
private theorem isaacs_thm_4_31_external_aux
    {P Q : Type*} [Group P] [Group Q] [Finite P] [Finite Q]
    {p : ℕ} [hp : Fact p.Prime] (hP : IsPGroup p P) (hQ_p' : ¬ p ∣ Nat.card Q) :
    ∀ n : ℕ, ∀ {G : Type*} [Group G] [Finite G]
    (φ : P × Q →* MulAut G) (_ : IsPGroup p G)
    (_ : ∀ g : G, (∀ x : P, (φ (x, 1)) g = g) → ∀ y : Q, (φ (1, y)) g = g),
    Nat.card G ≤ n → actionCommutator (φ.comp (prodRightHom P Q)) = ⊥ := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ _ _ h_le
    exfalso
    have h_pos : 0 < Nat.card G := Nat.card_pos
    omega
  | succ m IH =>
    intro G _ _ φ hG h_fix h_le
    rcases Nat.lt_or_ge (Nat.card G) (m + 1) with h_lt | h_ge
    · exact IH φ hG h_fix (Nat.le_of_lt_succ h_lt)
    have h_card_G : Nat.card G = m + 1 := le_antisymm h_le h_ge
    by_cases hG_nontriv : Nontrivial G
    swap
    · haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG_nontriv
      rw [actionCommutator_eq_bot_iff_acts_trivially]
      intro q g
      exact Subsingleton.elim _ _
    letI : Nontrivial G := hG_nontriv
    let φP : P →* MulAut G := φ.comp (prodLeftHom P Q)
    set H : Subgroup G := actionCommutator φP with hH_def
    have h_lt_comm : ⁅(SemidirectProduct.inl : G →* G ⋊[φP] P).range,
        (SemidirectProduct.inr : P →* G ⋊[φP] P).range⁆ <
          (SemidirectProduct.inl : G →* G ⋊[φP] P).range :=
      commutator_inl_inr_lt_inl_of_pgroup_action hG hP φP
    have hH_ne_top : H ≠ ⊤ := by
      intro htop
      have hmap : H.map (SemidirectProduct.inl : G →* G ⋊[φP] P) =
          (SemidirectProduct.inl : G →* G ⋊[φP] P).range := by
        rw [htop]
        exact (MonoidHom.range_eq_map _).symm
      rw [hH_def, actionCommutator_map_inl] at hmap
      exact h_lt_comm.ne hmap
    have hH_card_lt : Nat.card H < Nat.card G := subgroup_card_lt_of_ne_top hH_ne_top
    have hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H := by
      rw [hH_def]
      simpa [φP] using OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator_prodLeft φ
    let φH : P × Q →* MulAut H :=
      OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH_inv
    have hH_pgrp : IsPGroup p H := hG.to_subgroup H
    have h_fix_H :
        ∀ h : H, (∀ x : P, (φH (x, 1)) h = h) → ∀ y : Q, (φH (1, y)) h = h := by
      intro h hP_fix y
      apply Subtype.ext
      have hP_fix_val : ∀ x : P, (φ (x, 1)) h.val = h.val := by
        intro x
        have hx := congr_arg (Subtype.val : H → G) (hP_fix x)
        simpa [φH] using hx
      have hQ_fix := h_fix h.val hP_fix_val y
      simpa [φH] using hQ_fix
    have hIH_H := IH φH hH_pgrp h_fix_H
      (Nat.le_of_lt_succ (hH_card_lt.trans_le h_le))
    have hQ_on_GP :
        ∀ q : Q, ∀ h ∈ actionCommutator (φ.comp (prodLeftHom P Q)), (φ (1, q)) h = h := by
      intro q h hh
      rw [actionCommutator_eq_bot_iff_acts_trivially] at hIH_H
      have h_in_H : h ∈ H := by
        simpa [H, φP] using hh
      have hact := congr_arg (Subtype.val : H → G) (hIH_H q ⟨h, h_in_H⟩)
      simpa [φH] using hact
    exact actionCommutator_prodRight_eq_bot_of_prodRight_fixes_actionCommutator_prodLeft
      φ hG hQ_p' hQ_on_GP h_fix

/-- **Isaacs Theorem 4.31** (external direct-product form).

Let `P × Q` act on the `p`-group `G`, with `P` a `p`-group and `Q` a
`p'`-group. If every element of `G` fixed by the `P`-factor is fixed by the
`Q`-factor, then the `Q`-factor acts trivially on `G`. -/
theorem isaacs_thm_4_31_external
    {G P Q : Type*} [Group G] [Group P] [Group Q] [Finite G] [Finite P] [Finite Q]
    {p : ℕ} [Fact p.Prime] (φ : P × Q →* MulAut G)
    (hG : IsPGroup p G) (hP : IsPGroup p P) (hQ_p' : ¬ p ∣ Nat.card Q)
    (h_fix : ∀ g : G, (∀ x : P, (φ (x, 1)) g = g) → ∀ y : Q, (φ (1, y)) g = g) :
    actionCommutator (φ.comp (prodRightHom P Q)) = ⊥ :=
  isaacs_thm_4_31_external_aux hP hQ_p' (Nat.card G) φ hG h_fix le_rfl

/-- First step toward **Isaacs Theorem 4.33**: if `Q = O_{p'}(N_G(P))`, then `Q`
centralizes the ambient `p`-core `O_p(G)`.

The proof is the 4.33 argument up to the Hall-Higman step.  Let `H = N_G(P)`,
`U = O_p(G)`, and `Q = O_{p'}(H)`.  Since `P ⊴ H` and `Q ⊴ H` have coprime
types, they commute, so `P × Q` acts on `U` by conjugation.  If `u ∈ U` is
fixed by `P`, then `u ∈ C_G(P) ≤ H`; hence `u ∈ U.subgroupOf H`, a normal
`p`-subgroup of `H`, and therefore `Q` fixes `u`.  Isaacs 4.31 then makes
the `Q`-action on `U` trivial. -/
theorem oPiCore_compl_normalizer_le_centralizer_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : IsPGroup p P) :
    (OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)}
        (Subgroup.normalizer (P : Set G))).map
        (Subgroup.normalizer (P : Set G)).subtype ≤
      Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) := by
  classical
  set H : Subgroup G := Subgroup.normalizer (P : Set G) with hH_def
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set PH : Subgroup H := P.subgroupOf H with hPH_def
  set Q : Subgroup H :=
    OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} H with hQ_def
  change Q.map H.subtype ≤ Subgroup.centralizer (U : Set G)
  have hP_le_H : P ≤ H := by
    rw [hH_def]
    exact Subgroup.le_normalizer
  haveI hPH_normal : PH.Normal := by
    rw [hPH_def, hH_def]
    exact Subgroup.normal_in_normalizer
  haveI hQ_normal : Q.Normal := by
    rw [hQ_def]
    infer_instance
  haveI hU_normal : U.Normal := by
    rw [hU_def]
    infer_instance
  have hPH_p : IsPGroup p PH := by
    rw [hPH_def]
    exact hP.of_equiv (Subgroup.subgroupOfEquivOfLe hP_le_H).symm
  have hQ_pi :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} Q := by
    rw [hQ_def]
    exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup {q | q ∉ ({p} : Set ℕ)}
  have hQ_p' : ¬ p ∣ Nat.card Q := by
    intro hp_dvd
    have hp_pf : p ∈ (Nat.card Q).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Fact.out, hp_dvd, Nat.card_pos.ne'⟩
    exact hQ_pi p hp_pf (by simp)
  have hPH_Q_comm : ∀ x y : H, x ∈ PH → y ∈ Q → Commute x y :=
    commute_of_normal_isPGroup_of_normal_isPiCompl hPH_p hQ_pi
  let pqMul : PH × Q →* H := {
    toFun z := z.1.val * z.2.val
    map_one' := by ext; simp
    map_mul' := by
      intro a b
      ext
      simp only [Prod.mul_def]
      change (((a.1.val * b.1.val) * (a.2.val * b.2.val) : H) : G) =
        (((a.1.val * a.2.val) * (b.1.val * b.2.val) : H) : G)
      have hc : Commute (a.2.val : H) (b.1.val : H) :=
        (hPH_Q_comm b.1.val a.2.val b.1.property a.2.property).symm
      rw [mul_assoc, ← mul_assoc b.1.val a.2.val b.2.val, ← hc.eq]
      group }
  let ψ : PH × Q →* G := H.subtype.comp pqMul
  let φ : PH × Q →* MulAut U := (MulAut.conjNormal : G →* MulAut U).comp ψ
  have hU_p : IsPGroup p U := by
    rw [hU_def]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  have hfix :
      ∀ u : U, (∀ x : PH, (φ (x, 1)) u = u) → ∀ y : Q, (φ (1, y)) u = u := by
    intro u hu y
    have hu_cent : (u : G) ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hxP
      have hfixed_x :=
        congr_arg (Subtype.val : U → G)
          (hu ⟨⟨x, hP_le_H hxP⟩, by simpa [PH, Subgroup.mem_subgroupOf] using hxP⟩)
      have hxconj : x * (u : G) * x⁻¹ = (u : G) := by
        simpa [φ, ψ, pqMul, MulAut.conjNormal_apply] using hfixed_x
      calc
        x * (u : G) = (x * (u : G) * x⁻¹) * x := by group
        _ = (u : G) * x := by rw [hxconj]
    have huH : (u : G) ∈ H := by
      rw [hH_def]
      exact centralizer_le_normalizer_subgroup P hu_cent
    let uH : H := ⟨u, huH⟩
    set UH : Subgroup H := U.subgroupOf H with hUH_def
    haveI hUH_normal : UH.Normal := by
      rw [hUH_def]
      exact (show U.Normal from inferInstance).subgroupOf H
    let incUH_U : UH →* U := {
      toFun x := ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hUH_p : IsPGroup p UH :=
      hU_p.of_injective incUH_U (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congr_arg (Subtype.val : U → G) hab)
    have hu_UH : uH ∈ UH := by
      rw [hUH_def]
      change (u : G) ∈ U
      exact u.property
    have hUH_Q_comm : ∀ x y : H, x ∈ UH → y ∈ Q → Commute x y :=
      commute_of_normal_isPGroup_of_normal_isPiCompl hUH_p hQ_pi
    have hcomm_u_y : Commute uH y.val :=
      hUH_Q_comm uH y.val hu_UH y.property
    apply Subtype.ext
    have hyconj_H : (y.val : H) * uH * (y.val : H)⁻¹ = uH := by
      have hyu : (y.val : H) * uH = uH * y.val := hcomm_u_y.symm.eq
      calc
        (y.val : H) * uH * (y.val : H)⁻¹ = (uH * y.val) * (y.val : H)⁻¹ := by rw [hyu]
        _ = uH := by group
    have hyconj_G := congr_arg (Subtype.val : H → G) hyconj_H
    simpa [φ, ψ, pqMul, MulAut.conjNormal_apply] using hyconj_G
  have hAC_bot : actionCommutator (φ.comp (prodRightHom PH Q)) = ⊥ :=
    isaacs_thm_4_31_external φ hU_p hPH_p hQ_p' hfix
  rw [actionCommutator_eq_bot_iff_acts_trivially] at hAC_bot
  rintro g ⟨q, hq, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u huU
  let qQ : Q := ⟨q, hq⟩
  let uU : U := ⟨u, huU⟩
  have hqfix := congr_arg (Subtype.val : U → G) (hAC_bot qQ uU)
  have hqconj : ((q : H) : G) * u * ((q : H) : G)⁻¹ = u := by
    simpa [φ, ψ, pqMul, MulAut.conjNormal_apply] using hqfix
  have hqu : ((q : H) : G) * u = u * ((q : H) : G) := by
    calc
      ((q : H) : G) * u =
          (((q : H) : G) * u * ((q : H) : G)⁻¹) * ((q : H) : G) := by group
      _ = u * ((q : H) : G) := by rw [hqconj]
  exact hqu.symm

/-- Reduced form of **Isaacs Theorem 4.33** after the Hall-Higman reduction:
if `G` is `p`-separable and `O_{p'}(G) = 1`, then every normalizer of a
`p`-subgroup has trivial `p'`-core.

The preceding lemma puts the image of `O_{p'}(N_G(P))` inside
`C_G(O_p(G))`; Hall-Higman puts this centralizer inside `O_p(G)`.  The image is
therefore simultaneously a `p`-group and a `p'`-group, hence trivial. -/
theorem oPiCore_compl_normalizer_eq_bot_of_oPiCore_compl_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hπ' : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥)
    (P : Subgroup G) (hP : IsPGroup p P) :
    OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)}
        (Subgroup.normalizer (P : Set G)) = ⊥ := by
  classical
  set H : Subgroup G := Subgroup.normalizer (P : Set G) with hH_def
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set Q : Subgroup H :=
    OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} H with hQ_def
  set K : Subgroup G := Q.map H.subtype with hK_def
  change Q = ⊥
  have hK_le_cent : K ≤ Subgroup.centralizer (U : Set G) := by
    rw [hK_def, hQ_def, hH_def, hU_def]
    exact oPiCore_compl_normalizer_le_centralizer_opCore P hP
  have hcent_le_U : Subgroup.centralizer (U : Set G) ≤ U := by
    rw [hU_def]
    exact hall_higman_opCore hπ'
  have hK_le_U : K ≤ U := hK_le_cent.trans hcent_le_U
  have hU_p : IsPGroup p U := by
    rw [hU_def]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup p G
  have hK_p : IsPGroup p K := hU_p.to_le hK_le_U
  have hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) K :=
    isPiGroup_singleton_of_isPGroup hK_p
  have hQ_pi :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} Q := by
    rw [hQ_def]
    exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup {q | q ∉ ({p} : Set ℕ)}
  have hK_pi' :
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup {q | q ∉ ({p} : Set ℕ)} K := by
    intro q hq
    have hcard : Nat.card K = Nat.card Q := by
      rw [hK_def]
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective Q H.subtype H.subtype_injective).symm.toEquiv
    rw [hcard] at hq
    exact hQ_pi q hq
  have hcop : Nat.Coprime (Nat.card K) (Nat.card K) :=
    OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      Nat.card_pos.ne' Nat.card_pos.ne' hK_pi hK_pi'
  have hK_bot : K = ⊥ :=
    disjoint_self.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  exact (Subgroup.map_eq_bot_iff_of_injective Q H.subtype_injective).mp
    (by simpa [hK_def] using hK_bot)

/-- **Isaacs Theorem 4.33** (p-local `p'`-core containment).

If `G` is finite `p`-separable and `H` is `p`-local in `G`, then
`O_{p'}(H) ≤ O_{p'}(G)`, expressed by mapping `O_{p'}(H)` from `↥H` back into
`G`.

The general case quotients by `N = O_{p'}(G)`.  Lemma 2.17 sends `p`-local
subgroups to `p`-local subgroups modulo the `p'`-kernel, the reduced theorem
above kills the `p'`-core in the quotient, and triviality of the quotient image
is exactly containment in `N`. -/
theorem oPiCore_compl_le_oPiCore_compl_of_isPLocal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (H : Subgroup G) (hH : OddOrder.Isaacs.Ch02.IsPLocal p H) :
    (OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} H).map H.subtype ≤
      OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G := by
  classical
  set π' : Set ℕ := {q | q ∉ ({p} : Set ℕ)} with hπ'_def
  set N : Subgroup G := OddOrder.Isaacs.Ch03.oPiCore π' G with hN_def
  set f : G →* G ⧸ N := QuotientGroup.mk' N with hf_def
  set Hbar : Subgroup (G ⧸ N) := H.map f with hHbar_def
  set Q : Subgroup H := OddOrder.Isaacs.Ch03.oPiCore π' H with hQ_def
  change Q.map H.subtype ≤ N
  have hN_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π' N := by
    rw [hN_def]
    exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup π'
  have hp_coprime_N : ¬ p ∣ Nat.card N := by
    intro hp_dvd
    have hp_pf : p ∈ (Nat.card N).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Fact.out, hp_dvd, Nat.card_pos.ne'⟩
    have hp_not : p ∈ π' := hN_pi' p hp_pf
    rw [hπ'_def] at hp_not
    exact hp_not (by simp)
  have hHbar_pLocal : OddOrder.Isaacs.Ch02.IsPLocal p Hbar := by
    rw [hHbar_def, hf_def]
    exact OddOrder.Isaacs.Ch02.isPLocal_map_of_coprime_kernel hp_coprime_N hH
  have hOpi'_Gbar_bot : OddOrder.Isaacs.Ch03.oPiCore π' (G ⧸ N) = ⊥ := by
    simpa [hN_def] using OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot (G := G) π'
  have hOpi'_Hbar_bot : OddOrder.Isaacs.Ch03.oPiCore π' Hbar = ⊥ := by
    obtain ⟨Pbar, _hPbar_ne, hPbar_p, hHbar_eq⟩ := hHbar_pLocal
    rw [hHbar_eq]
    exact oPiCore_compl_normalizer_eq_bot_of_oPiCore_compl_eq_bot
      (G := G ⧸ N) (p := p) hOpi'_Gbar_bot Pbar hPbar_p
  let fH : H →* Hbar := f.subgroupMap H
  have hfH_surj : Function.Surjective fH := f.subgroupMap_surjective H
  haveI hQ_normal : Q.Normal := by
    rw [hQ_def]
    infer_instance
  haveI hQbar_normal : (Q.map fH).Normal := hQ_normal.map fH hfH_surj
  have hQ_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π' Q := by
    rw [hQ_def]
    exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup π'
  have hQbar_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π' (Q.map fH) := by
    intro r hr
    exact hQ_pi' r (Nat.primeFactors_mono (Q.card_map_dvd fH) Nat.card_pos.ne' hr)
  have hQbar_le : Q.map fH ≤ OddOrder.Isaacs.Ch03.oPiCore π' Hbar :=
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore hQbar_pi'
  have hQbar_bot : Q.map fH = ⊥ := by
    rw [hOpi'_Hbar_bot] at hQbar_le
    exact le_bot_iff.mp hQbar_le
  rintro y ⟨q, hq, rfl⟩
  have hqbar_mem : fH q ∈ Q.map fH := ⟨q, hq, rfl⟩
  rw [hQbar_bot, Subgroup.mem_bot] at hqbar_mem
  have hfq_one : f (q : G) = 1 := by
    change (f.subgroupMap H q).val = (1 : G ⧸ N)
    rw [show f.subgroupMap H q = fH q from rfl, hqbar_mem]
    rfl
  change (q : G) ∈ N
  rw [← QuotientGroup.eq_one_iff]
  simpa [hf_def] using hfq_one

/-- Strong-induction form of Isaacs Theorem 4.38. -/
private theorem isaacs_thm_4_38_aux
    {A : Type*} [Group A] [Finite A]
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    (P Q : Subgroup A) [Q.Normal] (hP : IsPGroup p P) (hQ_p' : ¬ p ∣ Nat.card Q) :
    ∀ n : ℕ, ∀ {G : Type*} [Group G] [Finite G]
    (φ : A →* MulAut G) (_ : IsPGroup p G)
    (_ : ∀ g : G, (∀ x : P, (φ x.val) g = g) → ∀ y : Q, (φ y.val) g = g),
    Nat.card G ≤ n → actionCommutator (φ.comp Q.subtype) = ⊥ := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ _ _ h_le
    exfalso
    have h_pos : 0 < Nat.card G := Nat.card_pos
    omega
  | succ m IH =>
    intro G _ _ φ hG h_fix h_le
    rcases Nat.lt_or_ge (Nat.card G) (m + 1) with h_lt | h_ge
    · exact IH φ hG h_fix (Nat.le_of_lt_succ h_lt)
    by_cases hG_nontriv : Nontrivial G
    swap
    · haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG_nontriv
      rw [actionCommutator_eq_bot_iff_acts_trivially]
      intro q g
      exact Subsingleton.elim _ _
    letI : Nontrivial G := hG_nontriv
    let φQ : Q →* MulAut G := φ.comp Q.subtype
    have hCop : Nat.Coprime (Nat.card Q) (Nat.card G) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
      rw [hk]
      exact (((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hQ_p').symm).pow_right k
    haveI hG_nilp : Group.IsNilpotent G := hG.isNilpotent
    have hG_solv : IsSolvable G := IsNilpotent.to_isSolvable
    have hSolv : IsSolvable Q ∨ IsSolvable G := Or.inr hG_solv
    by_cases h_AC_top : actionCommutator φQ = ⊤
    swap
    · set H : Subgroup G := actionCommutator φQ with hH_def
      have hH_card_lt : Nat.card H < Nat.card G := subgroup_card_lt_of_ne_top h_AC_top
      have hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H := by
        rw [hH_def]
        simpa [φQ] using OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator_of_normal φ Q
      let φH : A →* MulAut H :=
        OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH_inv
      have hH_pgrp : IsPGroup p H := hG.to_subgroup H
      have h_fix_H :
          ∀ h : H, (∀ x : P, (φH x.val) h = h) → ∀ y : Q, (φH y.val) h = h := by
        intro h hP_fix y
        apply Subtype.ext
        have hP_fix_val : ∀ x : P, (φ x.val) h.val = h.val := by
          intro x
          have hx := congr_arg (Subtype.val : H → G) (hP_fix x)
          simpa [φH] using hx
        have hQ_fix := h_fix h.val hP_fix_val y
        simpa [φH] using hQ_fix
      have hIH_H := IH φH hH_pgrp h_fix_H
        (Nat.le_of_lt_succ (hH_card_lt.trans_le h_le))
      have h_triv : ∀ q : Q, ∀ x ∈ H, (φ q.val) x = x := by
        intro q x hx
        rw [actionCommutator_eq_bot_iff_acts_trivially] at hIH_H
        have hact := congr_arg (Subtype.val : H → G) (hIH_H q ⟨x, hx⟩)
        simpa [φH] using hact
      exact actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime
        (A := Q) (G := G) (φ := φQ) hCop hSolv h_triv
    set G' : Subgroup G := commutator G with hG'_def
    have hG'_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ G' :=
      OddOrder.Isaacs.Ch03.IsAInvariant.derivedSeries φ 1
    have h_G'_lt_top : G' < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial G
    have h_G'_card_lt : Nat.card G' < Nat.card G :=
      subgroup_card_lt_of_ne_top h_G'_lt_top.ne
    let φG' : A →* MulAut G' :=
      OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hG'_inv
    have hG'_pgrp : IsPGroup p G' := hG.to_subgroup G'
    have h_fix_G' :
        ∀ g' : G', (∀ x : P, (φG' x.val) g' = g') → ∀ y : Q, (φG' y.val) g' = g' := by
      intro g' hP_fix y
      apply Subtype.ext
      have hP_fix_val : ∀ x : P, (φ x.val) g'.val = g'.val := by
        intro x
        have hx := congr_arg (Subtype.val : G' → G) (hP_fix x)
        simpa [φG'] using hx
      have hQ_fix := h_fix g'.val hP_fix_val y
      simpa [φG'] using hQ_fix
    have hIH_G' := IH φG' hG'_pgrp h_fix_G'
      (Nat.le_of_lt_succ (h_G'_card_lt.trans_le h_le))
    have h_triv_G' : ∀ q : Q, ∀ g' ∈ G', (φ q.val) g' = g' := by
      intro q g' hg'
      rw [actionCommutator_eq_bot_iff_acts_trivially] at hIH_G'
      have hact := congr_arg (Subtype.val : G' → G) (hIH_G' q ⟨g', hg'⟩)
      simpa [φG'] using hact
    have h_class_le_2 : commutator G ≤ Subgroup.center G := by
      set XG : Subgroup (G ⋊[φQ] Q) := (SemidirectProduct.inl : G →* G ⋊[φQ] Q).range
      set YQ : Subgroup (G ⋊[φQ] Q) := (SemidirectProduct.inr : Q →* G ⋊[φQ] Q).range
      set XG' : Subgroup (G ⋊[φQ] Q) := G'.map (SemidirectProduct.inl : G →* G ⋊[φQ] Q)
      have h_G'_YQ : ⁅XG', YQ⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        rintro _ ⟨k, hk, rfl⟩ _ ⟨q, rfl⟩
        rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
        have h_fix' : (φQ q) k = k := by
          simpa [φQ] using h_triv_G' q k hk
        rw [show (φQ q) k⁻¹ = ((φQ q) k)⁻¹ from map_inv (φQ q) k,
          h_fix', mul_inv_cancel]
        exact map_one _
      have h_GG'_le : ⁅XG, XG'⁆ ≤ XG' := by
        rw [Subgroup.commutator_le]
        rintro _ ⟨g, rfl⟩ _ ⟨k, hk, rfl⟩
        rw [show (⁅(SemidirectProduct.inl g : G ⋊[φQ] Q), SemidirectProduct.inl k⁆ :
            G ⋊[φQ] Q) = SemidirectProduct.inl ⁅g, k⁆ from by
          simp [commutatorElement_def, ← map_mul, ← map_inv]]
        refine ⟨⁅g, k⁆, ?_, rfl⟩
        have hG'_normal : G'.Normal := inferInstance
        have h_gkg : g * k * g⁻¹ ∈ G' := hG'_normal.conj_mem k hk g
        have h_inv : k⁻¹ ∈ G' := G'.inv_mem hk
        rw [commutatorElement_def]
        exact G'.mul_mem h_gkg h_inv
      have h12 : ⁅⁅XG, XG'⁆, YQ⁆ = ⊥ := by
        rw [eq_bot_iff]
        calc ⁅⁅XG, XG'⁆, YQ⁆ ≤ ⁅XG', YQ⁆ := Subgroup.commutator_mono h_GG'_le le_rfl
          _ = ⊥ := h_G'_YQ
      have h23 : ⁅⁅XG', YQ⁆, XG⁆ = ⊥ := by
        rw [h_G'_YQ]
        exact Subgroup.commutator_bot_left XG
      have h_three : ⁅⁅YQ, XG⁆, XG'⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate h12 h23
      have h_XGYQ_eq_XG : ⁅XG, YQ⁆ = XG := by
        rw [← actionCommutator_map_inl φQ, h_AC_top]
        exact (MonoidHom.range_eq_map _).symm
      have h_YQXG_eq_XG : ⁅YQ, XG⁆ = XG := by
        rw [Subgroup.commutator_comm]
        exact h_XGYQ_eq_XG
      have h_XG_XG'_bot : ⁅XG, XG'⁆ = ⊥ := h_YQXG_eq_XG ▸ h_three
      have h_top_G'_bot : ⁅(⊤ : Subgroup G), G'⁆ = ⊥ := by
        apply Subgroup.map_injective (f := (SemidirectProduct.inl : G →* G ⋊[φQ] Q))
          SemidirectProduct.inl_injective
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.map_bot]
        exact h_XG_XG'_bot
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h_top_G'_bot
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have := h_top_G'_bot (Subgroup.mem_top y)
      exact (this x hx).symm
    have hOdd_p : Odd p := hp.out.odd_of_ne_two hp_odd
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
    have hOdd_card : Odd (Nat.card G) := by
      rw [hk]
      exact hOdd_p.pow
    haveI : Fact (Odd (Nat.card G)) := ⟨hOdd_card⟩
    haveI : Fact (_root_.commutator G ≤ Subgroup.center G) := ⟨h_class_le_2⟩
    set φ' : A →* MulAut (BaerMul G) := MonoidHom.toBaerMulLift φ with hφ'
    have hG_baer : IsPGroup p (BaerMul G) := (BaerMul.isPGroup_iff p).mpr hG
    have h_fix_baer :
        ∀ g : BaerMul G, (∀ x : P, (φ' x.val) g = g) →
          ∀ y : Q, (φ' y.val) g = g := by
      intro g hP_fix y
      have hP_fix_G : ∀ x : P, (φ x.val) (BaerMul.toG g) = BaerMul.toG g := by
        intro x
        have hx := congr_arg BaerMul.toG (hP_fix x)
        simpa [hφ'] using hx
      have h_fixed : (φ y.val) (BaerMul.toG g) = BaerMul.toG g :=
        h_fix (BaerMul.toG g) hP_fix_G y
      change BaerMul.ofG ((φ y.val) (BaerMul.toG g)) = g
      rw [h_fixed]
      exact BaerMul.ofG_toG g
    have h_bot_baer :=
      actionCommutator_eq_bot_of_abelian_pgroup_of_subgroup_fixedPoints
        φ' hG_baer P Q hP hQ_p' h_fix_baer
    rw [actionCommutator_eq_bot_iff_acts_trivially] at h_bot_baer
    rw [actionCommutator_eq_bot_iff_acts_trivially]
    intro q g
    have h_act := h_bot_baer q (BaerMul.ofG g)
    have h_eq : BaerMul.ofG ((φ q.val) g) = BaerMul.ofG g := by
      have hkey : (φ' q.val) (BaerMul.ofG g) = BaerMul.ofG ((φ q.val) g) := by
        change BaerMul.ofG ((φ q.val) (BaerMul.toG (BaerMul.ofG g))) =
          BaerMul.ofG ((φ q.val) g)
        rw [BaerMul.toG_ofG]
      rw [← hkey]
      exact h_act
    exact BaerMul.ofG.injective h_eq

/-- **Isaacs Theorem 4.38**.

Let `A` act on the p-group `G` with `p > 2`. If `P ≤ A` is a p-group,
`Q ⊴ A` is p', and every `P`-fixed point of `G` is `Q`-fixed, then `Q`
acts trivially on `G`. -/
theorem isaacs_thm_4_38
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (φ : A →* MulAut G) (hG : IsPGroup p G)
    (P Q : Subgroup A) [Q.Normal] (hP : IsPGroup p P) (hQ_p' : ¬ p ∣ Nat.card Q)
    (h_fix : ∀ g : G, (∀ x : P, (φ x.val) g = g) → ∀ y : Q, (φ y.val) g = g) :
    actionCommutator (φ.comp Q.subtype) = ⊥ :=
  isaacs_thm_4_38_aux hp_odd P Q hP hQ_p' (Nat.card G) φ hG h_fix le_rfl

end -- 4D

end OddOrder.Isaacs.Ch04
