/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.GroupTheory.Index

/-!
# Isaacs Ch. 3 — Lemma 3.6: crossed homomorphisms (pp. 76-78)

Isaacs, *Finite Group Theory* (AMS GSM 92), section 3B, **Lemma 3.6** —
crossed homomorphism (1-cocycle) の基礎 4 点. mathlib の
`groupCohomology.oneCocycles` は可換係数 (`Rep k G`) 限定なので, 書籍どおりの
**非可換係数** crossed homomorphism をここで定義する.

**Convention 注意**: 書籍は右作用 (`n^g`) で `φ(xy) = φ(x)^y · φ(y)` と定義するが,
mathlib は左作用 (`g • n` = `MulDistribMulAction`) なので, 標準的な (Serre 流)
左 1-cocycle 条件 `φ(xy) = φ(x) * x • φ(y)` を採用する. 両者は mirror
(`x ↦ φ(x⁻¹)` で対応) であり, 帰結もすべて mirror になる: 書籍 3.6(c) の
「右 coset `Kx = Ky`」は本ファイルでは「左 coset (`QuotientGroup` の標準)」になる.

- **3.6(a)** `CrossedHom.map_one`: `φ(1) = 1`. 追加で inverse 公式
  `CrossedHom.map_inv` (`φ(x⁻¹) = x⁻¹ • φ(x)⁻¹`, 書籍 proof 中の式).
- **3.6(b)** `CrossedHom.ker : Subgroup G`: kernel は部分群.
- **3.6(c)** `CrossedHom.apply_eq_apply_iff`: `φ(x) = φ(y) ⟺ x, y` が `ker φ` の
  同じ (左) coset (成分は `apply_eq_of_inv_mul_mem` / `inv_mul_mem_of_apply_eq`).
- **3.6(d)** `CrossedHom.rangeEquiv` (`G ⧸ ker φ ≃ φ(G)` の全単射) と
  `CrossedHom.index_ker` (`|G : ker φ| = |φ(G)|`). 書籍より強く有限性を仮定しない.

## Lemma 3.7 / Theorem 3.5 の mathlib 対応 (no-wrapper 記録)

**Lemma 3.7** (transversal difference `d(S,T) = ∏_{s≡t} s⁻¹t` の 3 性質) は Lean 実体を
書かない: mathlib の transfer 用 difference 装置が `ϕ := MonoidHom.id H`
(`H` 可換, 書籍の abelian `N` に対応) の実例化でそのまま同内容を持つ.

| 書籍 | mathlib |
|---|---|
| `d(S,T)` の定義 | `Subgroup.leftTransversals.diff ϕ S T` (`Transfer.lean`) |
| 3.7(a) `d(S,T)d(T,U) = d(S,U)` | `Subgroup.leftTransversals.diff_mul_diff` |
| 3.7(b) `d(Sg,Tg) = d(S,T)^g` | `Subgroup.smul_diff_smul'` (`Gᵐᵒᵖ`-smul = 右移動) |
| 3.7(c) `d(S,Sn) = n^{|G:N|}` | `Subgroup.smul_diff'` + `diff_self` (`α := β` 実例化) |

(書籍は right transversal だが `N` normal なので left と一致; mathlib は
`H.LeftTransversal`.) **Theorem 3.5** (abelian Schur-Zassenhaus: 存在+共役) も
Lean 実体は不要: 存在は mathlib `Subgroup.exists_right_complement'_of_coprime`
(一般 SZ) の内部で `QuotientDiff` として証明済み, 共役は repo の Thm 3.12
(`SchurZassenhausConj.lean`, 可解性両 case で book 強度) が包含する.
-/

namespace OddOrder.Isaacs.Ch03

section /- 3B: Crossed homomorphisms, Lemma 3.6 (pp. 76-78) -/

variable {G N : Type*} [Group G] [Group N] [MulDistribMulAction G N]

/-- **Isaacs p. 77 (crossed homomorphism)**: `G` が `N` に automorphism で作用する
(`MulDistribMulAction G N`) とき, `φ : G → N` が **crossed homomorphism** とは
`φ(xy) = φ(x) * x • φ(y)` を満たすこと (左作用 convention; 書籍の右作用版
`φ(xy) = φ(x)^y φ(y)` の mirror). 作用が自明なら通常の準同型に一致する. -/
structure CrossedHom (G N : Type*) [Group G] [Group N] [MulDistribMulAction G N] where
  /-- 台となる写像. -/
  toFun : G → N
  /-- Crossed homomorphism 条件 (左 1-cocycle 等式). -/
  map_mul_smul' : ∀ x y : G, toFun (x * y) = toFun x * x • toFun y

namespace CrossedHom

instance : FunLike (CrossedHom G N) G N where
  coe := CrossedHom.toFun
  coe_injective := fun φ ψ h => by cases φ; cases ψ; congr

@[ext]
lemma ext {φ ψ : CrossedHom G N} (h : ∀ x, φ x = ψ x) : φ = ψ := DFunLike.ext _ _ h

@[simp]
lemma coe_mk (f : G → N) (h : ∀ x y : G, f (x * y) = f x * x • f y) : ⇑(mk f h) = f := rfl

/-- Crossed homomorphism 条件 (coercion 形). -/
lemma map_mul_smul (φ : CrossedHom G N) (x y : G) : φ (x * y) = φ x * x • φ y :=
  φ.map_mul_smul' x y

/-- **Isaacs Lemma 3.6(a)**: `φ(1) = 1`. -/
@[simp]
lemma map_one (φ : CrossedHom G N) : φ 1 = 1 := by
  have h := φ.map_mul_smul 1 1
  rw [mul_one, one_smul] at h
  exact left_eq_mul.mp h

/-- Inverse 公式 `φ(x⁻¹) = x⁻¹ • φ(x)⁻¹` (書籍 Lemma 3.6 証明中の
`φ(k⁻¹)` の計算の一般形). -/
lemma map_inv (φ : CrossedHom G N) (x : G) : φ x⁻¹ = x⁻¹ • (φ x)⁻¹ := by
  have h := φ.map_mul_smul x x⁻¹
  rw [mul_inv_cancel, φ.map_one] at h
  have h2 : x • φ x⁻¹ = (φ x)⁻¹ := eq_inv_of_mul_eq_one_right h.symm
  rw [← h2, inv_smul_smul]

/-- **Isaacs Lemma 3.6(b)**: crossed homomorphism の kernel
`{x | φ(x) = 1}` は部分群. -/
def ker (φ : CrossedHom G N) : Subgroup G where
  carrier := {x | φ x = 1}
  one_mem' := φ.map_one
  mul_mem' := fun {x y} hx hy => by
    have hx' : φ x = 1 := hx
    have hy' : φ y = 1 := hy
    change φ (x * y) = 1
    rw [φ.map_mul_smul, hx', hy', smul_one, mul_one]
  inv_mem' := fun {x} hx => by
    have hx' : φ x = 1 := hx
    change φ x⁻¹ = 1
    rw [φ.map_inv, hx', inv_one, smul_one]

@[simp]
lemma mem_ker (φ : CrossedHom G N) {x : G} : x ∈ φ.ker ↔ φ x = 1 := Iff.rfl

/-- **Isaacs Lemma 3.6(c) (半分)**: `x⁻¹y ∈ ker φ` なら `φ(x) = φ(y)`
(`φ` は `ker φ` の左 coset 上で定数). -/
lemma apply_eq_of_inv_mul_mem (φ : CrossedHom G N) {x y : G}
    (h : x⁻¹ * y ∈ φ.ker) : φ x = φ y := by
  have h1 : φ (x⁻¹ * y) = 1 := h
  have h2 := φ.map_mul_smul x (x⁻¹ * y)
  rw [h1, smul_one, mul_one, ← mul_assoc, mul_inv_cancel, one_mul] at h2
  exact h2.symm

/-- **Isaacs Lemma 3.6(c) (半分)**: `φ(x) = φ(y)` なら `x⁻¹y ∈ ker φ`
(`φ` は相異なる coset 上で相異なる値を取る). -/
lemma inv_mul_mem_of_apply_eq (φ : CrossedHom G N) {x y : G}
    (h : φ x = φ y) : x⁻¹ * y ∈ φ.ker := by
  change φ (x⁻¹ * y) = 1
  rw [φ.map_mul_smul, φ.map_inv, ← h, ← smul_mul', inv_mul_cancel, smul_one]

/-- **Isaacs Lemma 3.6(c)**: `φ(x) = φ(y)` ⟺ `x, y` が `ker φ` の同じ左 coset.
(書籍は右作用 convention ゆえ右 coset `Kx = Ky`; mirror で左になる.) -/
lemma apply_eq_apply_iff (φ : CrossedHom G N) {x y : G} :
    φ x = φ y ↔ (x : G ⧸ φ.ker) = (y : G ⧸ φ.ker) := by
  rw [QuotientGroup.eq]
  exact ⟨φ.inv_mul_mem_of_apply_eq, φ.apply_eq_of_inv_mul_mem⟩

/-- **Isaacs Lemma 3.6(d) (全単射形)**: `φ` の誘導する `G ⧸ ker φ ≃ φ(G)`.
書籍の「`φ` は coset 上定数で相異なる coset 上相異なる値」の bundled 版. -/
noncomputable def rangeEquiv (φ : CrossedHom G N) : (G ⧸ φ.ker) ≃ Set.range ⇑φ := by
  refine Equiv.ofBijective
    (fun q => Quotient.liftOn' q (fun x => (⟨φ x, Set.mem_range_self x⟩ : Set.range ⇑φ))
      fun x y hxy =>
        Subtype.ext (φ.apply_eq_of_inv_mul_mem (QuotientGroup.leftRel_apply.mp hxy)))
    ⟨?_, ?_⟩
  · intro q₁ q₂
    refine Quotient.inductionOn₂' q₁ q₂ ?_
    intro x y h
    exact Quotient.sound' (QuotientGroup.leftRel_apply.mpr
      (φ.inv_mul_mem_of_apply_eq (Subtype.ext_iff.mp h)))
  · intro n
    obtain ⟨v, x, rfl⟩ := n
    exact ⟨(x : G ⧸ φ.ker), rfl⟩

/-- **Isaacs Lemma 3.6(d)**: `|G : ker φ| = |φ(G)|`. 書籍より強く `G`, `N` の
有限性を仮定しない (両辺 `Nat.card`; 無限 index では両辺 `0`). -/
lemma index_ker (φ : CrossedHom G N) : φ.ker.index = Nat.card (Set.range ⇑φ) := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr φ.rangeEquiv

end CrossedHom

end

end OddOrder.Isaacs.Ch03
