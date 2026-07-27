/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusActionTI

/-!
# Isaacs Problem 6B.3 — Thm 6.21 の coprime 仮定は落とせない (書籍 p. 195)

**主張**: Thm 6.21 (可換非巡回 `A` が `N` に **coprime** に作用すれば `C_N(a)` (`a ≠ 1`) が
`N` を生成する) から coprime 仮定を落とすと結論は**偽**になる。

**反例**: `A = (ℤ/2)²` を `N = (ℤ/2)³` に

```
(b, c) · (x, y, z) = (x + b z, y + c z, z)
```

で作用させる (`GL(3,2)` の単三角行列のうち `a` 成分が `0` のもの全体 — 基本可換 `2`-群)。

* `A` は可換で**非巡回** (Klein 四元群)。
* `|A| = 4`, `|N| = 8` なので **coprime でない**。
* `(b,c) ≠ (0,0)` なら固定点は `b z = 0 ∧ c z = 0` すなわち **`z = 0`**。したがって
  すべての `C_N(a)` (`a ≠ 1`) が超平面 `{z = 0}` に含まれ, 生成しても `N` にならない。
-/

namespace OddOrder.Isaacs.Ch06

section /- 6B.3: Thm 6.21 の coprime 仮定の必要性 (p. 195) -/

/-- 反例の作用側 `A = (ℤ/2)²` (Klein 四元群)。 -/
abbrev KleinFour : Type := Multiplicative (ZMod 2 × ZMod 2)

/-- 反例の被作用側 `N = (ℤ/2)³`。 -/
abbrev ElemAbelianCube : Type := Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)

/-- 反例の作用 (加法的な書き方): `(b, c) · (x, y, z) = (x + b z, y + c z, z)`。 -/
def shearAct (a : ZMod 2 × ZMod 2) (n : ZMod 2 × ZMod 2 × ZMod 2) :
    ZMod 2 × ZMod 2 × ZMod 2 :=
  (n.1 + a.1 * n.2.2, n.2.1 + a.2 * n.2.2, n.2.2)

instance : MulDistribMulAction KleinFour ElemAbelianCube where
  smul a n := Multiplicative.ofAdd (shearAct a.toAdd n.toAdd)
  one_smul n := by
    apply Multiplicative.toAdd.injective
    change shearAct (0 : ZMod 2 × ZMod 2) (Multiplicative.toAdd n) = Multiplicative.toAdd n
    simp [shearAct]
  mul_smul a b n := by
    apply Multiplicative.toAdd.injective
    change shearAct (Multiplicative.toAdd a + Multiplicative.toAdd b) (Multiplicative.toAdd n)
      = shearAct (Multiplicative.toAdd a)
        (shearAct (Multiplicative.toAdd b) (Multiplicative.toAdd n))
    simp only [shearAct, Prod.mk.injEq, Prod.fst_add, Prod.snd_add]
    exact ⟨by ring, by ring, trivial⟩
  smul_one a := by
    apply Multiplicative.toAdd.injective
    change shearAct (Multiplicative.toAdd a) (0 : ZMod 2 × ZMod 2 × ZMod 2) = 0
    simp [shearAct]
  smul_mul a x y := by
    apply Multiplicative.toAdd.injective
    change shearAct (Multiplicative.toAdd a) (Multiplicative.toAdd x + Multiplicative.toAdd y)
      = shearAct (Multiplicative.toAdd a) (Multiplicative.toAdd x)
        + shearAct (Multiplicative.toAdd a) (Multiplicative.toAdd y)
    simp only [shearAct, Prod.mk_add_mk, Prod.mk.injEq, Prod.fst_add, Prod.snd_add]
    exact ⟨by ring, by ring, trivial⟩

/-- `A` は巡回でない: すべての元が `a ^ 2 = 1` をみたすのに位数は `4`。 -/
theorem not_isCyclic_kleinFour : ¬ IsCyclic KleinFour := by
  intro h
  obtain ⟨g, hg⟩ := h.exists_generator
  have hsq : g * g = 1 := by
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd g + Multiplicative.toAdd g = 0
    have hz : ∀ x : ZMod 2, x + x = 0 := by decide
    refine Prod.ext ?_ ?_ <;> exact hz _
  have hord : orderOf g ≤ 2 := by
    refine orderOf_le_of_pow_eq_one (by norm_num) ?_
    rw [pow_two]; exact hsq
  have hcard : orderOf g = Nat.card KleinFour :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  rw [hcard] at hord
  have h4 : Nat.card KleinFour = 4 := by rw [Nat.card_eq_fintype_card]; decide
  omega

/-- `(p1, p2) ≠ 0` かつ `p1 z = p2 z = 0` (係数 `ℤ/2`) なら `z = 0`。 -/
theorem eq_zero_of_shear_fixed : ∀ {p1 p2 z : ZMod 2},
    (p1, p2) ≠ ((0 : ZMod 2), (0 : ZMod 2)) → p1 * z = 0 → p2 * z = 0 → z = 0 := by decide

/-- 固定点が乗る超平面 `{(x, y, 0)}`。 -/
def lastCoordZero : Subgroup ElemAbelianCube where
  carrier := {u : ElemAbelianCube | (Multiplicative.toAdd u).2.2 = 0}
  mul_mem' := fun {x y} hx hy => by
    have hx' : (Multiplicative.toAdd x).2.2 = 0 := hx
    have hy' : (Multiplicative.toAdd y).2.2 = 0 := hy
    change (Multiplicative.toAdd x).2.2 + (Multiplicative.toAdd y).2.2 = 0
    rw [hx', hy', add_zero]
  one_mem' := rfl
  inv_mem' := fun {x} hx => by
    have hx' : (Multiplicative.toAdd x).2.2 = 0 := hx
    change -(Multiplicative.toAdd x).2.2 = 0
    rw [hx', neg_zero]

/-- **Isaacs Problem 6B.3** (p. 195) ⭐: Thm 6.21 の coprime 仮定は落とせない。

`A = (ℤ/2)²` は可換非巡回だが, `N = (ℤ/2)³` への上記のずらし作用は coprime でなく,
`C_N(a)` (`a ≠ 1`) たちは超平面 `{z = 0}` しか生成しない。 -/
theorem nontrivialActionFixedByClosure_ne_top_of_not_coprime :
    ¬ IsCyclic KleinFour ∧
      ¬ Nat.Coprime (Nat.card KleinFour) (Nat.card ElemAbelianCube) ∧
      nontrivialActionFixedByClosure
        (MulDistribMulAction.toMulAut KleinFour ElemAbelianCube) ≠ ⊤ := by
  refine ⟨not_isCyclic_kleinFour, ?_, ?_⟩
  · have h1 : Nat.card KleinFour = 4 := by rw [Nat.card_eq_fintype_card]; decide
    have h2 : Nat.card ElemAbelianCube = 8 := by rw [Nat.card_eq_fintype_card]; decide
    rw [h1, h2]
    decide
  · intro htop
    have hle : nontrivialActionFixedByClosure
        (MulDistribMulAction.toMulAut KleinFour ElemAbelianCube) ≤ lastCoordZero := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro u ⟨a, ha, hu⟩
      have hfix : a • u = u := hu
      have hfix' : shearAct (Multiplicative.toAdd a) (Multiplicative.toAdd u)
          = Multiplicative.toAdd u := congrArg Multiplicative.toAdd hfix
      have hane : ((Multiplicative.toAdd a).1, (Multiplicative.toAdd a).2)
          ≠ ((0 : ZMod 2), (0 : ZMod 2)) := by
        intro hcon
        refine ha (Multiplicative.toAdd.injective ?_)
        have h0 : Multiplicative.toAdd a = ((0 : ZMod 2), (0 : ZMod 2)) := by rw [← hcon]
        exact h0
      have e1 : (Multiplicative.toAdd a).1 * (Multiplicative.toAdd u).2.2 = 0 := by
        have h := congrArg (fun w : ZMod 2 × ZMod 2 × ZMod 2 => w.1) hfix'
        simpa [shearAct] using h
      have e2 : (Multiplicative.toAdd a).2 * (Multiplicative.toAdd u).2.2 = 0 := by
        have h := congrArg (fun w : ZMod 2 × ZMod 2 × ZMod 2 => w.2.1) hfix'
        simpa [shearAct] using h
      exact eq_zero_of_shear_fixed hane e1 e2
    have htopK : (lastCoordZero : Subgroup ElemAbelianCube) = ⊤ :=
      top_le_iff.mp (htop ▸ hle)
    have hmem : Multiplicative.ofAdd ((0 : ZMod 2), (0 : ZMod 2), (1 : ZMod 2))
        ∈ lastCoordZero := htopK ▸ Subgroup.mem_top _
    have hone : (1 : ZMod 2) = 0 := hmem
    exact one_ne_zero hone

end

end OddOrder.Isaacs.Ch06
