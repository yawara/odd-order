/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Tactic.LinearCombination

/-!
# Semidihedral group

This file defines the **semidihedral group** `SemiDihedralGroup n` of order `2 ^ (n+1)`
(also called the **quasidihedral group**). Together with the cyclic, dihedral, and
generalised quaternion families, it is one of the four classes of 2-groups admitting
a cyclic maximal subgroup; for `n ≥ 3` it is the third (genuinely new) non-abelian
example after `DihedralGroup (2 ^ n)` and `QuaternionGroup (2 ^ (n-1))`.

`SemiDihedralGroup n` is defined for all `n : ℕ`, by the presentation
$\langle c, a \mid c^{2^n} = 1,\ a^2 = 1,\ a c a^{-1} = c^{2^{n-1} - 1}\rangle$.
We use constructor `c i` for $c^i$ and `ca i` for $a \cdot c^i$, both indexed by
`ZMod (2 ^ n)`. The group has `2 * 2^n = 2^(n+1)` elements.

The mathematical definition usually requires `n ≥ 3` to obtain a non-abelian group
that is distinct from the cyclic / dihedral / quaternion cases; for smaller `n` the
formulas still define a group (`SemiDihedralGroup 0` is `ZMod 2`; for `n = 1, 2`
the construction collapses to abelian or dihedral cases). We do not enforce `n ≥ 3`
in the definition for the same convenience reasons as `QuaternionGroup`.

## Main definitions

* `OddOrder.GroupTheory.SemiDihedralGroup n`: the semidihedral group of order
  `2 ^ (n+1)`.
* `SemiDihedralGroup.c`, `SemiDihedralGroup.ca`: the two constructors.
* Group, Inhabited, Nontrivial, Fintype instances.
* `SemiDihedralGroup.card`: cardinality is `2 ^ (n+1)`.

## Implementation notes

The construction follows `Mathlib.GroupTheory.SpecificGroups.Quaternion`
(`QuaternionGroup`) closely. The key arithmetic fact is that the twist
`r := 2^(n-1) - 1 : ZMod (2^n)` satisfies `r * r = 1`, which is what makes
the multiplication formula associative. We prove this as `twist_mul_self`.

## References

* Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Lemma 6.13 and surrounding
  text on 2-groups with cyclic maximal subgroup.
* Aschbacher, *Finite Group Theory* (2000), §23.
* <https://en.wikipedia.org/wiki/Semidihedral_group>

## TODO

* Center, derived subgroup, Frattini subgroup computations.
* Isomorphism with `Dihedral` / `Quaternion` in degenerate cases (`n ≤ 2`).
* Possible mathlib upstream as `Mathlib/GroupTheory/SpecificGroups/SemiDihedral.lean`.

-/

namespace OddOrder.GroupTheory

/-- The **semidihedral group** (a.k.a. **quasidihedral group**) `SemiDihedralGroup n`
of order `2 ^ (n+1)`. It is defined by the presentation
$\langle c, a \mid c^{2^n} = 1,\ a^2 = 1,\ a c a^{-1} = c^{2^{n-1} - 1}\rangle$.
We write `c i` for $c^i$ and `ca i` for $a \cdot c^i$. -/
inductive SemiDihedralGroup (n : ℕ) : Type
  | c : ZMod (2 ^ n) → SemiDihedralGroup n
  | ca : ZMod (2 ^ n) → SemiDihedralGroup n
  deriving DecidableEq

namespace SemiDihedralGroup

variable {n : ℕ}

/-- The twist factor `r` appearing in the relation `a c a⁻¹ = c^r`.

Mathematically, `r := 2^(n-1) - 1`, valid for `n ≥ 2`. The genuine semidihedral
group requires `n ≥ 3`. For `n = 0` we get `ZMod 1` (trivial). For `n = 1` the
formula `2^0 - 1 = 0` would make the construction non-associative
(`r² = 0 ≠ 1` in `ZMod 2`); so we override and set `twist 1 := 1` to keep
the construction a valid group (in this degenerate case it coincides with
the Klein four group `ZMod 2 × ZMod 2`). -/
def twist : (n : ℕ) → ZMod (2 ^ n)
  | 0 => 0
  | 1 => 1
  | n + 2 => (2 ^ (n + 1) : ZMod (2 ^ (n + 2))) - 1

/-- The key arithmetic identity that makes the multiplication associative:
`r * r = 1` in `ZMod (2^n)`.

For `n ≥ 2`, `r = 2^(n-1) - 1` and `r² = 2^(2n-2) - 2 · 2^(n-1) + 1 = 2^(2n-2) - 2^n + 1`,
and modulo `2^n` both `2^(2n-2)` and `2^n` vanish. For `n ≤ 1` we check by `decide`. -/
theorem twist_mul_self : twist n * twist n = 1 := by
  match n with
  | 0 => decide
  | 1 => decide
  | k + 2 =>
    change ((2 ^ (k + 1) : ZMod (2 ^ (k + 2))) - 1) *
         ((2 ^ (k + 1) : ZMod (2 ^ (k + 2))) - 1) = 1
    have h2 : (2 ^ (k + 1) : ZMod (2 ^ (k + 2))) * (2 ^ (k + 1)) = 0 := by
      have key : ((2 ^ (k + 2) : ℕ) : ZMod (2 ^ (k + 2))) = 0 := ZMod.natCast_self _
      have eq1 : (2 ^ (k + 1) : ZMod (2 ^ (k + 2))) * (2 ^ (k + 1)) =
          ((2 ^ (k + 2) : ℕ) : ZMod (2 ^ (k + 2))) * (2 ^ k : ZMod (2 ^ (k + 2))) := by
        push_cast
        ring
      rw [eq1, key, zero_mul]
    have h3 : (2 : ZMod (2 ^ (k + 2))) * (2 ^ (k + 1)) = 0 := by
      have key : ((2 ^ (k + 2) : ℕ) : ZMod (2 ^ (k + 2))) = 0 := ZMod.natCast_self _
      have eq1 : (2 : ZMod (2 ^ (k + 2))) * (2 ^ (k + 1)) =
          ((2 ^ (k + 2) : ℕ) : ZMod (2 ^ (k + 2))) := by
        push_cast; rw [pow_succ]; ring
      rw [eq1, key]
    linear_combination h2 - h3

/-- Multiplication on the semidihedral group, given by the formulas derived from
`a c = c^r a` (equivalently `c a = a c^r`), where `r := 2^(n-1) - 1`. -/
private def mul : SemiDihedralGroup n → SemiDihedralGroup n → SemiDihedralGroup n
  | c i, c j => c (i + j)
  | c i, ca j => ca (twist n * i + j)
  | ca i, c j => ca (i + j)
  | ca i, ca j => c (twist n * i + j)

/-- The identity element `1` is `c 0 = c^0`. -/
private def one : SemiDihedralGroup n := c 0

instance : Inhabited (SemiDihedralGroup n) := ⟨one⟩

/-- Inverse on the semidihedral group. For `c i`, the inverse is `c (-i)`.
For `ca i`, we need `ca i * ca j = c (twist n * i + j) = 1`, so `j = -(twist n * i)`. -/
private def inv : SemiDihedralGroup n → SemiDihedralGroup n
  | c i => c (-i)
  | ca i => ca (-(twist n * i))

/-- The group structure on `SemiDihedralGroup n`. -/
instance : Group (SemiDihedralGroup n) where
  mul := mul
  mul_assoc := by
    have hr : twist n * twist n = 1 := twist_mul_self
    rintro (i | i) (j | j) (k | k) <;>
      (change mul (mul _ _) _ = mul _ (mul _ _)) <;>
      simp only [mul] <;>
      first
        | rfl
        | (refine congr_arg c ?_; linear_combination i * hr)
        | (refine congr_arg ca ?_; linear_combination i * hr)
        | (refine congr_arg c ?_; ring)
        | (refine congr_arg ca ?_; ring)
  one := one
  one_mul := by
    rintro (i | i)
    · exact congr_arg c (zero_add i)
    · change ca (twist n * 0 + i) = ca i
      rw [mul_zero, zero_add]
  mul_one := by
    rintro (i | i)
    · exact congr_arg c (add_zero i)
    · exact congr_arg ca (add_zero i)
  inv := inv
  inv_mul_cancel := by
    rintro (i | i)
    · exact congr_arg c (neg_add_cancel i)
    · change c (twist n * (-(twist n * i)) + i) = one
      have hcalc : twist n * (-(twist n * i)) = -(twist n * twist n * i) := by ring
      rw [hcalc, twist_mul_self, one_mul, neg_add_cancel]
      rfl

@[simp]
theorem c_mul_c (i j : ZMod (2 ^ n)) : c i * c j = c (i + j) := rfl

@[simp]
theorem c_mul_ca (i j : ZMod (2 ^ n)) : c i * ca j = ca (twist n * i + j) := rfl

@[simp]
theorem ca_mul_c (i j : ZMod (2 ^ n)) : ca i * c j = ca (i + j) := rfl

@[simp]
theorem ca_mul_ca (i j : ZMod (2 ^ n)) : ca i * ca j = c (twist n * i + j) := rfl

@[simp]
theorem inv_c (i : ZMod (2 ^ n)) : (c i)⁻¹ = c (-i) := rfl

@[simp]
theorem inv_ca (i : ZMod (2 ^ n)) : (ca i)⁻¹ = ca (-(twist n * i)) := rfl

@[simp]
theorem c_zero : c 0 = (1 : SemiDihedralGroup n) := rfl

theorem one_def : (1 : SemiDihedralGroup n) = c 0 := rfl

/-- The equivalence between `SemiDihedralGroup n` and the disjoint sum of two
copies of `ZMod (2 ^ n)`. -/
@[simps]
def equivSum : SemiDihedralGroup n ≃ ZMod (2 ^ n) ⊕ ZMod (2 ^ n) where
  toFun
    | c j => .inl j
    | ca j => .inr j
  invFun
    | .inl j => c j
    | .inr j => ca j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

instance : NeZero (2 ^ n) := ⟨(Nat.two_pow_pos n).ne'⟩

instance : Fintype (SemiDihedralGroup n) :=
  Fintype.ofEquiv _ equivSum.symm

instance : Nontrivial (SemiDihedralGroup n) :=
  ⟨⟨c 0, ca 0, by by_contra h; injection h⟩⟩

/-- `SemiDihedralGroup n` has `2 ^ (n+1)` elements. -/
theorem card : Fintype.card (SemiDihedralGroup n) = 2 ^ (n + 1) := by
  rw [Fintype.card_eq.mpr ⟨equivSum⟩, Fintype.card_sum, ZMod.card, ← two_mul, pow_succ, mul_comm]

theorem nat_card : Nat.card (SemiDihedralGroup n) = 2 ^ (n + 1) := by
  rw [Nat.card_eq_fintype_card, card]

/-! ### Powers and order of `c`

The element `c 1` generates a cyclic subgroup of order `2^n`. -/

@[simp]
theorem c_one_pow (k : ℕ) : (c 1 : SemiDihedralGroup n) ^ k = c k := by
  induction k with
  | zero => rw [Nat.cast_zero]; rfl
  | succ k IH =>
    rw [pow_succ, IH, c_mul_c]
    congr 1
    push_cast
    ring

@[simp]
theorem c_pow (i : ZMod (2 ^ n)) (k : ℕ) :
    (c i) ^ k = c (i * (k : ZMod (2 ^ n))) := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, mul_zero]; rfl
  | succ k IH =>
    rw [pow_succ, IH, c_mul_c]
    congr 1
    push_cast
    ring

theorem c_one_pow_n : (c 1 : SemiDihedralGroup n) ^ (2 ^ n) = 1 := by
  rw [c_one_pow]
  show c ((2 ^ n : ℕ) : ZMod (2 ^ n)) = 1
  rw [ZMod.natCast_self]
  rfl

/-- `orderOf (c 1) = 2 ^ n`. For `n = 0` both sides are `1` (the group is trivial-or-`Z/2`,
and `c 1 = c 0 = 1`); for `n ≥ 1` the element `c 1` generates a cyclic subgroup of index 2. -/
@[simp]
theorem orderOf_c_one : orderOf (c 1 : SemiDihedralGroup n) = 2 ^ n := by
  apply (Nat.le_of_dvd (NeZero.pos _)
    (orderOf_dvd_of_pow_eq_one c_one_pow_n)).lt_or_eq.resolve_left
  intro h
  have h1 : (c 1 : SemiDihedralGroup n) ^ orderOf (c 1 : SemiDihedralGroup n) = 1 :=
    pow_orderOf_eq_one _
  rw [c_one_pow] at h1
  have h_eq : (c ((orderOf (c 1 : SemiDihedralGroup n) : ℕ) : ZMod (2 ^ n)) :
      SemiDihedralGroup n) = c 0 := h1
  injection h_eq with h2
  rw [← ZMod.val_eq_zero, ZMod.val_natCast, Nat.mod_eq_of_lt h] at h2
  exact absurd h2 (orderOf_pos _).ne'

/-- `orderOf (c i) = 2 ^ n / gcd(2^n, i.val)`. -/
theorem orderOf_c (i : ZMod (2 ^ n)) :
    orderOf (c i) = 2 ^ n / Nat.gcd (2 ^ n) i.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  rw [← c_one_pow, orderOf_pow, orderOf_c_one]

/-! ### Powers and involutions on the `ca` side

Every `ca i` satisfies `(ca i)^4 = 1`. The element `ca 0` is the canonical involution
outside the cyclic subgroup `⟨c 1⟩`. -/

@[simp]
theorem ca_sq (i : ZMod (2 ^ n)) : (ca i : SemiDihedralGroup n) ^ 2 = c (twist n * i + i) := by
  rw [sq, ca_mul_ca]

theorem ca_zero_sq : (ca 0 : SemiDihedralGroup n) ^ 2 = 1 := by
  rw [ca_sq, mul_zero, zero_add]
  rfl

/-- `2 · (twist n + 1) = 0` in `ZMod (2^n)`. Equivalent to `twist n ≡ -1 (mod 2^{n-1})`,
the key identity behind `(ca i)^4 = 1`. -/
private lemma two_mul_twist_succ_eq_zero :
    (2 : ZMod (2 ^ n)) * (twist n + 1) = 0 := by
  match n with
  | 0 => decide
  | 1 => decide
  | k + 2 =>
    have h_twist : (twist (k + 2) : ZMod (2 ^ (k + 2))) + 1 =
        (2 ^ (k + 1) : ZMod (2 ^ (k + 2))) := by
      change ((2 ^ (k + 1) : ZMod (2 ^ (k + 2))) - 1) + 1 = _
      ring
    rw [h_twist]
    have key : ((2 ^ (k + 2) : ℕ) : ZMod (2 ^ (k + 2))) = 0 := ZMod.natCast_self _
    have eq1 : (2 : ZMod (2 ^ (k + 2))) * 2 ^ (k + 1) =
        ((2 ^ (k + 2) : ℕ) : ZMod (2 ^ (k + 2))) := by
      push_cast
      rw [pow_succ]
      ring
    rw [eq1, key]

theorem ca_pow_four (i : ZMod (2 ^ n)) : (ca i : SemiDihedralGroup n) ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ca_sq, c_pow]
  show c ((twist n * i + i) * ((2 : ℕ) : ZMod (2 ^ n))) = 1
  have h : (twist n * i + i) * ((2 : ℕ) : ZMod (2 ^ n)) = 2 * (twist n + 1) * i := by
    push_cast; ring
  rw [h, two_mul_twist_succ_eq_zero, zero_mul]
  rfl

/-! ### Defining conjugation relation

The relation `a · c · a⁻¹ = c^{twist n}` is the defining relation of `SemiDihedralGroup n`.
This is what Isaacs Lemma 6.13 uses to recognise semidihedral structure. -/

/-- **Defining relation**: conjugation of `c i` by any `ca j` is `c (twist n · i)`,
independent of `j`. Specialised to `j = 0` this gives `a · c · a⁻¹ = c^{twist n}`. -/
theorem c_conj_ca (j i : ZMod (2 ^ n)) :
    (ca j : SemiDihedralGroup n) * c i * (ca j)⁻¹ = c (twist n * i) := by
  simp only [inv_ca, ca_mul_c, ca_mul_ca]
  congr 1
  ring

theorem c_one_conj_ca_zero :
    (ca 0 : SemiDihedralGroup n) * c 1 * (ca 0)⁻¹ = c (twist n) := by
  rw [c_conj_ca, mul_one]

end SemiDihedralGroup

end OddOrder.GroupTheory
