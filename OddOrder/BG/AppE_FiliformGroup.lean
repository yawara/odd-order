/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_FiliformCounterexample
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.LinearCombination

/-!
# The Lazard group of `Q₆`: the group-level counterexample to BG Proposition E.4

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, Proposition E.4 (p. 162).

This leaf is **Tier 2** of the counterexample programme (issue 3027; Tier 1 =
`OddOrder/BG/AppE_FiliformCounterexample.lean`): it constructs the **Lazard group**
`S = Exp(L)` of the exceptional filiform Lie ring `Q₆` over `𝔽₁₉₇` as an honest
`Group` in Lean, so that the printed Proposition E.4 can be refuted against the
repo's own `RegularOperatorSetup` — eliminating the last prose gap (the Lazard
correspondence) left by Tier 1.

## The group law

`Q6` is `V = Fin 6 → ZMod 197` equipped with the truncated Baker–Campbell–Hausdorff
multiplication `gmul` in coordinates of the first kind, **rescaled** by
`diag(1, 1, 2, 12, 24, 720)` so that every coefficient is a small integer.  The
rescaling matters: it turns all the group identities below into polynomial
identities with *integer* coefficients that hold over `ℚ` (verified symbolically),
hence over `ℤ`, hence over every commutative ring — so plain `ring` closes them,
with no characteristic-`197` coefficient arithmetic anywhere.

The polynomials were computed in the truncated universal enveloping algebra
`U(L)/(weight > 5)` (PBW straightening; session scripts `derive_group_law.py`,
`emit_scaled.py`, issue 3027), where the following were verified over `ℚ` before
the rescaling: the Friedrichs criterion (`log(exp x · exp y)` is a Lie element —
the internal consistency check of the computation), associativity, the unit and
inverse laws, `gmul (c • x) x = (c + 1) • x`, and the exact weight-grading of every
monomial.  Lean re-verifies all of these from scratch; the symbolic derivation is
scaffolding, not a trusted input.

Because the law is graded-polynomial with linear top layer and `x ^ n = n • x`,
this group is the exponent-`197`, order-`197⁶`, class-`5` Lazard group of `Q₆` —
but nothing below relies on the correspondence; all group facts are proved directly
against `gmul`.
-/

namespace OddOrder.BG.AppE.Filiform

open scoped commutatorElement

/-! ### The (rescaled) truncated BCH group law -/

/-- The Lazard group law of `Q₆` over `𝔽₁₉₇`: truncated BCH in first-kind
coordinates, rescaled by `diag(1,1,2,12,24,720)` to clear all denominators.
Every group identity below is an integer polynomial identity, so `ring` applies. -/
def gmul (x y : V) : V := fun k =>
  if k = 0 then x 0 + y 0
  else if k = 1 then x 1 + y 1
  else if k = 2 then x 0 * y 1 - x 1 * y 0 + x 2 + y 2
  else if k = 3 then
    x 0 * x 1 * y 1 - x 0 * y 1 * y 1 - x 1 * x 1 * y 0 + x 1 * y 0 * y 1 +
      3 * x 1 * y 2 - 3 * x 2 * y 1 + x 3 + y 3
  else if k = 4 then
    -x 0 * x 1 * y 1 * y 1 + x 1 * x 1 * y 0 * y 1 + x 1 * x 1 * y 2 - x 1 * x 2 * y 1 -
      x 1 * y 1 * y 2 + x 1 * y 3 + x 2 * y 1 * y 1 - x 3 * y 1 + x 4 + y 4
  else
    -x 0 * x 0 * x 1 * x 1 * y 1 - 6 * x 0 * x 0 * x 1 * y 1 * y 1 -
      2 * x 0 * x 0 * y 1 * y 1 * y 1 + x 0 * x 1 * x 1 * x 1 * y 0 +
      8 * x 0 * x 1 * x 1 * y 0 * y 1 + 8 * x 0 * x 1 * y 0 * y 1 * y 1 -
      15 * x 0 * x 1 * y 1 * y 2 + 5 * x 0 * x 1 * y 3 - 10 * x 0 * x 3 * y 1 +
      x 0 * y 0 * y 1 * y 1 * y 1 + 5 * x 0 * y 1 * y 3 + 15 * x 0 * y 4 -
      2 * x 1 * x 1 * x 1 * y 0 * y 0 - 6 * x 1 * x 1 * y 0 * y 0 * y 1 +
      15 * x 1 * x 2 * y 0 * y 1 + 15 * x 1 * x 2 * y 2 + 5 * x 1 * x 3 * y 0 -
      x 1 * y 0 * y 0 * y 1 * y 1 - 10 * x 1 * y 0 * y 3 - 15 * x 1 * y 2 * y 2 -
      15 * x 2 * x 2 * y 1 + 15 * x 2 * y 1 * y 2 + 15 * x 2 * y 3 +
      5 * x 3 * y 0 * y 1 - 15 * x 3 * y 2 - 15 * x 4 * y 0 + x 5 + y 5

theorem gmul_zero_right (x : V) : gmul x 0 = x := by
  funext k
  fin_cases k <;> simp [gmul]

theorem gmul_zero_left (y : V) : gmul 0 y = y := by
  funext k
  fin_cases k <;> simp [gmul]

theorem gmul_neg_left (x : V) : gmul (-x) x = 0 := by
  funext k
  fin_cases k <;> simp [gmul] <;> ring

/-- **Associativity of the BCH law** — coordinatewise, integer polynomial
identities (the mod-`197` shadow of the rational BCH identities, made integral by
the rescaling), closed by `ring`. -/
theorem gmul_assoc (x y z : V) : gmul (gmul x y) z = gmul x (gmul y z) := by
  funext k
  fin_cases k <;> simp [gmul] <;> ring

/-! ### The group `Q6` -/

/-- The Lazard group `S = Exp(Q₆)`: order `197⁶`, exponent `197`, nilpotency
class `5` — the group-level carrier of the counterexample to BG Prop E.4. -/
@[ext]
structure Q6 : Type where
  /-- first-kind (rescaled BCH) coordinates -/
  co : V

instance : One Q6 := ⟨⟨0⟩⟩
instance : Mul Q6 := ⟨fun x y => ⟨gmul x.co y.co⟩⟩
instance : Inv Q6 := ⟨fun x => ⟨-x.co⟩⟩

@[simp] theorem co_mul (x y : Q6) : (x * y).co = gmul x.co y.co := rfl
@[simp] theorem co_one : (1 : Q6).co = 0 := rfl
@[simp] theorem co_inv (x : Q6) : (x⁻¹).co = -x.co := rfl

instance : Group Q6 :=
  Group.ofLeftAxioms
    (fun _ _ _ => Q6.ext (by simp [gmul_assoc]))
    (fun _ => Q6.ext (by simp [gmul_zero_left]))
    (fun _ => Q6.ext (by simp [gmul_neg_left]))

instance : Finite Q6 :=
  Finite.of_injective Q6.co fun _ _ h => Q6.ext h

/-- `|S| = 197⁶`. -/
theorem card_q6 : Nat.card Q6 = 197 ^ 6 := by
  rw [Nat.card_eq_of_bijective (fun x : Q6 => x.co)
    ⟨fun _ _ h => Q6.ext h, fun f => ⟨⟨f⟩, rfl⟩⟩]
  simp [Nat.card_pi, Nat.card_zmod]

/-! ### Powers are scalar multiples: exponent `197` -/

theorem gmul_smul_self (c : K) (x : V) : gmul (c • x) x = (c + 1) • x := by
  funext k
  fin_cases k <;> simp [gmul] <;> ring

/-- `x ^ n = n • x` in BCH coordinates. -/
theorem co_pow (x : Q6) (n : ℕ) : (x ^ n).co = (n : K) • x.co := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    show gmul (x ^ n).co x.co = _
    rw [ih, gmul_smul_self]
    congr 1
    push_cast
    ring

/-- `S` has exponent `197`. -/
theorem pow_card_eq_one (x : Q6) : x ^ 197 = 1 := by
  ext k
  rw [co_pow, show ((197 : ℕ) : K) = 0 from by decide, zero_smul]
  rfl

/-- `S` is a `197`-group. -/
theorem isPGroup_q6 : IsPGroup 197 Q6 :=
  fun g => ⟨1, by rw [pow_one]; exact pow_card_eq_one g⟩

/-! ### The distinguished elements -/

/-- `v = a + b` as a group element: the generator of `R₀`. -/
def vg : Q6 := ⟨v⟩

/-- `e₅` (rescaled) as a group element: the generator of `R₁ ≤ Z(S)`. -/
def e5g : Q6 := ⟨e5⟩

/-- `b` as a group element: a witness in `T = C_S(Z₂(S))`. -/
def bg : Q6 := ⟨eB⟩

/-- `e₂` (rescaled) as a group element: the other witness in `T`. -/
def e2g : Q6 := ⟨e2⟩

/-- `e₄` (rescaled) as a group element: a generator of `Z₂(S)` used to cut `T`
out. -/
def e4g : Q6 := ⟨e4⟩

theorem vg_ne_one : vg ≠ 1 := by
  intro h
  exact absurd (congrFun (congrArg Q6.co h) 0) (by decide)

theorem e5g_ne_one : e5g ≠ 1 := by
  intro h
  exact absurd (congrFun (congrArg Q6.co h) 5) (by decide)

theorem orderOf_vg : orderOf vg = 197 :=
  orderOf_eq_prime (pow_card_eq_one vg) vg_ne_one

theorem orderOf_e5g : orderOf e5g = 197 :=
  orderOf_eq_prime (pow_card_eq_one e5g) e5g_ne_one

/-- **`T` is not abelian, at the group level**: `b` and `e₂` do not commute
(their group commutator is `≡ e₃` modulo higher weight; concretely the third
coordinate of `b * e₂` and `e₂ * b` differ by `6 ≠ 0`). -/
theorem bg_e2g_not_commute : bg * e2g ≠ e2g * bg := by
  intro h
  exact absurd (congrFun (congrArg Q6.co h) 3) (by decide)

/-- `a` as a group element: together with `bg` it generates `S`, and it cuts the
first coordinate out of `Z(S)` and `Z₂(S)`. -/
def ag : Q6 := ⟨eA⟩

@[simp] theorem co_ag : ag.co = eA := rfl
@[simp] theorem co_vg : vg.co = v := rfl
@[simp] theorem co_e5g : e5g.co = e5 := rfl
@[simp] theorem co_bg : bg.co = eB := rfl
@[simp] theorem co_e2g : e2g.co = e2 := rfl
@[simp] theorem co_e4g : e4g.co = e4 := rfl

/-! ### The `e₅`-line is central -/

/-- Multiplying by an `e₅`-line element on the right is coordinate addition:
`e₅` sits in the top layer of the grading, so no BCH cross terms survive. -/
theorem gmul_smul_e5 (x : V) (t : K) : gmul x (t • e5) = x + t • e5 := by
  funext k
  fin_cases k <;> simp [gmul, e5]

/-- Multiplying by an `e₅`-line element on the left is coordinate addition. -/
theorem smul_e5_gmul (x : V) (t : K) : gmul (t • e5) x = x + t • e5 := by
  funext k
  fin_cases k <;> simp [gmul, e5] <;> ring

/-- **`Z(S)` is exactly the `e₅`-line**: an element is central iff its coordinates
`0`–`4` vanish.  (Upper bound: commuting with `a` forces `x₁ = x₄ = 0` and commuting
with `b` forces `x₀ = x₂ = x₃ = 0`; lower bound: `gmul_smul_e5`/`smul_e5_gmul`.) -/
theorem mem_center_iff {x : Q6} :
    x ∈ Subgroup.center Q6 ↔ ∃ t : K, x.co = t • e5 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    have hA : gmul eA x.co = gmul x.co eA := congrArg Q6.co (h ag)
    have hB : gmul eB x.co = gmul x.co eB := congrArg Q6.co (h bg)
    have hA2 := congrFun hA 2
    have hA5 := congrFun hA 5
    have hB2 := congrFun hB 2
    have hB3 := congrFun hB 3
    have hB4 := congrFun hB 4
    simp [gmul, eA, eB] at hA2 hA5 hB2 hB3 hB4
    have hx1 : x.co 1 = 0 := by
      have hh : (2 : K) * x.co 1 = 0 := by linear_combination hA2
      exact (mul_eq_zero.mp hh).resolve_left (by decide)
    have hx0 : x.co 0 = 0 := by
      have hh : (2 : K) * x.co 0 = 0 := by linear_combination -hB2
      exact (mul_eq_zero.mp hh).resolve_left (by decide)
    rw [hx0] at hB3 hB4
    have hx2 : x.co 2 = 0 := by
      have hh : (6 : K) * x.co 2 = 0 := by linear_combination hB3
      exact (mul_eq_zero.mp hh).resolve_left (by decide)
    rw [hx1, hx2] at hB4
    have hx3 : x.co 3 = 0 := by
      have hh : (2 : K) * x.co 3 = 0 := by linear_combination hB4
      exact (mul_eq_zero.mp hh).resolve_left (by decide)
    have hx4 : x.co 4 = 0 := by
      have hh : (30 : K) * x.co 4 = 0 := by linear_combination hA5
      exact (mul_eq_zero.mp hh).resolve_left (by decide)
    refine ⟨x.co 5, ?_⟩
    funext k
    fin_cases k <;> simp [e5, hx0, hx1, hx2, hx3, hx4]
  · rintro ⟨t, ht⟩ y
    ext1
    rw [co_mul, co_mul, ht, gmul_smul_e5, smul_e5_gmul]

/-- `e₅` generates a central subgroup: `⟨e5g⟩ ≤ Z(S)`. -/
theorem e5g_mem_center : e5g ∈ Subgroup.center Q6 :=
  mem_center_iff.mpr ⟨1, by rw [co_e5g, one_smul]⟩

/-! ### Integer powers and the two distinguished lines -/

/-- `x ^ n = n • x` in BCH coordinates, for integer exponents. -/
theorem co_zpow (x : Q6) (n : ℤ) : (x ^ n).co = (n : K) • x.co := by
  cases n with
  | ofNat m => simpa using co_pow x m
  | negSucc m =>
    rw [zpow_negSucc, co_inv, co_pow, Int.cast_negSucc, neg_smul]

/-- The coordinate description of `R₀ = ⟨vg⟩`: the line `K·v`. -/
theorem mem_zpowers_vg_iff {x : Q6} :
    x ∈ Subgroup.zpowers vg ↔ ∃ c : K, x.co = c • v := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨(n : K), co_zpow vg n⟩
  · rintro ⟨c, hc⟩
    obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective c
    exact ⟨(m : ℤ), Q6.ext (by rw [co_zpow, hc, co_vg]; norm_cast)⟩

/-- The coordinate description of `R₁ = ⟨e5g⟩`: the line `K·e₅`. -/
theorem mem_zpowers_e5g_iff {x : Q6} :
    x ∈ Subgroup.zpowers e5g ↔ ∃ t : K, x.co = t • e5 := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨(n : K), co_zpow e5g n⟩
  · rintro ⟨t, ht⟩
    obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective t
    exact ⟨(m : ℤ), Q6.ext (by rw [co_zpow, ht, co_e5g]; norm_cast)⟩

/-- `R₀ ∩ R₁ = 1`: the lines `K·v` and `K·e₅` meet only at the origin
(coordinate `0` separates them). -/
theorem disjoint_zpowers_vg_e5g :
    Disjoint (Subgroup.zpowers vg) (Subgroup.zpowers e5g) := by
  rw [Subgroup.disjoint_def]
  intro x hxv hx5
  obtain ⟨c, hc⟩ := mem_zpowers_vg_iff.mp hxv
  obtain ⟨t, ht⟩ := mem_zpowers_e5g_iff.mp hx5
  have hc0 : c = 0 := by simpa [v, e5] using congrFun (hc.symm.trans ht) 0
  exact Q6.ext (by rw [hc, hc0, zero_smul]; rfl)

/-! ### Theorem E.3's centralizer hypothesis: `C_S(R₀) = R₀ ⊔ R₁` -/

/-- An element commutes with `vg` iff it lies on `K·v + K·e₅` in coordinates —
the triangular solve behind Theorem E.3's hypothesis `C_R(R₀) = R₀ × R₁`.
(Coordinate `2` forces `x₁ = x₀`, then `3` forces `x₂ = 0`, then `4` forces
`x₃ = 0`, then `5` forces `x₄ = 0`.) -/
theorem commute_vg_iff {x : Q6} :
    vg * x = x * vg ↔ ∃ c t : K, x.co = c • v + t • e5 := by
  constructor
  · intro h
    have h' : gmul v x.co = gmul x.co v := congrArg Q6.co h
    have h2 := congrFun h' 2
    have h3 := congrFun h' 3
    have h4 := congrFun h' 4
    have h5 := congrFun h' 5
    simp [gmul, v] at h2 h3 h4 h5
    have hx1 : x.co 1 = x.co 0 := by
      have hh : (2 : K) * (x.co 1 - x.co 0) = 0 := by linear_combination h2
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by decide))
    have hx2 : x.co 2 = 0 := by
      have hh : (6 : K) * x.co 2 = 0 := by linear_combination h3
      exact (mul_eq_zero.mp hh).resolve_left (by decide)
    rw [hx1] at h4
    have hx3 : x.co 3 = 0 := by
      have hh : (2 : K) * x.co 3 = 0 := by linear_combination h4
      exact (mul_eq_zero.mp hh).resolve_left (by decide)
    rw [hx2] at h5
    have hx4 : x.co 4 = 0 := by
      have hh : (30 : K) * x.co 4 = 0 := by linear_combination h5
      exact (mul_eq_zero.mp hh).resolve_left (by decide)
    refine ⟨x.co 0, x.co 5, ?_⟩
    funext k
    fin_cases k <;> simp [v, e5, hx1, hx2, hx3, hx4]
  · rintro ⟨c, t, hx⟩
    ext1
    rw [co_mul, co_mul, hx]
    funext k
    fin_cases k <;> simp [gmul, v, e5] <;> ring

/-- **Theorem E.3's centralizer hypothesis holds in the Lazard group**:
`C_S(R₀) = R₀ ⊔ R₁` for `R₀ = ⟨vg⟩` and `R₁ = ⟨e5g⟩` — this is the field
`RegularOperatorSetup.centralizer_eq` of the repo's E.3/E.4 setup. -/
theorem centralizer_zpowers_vg :
    Subgroup.centralizer ((Subgroup.zpowers vg : Subgroup Q6) : Set Q6) =
      Subgroup.zpowers vg ⊔ Subgroup.zpowers e5g := by
  refine le_antisymm (fun x hx => ?_) (sup_le (Subgroup.zpowers_le.mpr ?_) ?_)
  · obtain ⟨c, t, hco⟩ := commute_vg_iff.mp
      (Subgroup.mem_centralizer_iff.mp hx vg (Subgroup.mem_zpowers vg))
    have hxeq : x = (⟨c • v⟩ : Q6) * ⟨t • e5⟩ := by
      ext1
      rw [co_mul]
      show x.co = gmul (c • v) (t • e5)
      rw [gmul_smul_e5, hco]
    rw [hxeq]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (mem_zpowers_vg_iff.mpr ⟨c, rfl⟩))
      (Subgroup.mem_sup_right (mem_zpowers_e5g_iff.mpr ⟨t, rfl⟩))
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (((Commute.refl vg).zpow_left n).eq)
  · exact le_trans (Subgroup.zpowers_le.mpr e5g_mem_center)
      (Subgroup.center_le_centralizer _)

/-! ### `Z₂(S)` is the `e₄`–`e₅` plane, and `T = C_S(Z₂(S))` is the hyperplane
`{x₀ = 0}` -/

/-- An element of the `e₄`–`e₅` plane commutes with everything up to an explicit
central `e₅`-correction (placed on the *left*, so that the group commutator is
literally the correction).  This is the single-depth identity that puts the plane
inside `Z₂(S)` without expanding any four-deep BCH composition. -/
theorem plane_mul_comm {x : Q6} (y : Q6) (h0 : x.co 0 = 0) (h1 : x.co 1 = 0)
    (h2 : x.co 2 = 0) (h3 : x.co 3 = 0) :
    x * y = (⟨(-30 * x.co 4 * y.co 0) • e5⟩ : Q6) * (y * x) := by
  ext1
  rw [co_mul, co_mul, co_mul, smul_e5_gmul]
  funext k
  fin_cases k <;> simp [gmul, e5, h0, h1, h2, h3] <;> ring

/-- The `e₄`–`e₅` plane lies in `Z₂(S)`: its commutator with anything is the
central correction of `plane_mul_comm`. -/
theorem plane_mem_upperCentralSeries_two {x : Q6} (h0 : x.co 0 = 0) (h1 : x.co 1 = 0)
    (h2 : x.co 2 = 0) (h3 : x.co 3 = 0) :
    x ∈ Subgroup.upperCentralSeries Q6 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
  intro y
  rw [Subgroup.upperCentralSeries_one, mem_center_iff]
  refine ⟨-30 * x.co 4 * y.co 0, ?_⟩
  have hxyc : ⁅x, y⁆ = x * y * (y * x)⁻¹ := by
    rw [commutatorElement_def, mul_inv_rev, mul_assoc (x * y)]
  rw [hxyc, plane_mul_comm y h0 h1 h2 h3, mul_inv_cancel_right]

/-- **`Z₂(S)` upper bound**: coordinates `0`–`3` of any element of `Z₂(S)` vanish.
(The commutator with `a` pins `x₁`, the one with `b` pins `x₀`, `x₂`, `x₃`.) -/
theorem upperCentralSeries_two_le_plane {x : Q6}
    (hx : x ∈ Subgroup.upperCentralSeries Q6 2) :
    x.co 0 = 0 ∧ x.co 1 = 0 ∧ x.co 2 = 0 ∧ x.co 3 = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff] at hx
  have hx' : ∀ y : Q6, ⁅x, y⁆ ∈ Subgroup.center Q6 := by
    intro y
    have := hx y
    rwa [Subgroup.upperCentralSeries_one] at this
  obtain ⟨tA, hA⟩ := mem_center_iff.mp (hx' ag)
  obtain ⟨tB, hB⟩ := mem_center_iff.mp (hx' bg)
  have hA2 := congrFun hA 2
  have hB2 := congrFun hB 2
  have hB3 := congrFun hB 3
  have hB4 := congrFun hB 4
  simp [commutatorElement_def, gmul, eA, eB, e5] at hA2 hB2 hB3 hB4
  have hx1 : x.co 1 = 0 := by
    have hh : (2 : K) * x.co 1 = 0 := by linear_combination -hA2
    exact (mul_eq_zero.mp hh).resolve_left (by decide)
  have hx0 : x.co 0 = 0 := by
    have hh : (2 : K) * x.co 0 = 0 := by linear_combination hB2
    exact (mul_eq_zero.mp hh).resolve_left (by decide)
  rw [hx0] at hB3
  have hx2 : x.co 2 = 0 := by
    have hh : (6 : K) * x.co 2 = 0 := by linear_combination -hB3
    exact (mul_eq_zero.mp hh).resolve_left (by decide)
  rw [hx0, hx1, hx2] at hB4
  have hx3 : x.co 3 = 0 := by
    have hh : (2 : K) * x.co 3 = 0 := by linear_combination -hB4
    exact (mul_eq_zero.mp hh).resolve_left (by decide)
  exact ⟨hx0, hx1, hx2, hx3⟩

/-- **`T = C_S(Z₂(S))` is exactly the hyperplane `{x | x₀ = 0}`** — the group-level
form of Tier 1's `memT_iff`.  The index-`p` clause of Proposition E.4 survives
(this is a hyperplane); it is the abelian clause that fails. -/
theorem mem_centralizer_upperCentralSeries_two_iff {x : Q6} :
    x ∈ Subgroup.centralizer
        ((Subgroup.upperCentralSeries Q6 2 : Subgroup Q6) : Set Q6) ↔ x.co 0 = 0 := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have he4 : e4g ∈ Subgroup.upperCentralSeries Q6 2 :=
      plane_mem_upperCentralSeries_two (by decide) (by decide) (by decide) (by decide)
    have hpm := plane_mul_comm (x := e4g) x (by decide) (by decide) (by decide) (by decide)
    rw [h e4g he4] at hpm
    have h1 : (⟨(-30 * e4g.co 4 * x.co 0) • e5⟩ : Q6) = 1 :=
      right_eq_mul.mp hpm
    have h5 := congrFun (congrArg Q6.co h1) 5
    simp [e5, co_one] at h5
    rcases h5 with h5 | h5
    · exact absurd h5 (by decide)
    · exact h5
  · intro h0 z hz
    obtain ⟨z0, z1, z2, z3⟩ := upperCentralSeries_two_le_plane hz
    have hzx := plane_mul_comm (x := z) x z0 z1 z2 z3
    rw [h0, mul_zero, zero_smul] at hzx
    rw [show (⟨(0 : V)⟩ : Q6) = 1 from rfl, one_mul] at hzx
    exact hzx

/-- **The abelian clause of Proposition E.4 fails in the Lazard group `S`**:
`T = C_S(Z₂(S))` contains `b` and `e₂`, which do not commute.  This is the
group-level heart of the refutation; the `RegularOperatorSetup` instantiation
(WP4–5, issue 3027) plugs it into the repo's E.4 statement verbatim. -/
theorem centralizer_upperCentralSeries_two_not_abelian :
    ¬ IsMulCommutative
        ↥(Subgroup.centralizer
          ((Subgroup.upperCentralSeries Q6 2 : Subgroup Q6) : Set Q6)) := by
  intro habel
  have hb : bg ∈ Subgroup.centralizer
      ((Subgroup.upperCentralSeries Q6 2 : Subgroup Q6) : Set Q6) :=
    mem_centralizer_upperCentralSeries_two_iff.mpr (by decide)
  have he : e2g ∈ Subgroup.centralizer
      ((Subgroup.upperCentralSeries Q6 2 : Subgroup Q6) : Set Q6) :=
    mem_centralizer_upperCentralSeries_two_iff.mpr (by decide)
  have := habel.is_comm.comm ⟨bg, hb⟩ ⟨e2g, he⟩
  exact bg_e2g_not_commute (by simpa [Subtype.ext_iff] using this)

end OddOrder.BG.AppE.Filiform
