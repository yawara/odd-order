/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S04_SmallRankBasic
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.GroupTheory.HallCollection
import OddOrder.GroupTheory.HallPetresco
import OddOrder.GroupTheory.RegularPGroup
import OddOrder.GroupTheory.OmegaSubgroup
import OddOrder.GroupTheory.SubgroupInAmbient

/-!
# BG Appendix E: Further Results of Feit and Thompson

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, pp. 157--164.

Appendix E records Philip Hall's commutator collection formula (E.1), its
regular-`p`-group consequences (E.2), the 1991 Feit--Thompson results on a
regular operator action on a `p`-group (E.3, E.4), and a maximal-subgroup
application (E.5).

## Honesty status

Every statement below is a genuine group-theoretic assertion: there are no
opaque `Prop` fields and no self-carried `_holds` proofs anywhere in this file.
Some of the deep results are still `sorry`-ed, but the sorries sit under
**book-strength statements**, so closing them is real mathematics rather than
packaging.  Per-result status:

| Result | Status |
|---|---|
| E.1 general (`hallCollection`) | **proved** (Mann; `GroupTheory/HallPetresco.lean`) |
| E.1 class `≤ 3` (`hallCollection_of_class_le_three`) | **proved, sorry-free** (all `n`) |
| E.1 class `≤ 2` (`hallCollection_of_class_le_two`) | **proved** (subsumed by the above) |
| E.1 general framework | `OddOrder/GroupTheory/HallCollection.lean`, **sorry-free** |
| E.2 Step 1 (`GroupTheory.pow_mul_pow_eq_pow_of_commutator_exponent`) | **proved** (general) |
| E.2(a) (`omega_pow_eq_one_of_lowerCentralSeries_eq_bot`) | **proved** (`IsPGroup` dropped) |
| E.2(a) class `≤ 2` | already in repo: `GroupTheory.Omega.pow_eq_one_of_class_le_two` |
| E.2(b) (`pow_mul_of_commutator_le_omega`) | **proved** from E.2(a) + Step 1 |
| E.2(b) class `≤ 2` (`pow_mul_of_class_le_two`) | **proved, sorry-free** |
| E.3(a) (`card_A_dvd_half_p_sub_one`) | **proved, sorry-free** |
| E.3(b) `C_R(R₀) = R₀ × R₁` structure | **proved** (abelian, order `p·|R₁|`, rank `≤ 2`) |
| E.3(b) Step 2, `R₀ ⊄ S'` (`not_le_derivedInG`) | **proved, sorry-free**, both branches |
| E.3(b) Step 2, `S` narrow / `\|Ω₁(Z(S))\| = p` / `\|S:T\| = p` | **proved, sorry-free** |
| E.3(b) Step 2, (E.4)--(E.7) | **proved, sorry-free** (chain, `\|T\| = pⁿ`, `\|S/S'\| = p²`) |
| E.3(b) second + third clause | **proved** from Step 2 + first clause |
| E.3(b) first clause, E.3(c)(d), E.4, E.5 | honest statements, `sorry` |
-/

namespace OddOrder.BG.AppE

open OddOrder.GroupTheory
open scoped commutatorElement Pointwise

/-! ## E.1: Philip Hall's commutator collection formula

BG indexes the lower central series as `G = G₁ ⊇ G₂ ⊇ ⋯`, so the book's `Gᵣ` is
mathlib's `lowerCentralSeries G (r - 1)`.

The product `c₂ ^ e₂ ⋯ cₙ ^ eₙ` is *ordered*, so it is spelled as a `List.prod`
over `List.range' 2 (n - 1) = [2, 3, …, n]` rather than a `Finset.prod` (which
would require commutativity). -/

section HallCollection

variable {G : Type*} [Group G]

/-- The ordered product `c₂ ^ e₂ ⋯ cₙ ^ eₙ` with `eᵣ = C(n, r)`, i.e. the
right-hand tail of BG Theorem E.1.

This is BG's name for the general ordered tail
`OddOrder.GroupTheory.hallTail` (`OddOrder/GroupTheory/HallCollection.lean`),
which carries the reusable collapse/absorption lemmas; the two are definitionally
equal, and the App.E-facing lemmas below are stated for this name. -/
def collectionTail (c : ℕ → G) (n : ℕ) : G := hallTail c n

@[simp] theorem collectionTail_zero (c : ℕ → G) : collectionTail c 0 = 1 := by
  simp [collectionTail]

@[simp] theorem collectionTail_one (c : ℕ → G) : collectionTail c 1 = 1 := by
  simp [collectionTail]

/-- **BG Theorem E.1** (Philip Hall's collection formula).  Let
`G = G₁ ⊇ G₂ ⊇ ⋯` be the lower central series of `G`, take `x y : G` and a
positive integer `n`, and let `eᵣ = C(n, r)`.  Then there are elements
`cᵣ ∈ Gᵣ` for `r = 2, 3, …, n` such that

`xⁿ yⁿ = (x y)ⁿ c₂^{e₂} ⋯ cₙ^{eₙ}`.

**Proved** (2026-07-20), by Mann's form of Hall's collecting process — see
`OddOrder/GroupTheory/HallPetresco.lean` for the general `m`-generator statement
`OddOrder.GroupTheory.HallPetresco.exists_hallPetresco`, of which this is the
two-generator case.  BG gives no proof, citing Suzuki, *Group Theory II*,
pp. 37--41 and Huppert, *Endliche Gruppen I*, pp. 315--318; the argument
formalised here is the short one of Dixon--du Sautoy--Mann--Segal, *Analytic
Pro-p Groups*, 2nd ed., Appendix A (contributed by A. Mann).

The idea is to *de-specialise*: instead of collecting `xⁿ yⁿ` directly — which
forces one to count how often each commutator appears, and hence to know that
the collection coefficients are `ℤ`-polynomials in `n` divisible by `C(n,k)` —
one gives each of the `n` copies of a generator its own letter, indexed by a
*slot*.  The expanded word is collected **once**, into blocks indexed by the set
of slots each factor touches; substituting the assignment attached to a slot set
`A` (which kills the letters outside `A`) shows that a block's value depends only
on `|A|`, and the binomial coefficient `C(n,k)` appears simply as the number of
`k`-element subsets of an `n`-element set.  In particular **no free nilpotent
groups, no basic-commutator bases and no Hall polynomials are needed**.

Sharper statements proved separately below: `hallCollection_of_class_le_two` and
`hallCollection_of_class_le_three` give the same conclusion for *all* `n` at once
with explicit `cᵣ`, for nilpotence class `≤ 2`, resp. `≤ 3`. -/
theorem hallCollection (x y : G) (n : ℕ) :
    ∃ c : ℕ → G,
      (∀ r, 2 ≤ r → r ≤ n → c r ∈ (⊤ : Subgroup G).lowerCentralSeries (r - 1)) ∧
      x ^ n * y ^ n = (x * y) ^ n * collectionTail c n := by
  rcases n with _ | m
  · exact ⟨fun _ => 1, fun r hr2 hr0 => absurd hr0 (by omega), by simp⟩
  obtain ⟨τ, hmem, hτ1, hprod⟩ :=
    OddOrder.GroupTheory.HallPetresco.exists_hallPetresco (G := G) [x, y] (Nat.le_add_left 1 m)
  refine ⟨τ, fun r hr2 hrn => hmem r (by omega) hrn, ?_⟩
  have hτ : τ 1 = x * y := by simpa using hτ1
  have hlhs : (([x, y] : List G).map fun g => g ^ (m + 1)).prod = x ^ (m + 1) * y ^ (m + 1) := by
    simp
  rw [hlhs] at hprod
  rw [hprod, List.range'_succ, List.map_cons, List.prod_cons, hτ, Nat.choose_one_right]
  rfl

/-- **BG Theorem E.1, class-`≤ 2` case** (proved, sorry-free).  When `G` has
nilpotence class at most `2` every `cᵣ` with `r ≥ 3` may be taken trivial, and
the single surviving term is `c₂ = ⁅y, x⁆⁻¹ ∈ G₂ = G'` carrying the exponent
`C(n, 2) = n(n-1)/2`.

This repackages the repo's class-`≤ 2` collection identity
`OddOrder.GroupTheory.mul_pow_eq_commutator_pow_mul_of_class_le_two`
(Gorenstein, *Finite Groups*, eq. (3.1)) into Hall's shape. -/
theorem hallCollection_of_class_le_two
    (hcl : _root_.commutator G ≤ Subgroup.center G) (x y : G) (n : ℕ) :
    ∃ c : ℕ → G,
      (∀ r, 2 ≤ r → r ≤ n → c r ∈ (⊤ : Subgroup G).lowerCentralSeries (r - 1)) ∧
      x ^ n * y ^ n = (x * y) ^ n * collectionTail c n := by
  classical
  refine ⟨fun r => if r = 2 then ⁅y, x⁆⁻¹ else 1, ?_, ?_⟩
  · intro r hr2 _
    by_cases h : r = 2
    · subst h
      change _ ∈ (⊤ : Subgroup G).lowerCentralSeries 1
      rw [Subgroup.top_lowerCentralSeries_one]
      exact Subgroup.inv_mem _
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x))
    · simp only [if_neg h]
      exact Subgroup.one_mem _
  · have hz : ⁅y, x⁆ ∈ Subgroup.center G :=
      hcl (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x))
    have hzc : ∀ g : G, ⁅y, x⁆ * g = g * ⁅y, x⁆ :=
      fun g => (Subgroup.mem_center_iff.mp hz g).symm
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · rw [collectionTail, hallTail_eq_of_eq_one_of_three_le _ hn
        (fun r hr => if_neg (by omega : ¬ r = 2))]
      rw [if_pos (rfl : (2 : ℕ) = 2), Nat.choose_two_right]
      -- `(x*y)^n = ⁅y,x⁆^{n(n-1)/2} * x^n * y^n` with `⁅y,x⁆` central.
      have hw : Commute (⁅y, x⁆ ^ (n * (n - 1) / 2)) (x ^ n * y ^ n) :=
        Commute.pow_left (hzc (x ^ n * y ^ n)) _
      rw [mul_pow_eq_commutator_pow_mul_of_class_le_two hcl x y n, inv_pow,
        mul_assoc (⁅y, x⁆ ^ (n * (n - 1) / 2)) (x ^ n) (y ^ n), hw.eq, mul_assoc,
        mul_inv_cancel, mul_one]

/-- The abstract shape of the class-`≤ 3` tail identity.  With `C = ⁅y, x⁆` and
`d₁, d₂` the two weight-`3` commutators (central under `γ₄ = 1`), the collected
tail `c₂ ^ m c₃ ^ k` with `c₂ = C⁻¹ e`, `c₃ = e`, `e = (d₁ d₂²)⁻¹` is exactly the
inverse of the class-`≤ 3` collection factor.

The point is the Pascal identity `m + k = C(n,2) + C(n,3) = C(n+1,3)`: the
weight-`3` exponent produced by the collecting process is `C(n+1,3)`, and it
splits as the *sum* of the two Hall exponents `C(n,2)` (contributed by the
weight-`3` part of `c₂`) and `C(n,3)` (contributed by `c₃`).  This is what makes
Hall's binomial exponents come out right at weight `3`. -/
private theorem class_three_tail_aux {K : Type*} [Group K] (C d₁ d₂ : K) (m k : ℕ)
    (h₁ : ∀ g : K, Commute d₁ g) (h₂ : ∀ g : K, Commute d₂ g) :
    (C⁻¹ * (d₁ * d₂ ^ 2)⁻¹) ^ m * ((d₁ * d₂ ^ 2)⁻¹) ^ k
      = (C ^ m * d₁ ^ (m + k) * d₂ ^ (2 * (m + k)))⁻¹ := by
  have hcomm : ∀ g : K, Commute (d₁ * d₂ ^ 2)⁻¹ g := fun g =>
    (Commute.mul_left (h₁ g) ((h₂ g).pow_left 2)).inv_left
  have hsplit : (d₁ * d₂ ^ 2) ^ (m + k) = d₁ ^ (m + k) * d₂ ^ (2 * (m + k)) := by
    rw [(h₁ (d₂ ^ 2)).mul_pow, ← pow_mul]
  calc (C⁻¹ * (d₁ * d₂ ^ 2)⁻¹) ^ m * ((d₁ * d₂ ^ 2)⁻¹) ^ k
      = C⁻¹ ^ m * ((d₁ * d₂ ^ 2)⁻¹) ^ m * ((d₁ * d₂ ^ 2)⁻¹) ^ k := by
        rw [(hcomm C⁻¹).symm.mul_pow]
    _ = C⁻¹ ^ m * ((d₁ * d₂ ^ 2)⁻¹) ^ (m + k) := by rw [mul_assoc, ← pow_add]
    _ = ((d₁ * d₂ ^ 2)⁻¹) ^ (m + k) * C⁻¹ ^ m := ((hcomm (C⁻¹ ^ m)).pow_left (m + k)).eq.symm
    _ = (C ^ m * (d₁ * d₂ ^ 2) ^ (m + k))⁻¹ := by
        rw [mul_inv_rev (C ^ m) ((d₁ * d₂ ^ 2) ^ (m + k)), inv_pow, inv_pow]
    _ = (C ^ m * d₁ ^ (m + k) * d₂ ^ (2 * (m + k)))⁻¹ := by rw [hsplit, mul_assoc]

/-- **BG Theorem E.1, class-`≤ 3` case** (proved, sorry-free).  If `γ₄(G) = 1`
(mathlib: `lowerCentralSeries ⊤ 3 = ⊥`), then Hall's collection formula holds for
every `x, y` and every `n`, with

`c₂ = ⁅y, x⁆⁻¹ (d₁ d₂²)⁻¹ ∈ G₂`,  `c₃ = (d₁ d₂²)⁻¹ ∈ G₃`,  `cᵣ = 1` for `r ≥ 4`,

where `d₁ = ⁅⁅y, x⁆, x⁆` and `d₂ = ⁅⁅y, x⁆, y⁆` are the two weight-`3`
commutators (central, since `γ₄ = 1`).

This strictly generalizes `hallCollection_of_class_le_two`.  The proof runs the
repo's class-`≤ 3` collection identity
`OddOrder.BG.Ch1.S04.mul_pow_eq_collect_of_triple_central`
(BG Proposition 4.3(a), `(4.4)`), whose weight-`3` exponents are `C(n+1,3)` and
`2 C(n+1,3)`, and converts them into Hall's shape by the Pascal splitting
`C(n+1,3) = C(n,2) + C(n,3)` (`class_three_tail_aux`).

Note that this is genuinely a *class* restriction and not an `n` restriction: it
gives Theorem E.1 for all `n` at once, for every group of nilpotence class
`≤ 3`. -/
theorem hallCollection_of_class_le_three
    (hγ : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥) (x y : G) (n : ℕ) :
    ∃ c : ℕ → G,
      (∀ r, 2 ≤ r → r ≤ n → c r ∈ (⊤ : Subgroup G).lowerCentralSeries (r - 1)) ∧
      x ^ n * y ^ n = (x * y) ^ n * collectionTail c n := by
  classical
  -- Weight bookkeeping: `⁅a,b⁆ ∈ γ₂`, `⁅⁅a,b⁆,c⁆ ∈ γ₃`, and `γ₄ = 1`.
  have hmem2 : ∀ a b : G, ⁅a, b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
    intro a b
    rw [Subgroup.top_lowerCentralSeries_one]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  have hmem3 : ∀ a b z : G, ⁅⁅a, b⁆, z⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    fun a b z => Subgroup.commutator_mem_commutator (hmem2 a b) (Subgroup.mem_top z)
  have hc4 : ∀ a b z w : G, ⁅⁅⁅a, b⁆, z⁆, w⁆ = 1 := by
    intro a b z w
    have hmem : ⁅⁅⁅a, b⁆, z⁆, w⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      Subgroup.commutator_mem_commutator (hmem3 a b z) (Subgroup.mem_top w)
    rwa [hγ, Subgroup.mem_bot] at hmem
  have hc3 : ∀ a b z : G, ⁅⁅a, b⁆, z⁆ ∈ Subgroup.center G := fun a b z =>
    Subgroup.mem_center_iff.2 fun g =>
      ((commutatorElement_eq_one_iff_commute.1 (hc4 a b z g)).symm).eq
  -- The two central weight-`3` commutators and the collected weight-`3` element `e`.
  have hd₁ : ∀ g : G, Commute ⁅⁅y, x⁆, x⁆ g :=
    fun g => (Subgroup.mem_center_iff.mp (hc3 y x x) g).symm
  have hd₂ : ∀ g : G, Commute ⁅⁅y, x⁆, y⁆ g :=
    fun g => (Subgroup.mem_center_iff.mp (hc3 y x y) g).symm
  have he_mem : (⁅⁅y, x⁆, x⁆ * ⁅⁅y, x⁆, y⁆ ^ 2)⁻¹ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    Subgroup.inv_mem _ (Subgroup.mul_mem _ (hmem3 y x x) (Subgroup.pow_mem _ (hmem3 y x y) 2))
  refine ⟨fun r => if r = 2 then ⁅y, x⁆⁻¹ * (⁅⁅y, x⁆, x⁆ * ⁅⁅y, x⁆, y⁆ ^ 2)⁻¹
      else if r = 3 then (⁅⁅y, x⁆, x⁆ * ⁅⁅y, x⁆, y⁆ ^ 2)⁻¹ else 1, ?_, ?_⟩
  · -- Memberships: `c₂ ∈ γ₂`, `c₃ ∈ γ₃`, `cᵣ = 1` otherwise.
    intro r hr2 _
    by_cases h2 : r = 2
    · subst h2
      simp only [reduceIte]
      refine Subgroup.mul_mem _ (Subgroup.inv_mem _ (hmem2 y x)) ?_
      exact (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega) he_mem
    · by_cases h3 : r = 3
      · subst h3
        exact he_mem
      · simp only [if_neg h2, if_neg h3]
        exact Subgroup.one_mem _
  · rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · -- Collapse the tail to its weight-`2` and weight-`3` factors.
      rw [collectionTail, hallTail_eq_of_eq_one_of_four_le _ hn
        (fun r hr => by rw [if_neg (by omega : ¬ r = 2), if_neg (by omega : ¬ r = 3)])]
      rw [if_pos (rfl : (2 : ℕ) = 2), if_neg (by norm_num : ¬ (3 : ℕ) = 2),
        if_pos (rfl : (3 : ℕ) = 3)]
      -- Run BG (4.4) and match exponents by Pascal `C(n+1,3) = C(n,2) + C(n,3)`.
      rw [OddOrder.BG.Ch1.S04.mul_pow_eq_collect_of_triple_central hc3 hc4 x y n,
        Nat.choose_succ_succ n 2]
      have hkey := class_three_tail_aux ⁅y, x⁆ ⁅⁅y, x⁆, x⁆ ⁅⁅y, x⁆, y⁆
        (n.choose 2) (n.choose 3) hd₁ hd₂
      calc x ^ n * y ^ n = x ^ n * y ^ n * 1 := (mul_one _).symm
        _ = x ^ n * y ^ n *
              ((⁅y, x⁆ ^ n.choose 2 * ⁅⁅y, x⁆, x⁆ ^ (n.choose 2 + n.choose 3)
                  * ⁅⁅y, x⁆, y⁆ ^ (2 * (n.choose 2 + n.choose 3)))
                * ((⁅y, x⁆⁻¹ * (⁅⁅y, x⁆, x⁆ * ⁅⁅y, x⁆, y⁆ ^ 2)⁻¹) ^ n.choose 2
                  * ((⁅⁅y, x⁆, x⁆ * ⁅⁅y, x⁆, y⁆ ^ 2)⁻¹) ^ n.choose 3)) := by
              rw [hkey, mul_inv_cancel]
        _ = x ^ n * y ^ n * ⁅y, x⁆ ^ n.choose 2
              * ⁅⁅y, x⁆, x⁆ ^ (n.choose 2 + n.choose 3)
              * ⁅⁅y, x⁆, y⁆ ^ (2 * (n.choose 2 + n.choose 3))
              * ((⁅y, x⁆⁻¹ * (⁅⁅y, x⁆, x⁆ * ⁅⁅y, x⁆, y⁆ ^ 2)⁻¹) ^ n.choose 2
                  * ((⁅⁅y, x⁆, x⁆ * ⁅⁅y, x⁆, y⁆ ^ 2)⁻¹) ^ n.choose 3) := by
              simp only [mul_assoc]

end HallCollection

/-! ## E.2: regular `p`-group consequences -/

section RegularPGroup

variable {R : Type*} [Group R]

/-! ### Step 1 lives in `OddOrder/GroupTheory/RegularPGroup.lean`

BG's Step 1 — "class `< p` and `R'` of exponent `p` imply that `x ↦ x^p` is a
homomorphism" — is not one of the book's numbered results but an internal step,
and it is a statement about arbitrary groups.  It is therefore proved once, in
general form, as
`OddOrder.GroupTheory.pow_mul_pow_eq_pow_of_commutator_exponent`, directly from
Hall's formula; the results below cite it rather than restating it.
-/

/-- **BG Proposition E.2(a)** (proved).  If `R` has nilpotence class at most
`p - 1` then `Ω₁(R)` has exponent `1` or `p`.

Proof: by `OddOrder.GroupTheory.pow_mul_eq_one_of_class_lt` the elements of order
dividing `p` are closed under multiplication (BG's Step 2, an induction on `|R|`
using a maximal subgroup containing `⟨y⟩`), so they already form a subgroup and
`Ω₁(R)` — the subgroup they generate — consists of exactly those elements.

⚠ **Generalised**: BG state this for `p`-groups, but the hypothesis is never
used — finiteness together with `γ_p(R) = 1` suffices — so the `IsPGroup`
assumption has been dropped. -/
theorem omega_pow_eq_one_of_lowerCentralSeries_eq_bot [Finite R] {p : ℕ} [hp : Fact p.Prime]
    (hgamma : (⊤ : Subgroup R).lowerCentralSeries (p - 1) = ⊥)
    {g : R} (hg : g ∈ Omega R p 1) : g ^ p = 1 :=
  OddOrder.GroupTheory.Omega.pow_eq_one_of_mul_closed
    (fun x y hx hy =>
      OddOrder.GroupTheory.pow_mul_eq_one_of_class_lt hp.out (Nat.card R + 1) R
        (by omega) hgamma x y hx hy) hg

/-- **BG Proposition E.2(b).**  If `R` is a `p`-group of nilpotence class at most
`p - 1` and `R' ≤ Ω₁(R)`, then `x ↦ x ^ p` is a homomorphism.

**Status: proved, sorry-free** — exactly BG's derivation ("(b) will follow from
(a) and Step 1").

⚠ **Generalised**: as for (a), the `IsPGroup` hypothesis is unused and has been
dropped. -/
theorem pow_mul_of_commutator_le_omega [Finite R] {p : ℕ} [hp : Fact p.Prime]
    (hgamma : (⊤ : Subgroup R).lowerCentralSeries (p - 1) = ⊥)
    (hR' : _root_.commutator R ≤ Omega R p 1) (x y : R) :
    (x * y) ^ p = x ^ p * y ^ p :=
  (OddOrder.GroupTheory.pow_mul_pow_eq_pow_of_commutator_exponent hp.out hgamma
    (fun _ hg => omega_pow_eq_one_of_lowerCentralSeries_eq_bot hgamma (hR' hg)) x y).symm

/-- **BG Proposition E.2(b), class-`≤ 2` case** (proved, sorry-free).  For odd `p`
and `R` of nilpotence class at most `2` with `R' ≤ Ω₁(R)`, the `p`-power map is a
homomorphism.

Class `≤ 2` is the `p = 3` instance of "class `≤ p - 1`", and for larger odd `p`
it is the first nontrivial case; the proof is Step 1 specialised to the repo's
class-`≤ 2` collection identity, where the only surviving collected term is
`⁅y, x⁆ ^ {p(p-1)/2}` and `p ∣ p(p-1)/2` because `p` is odd. -/
theorem pow_mul_of_class_le_two {p : ℕ} (hp_odd : Odd p)
    (hcl : _root_.commutator R ≤ Subgroup.center R)
    (hR' : _root_.commutator R ≤ Omega R p 1) (x y : R) :
    (x * y) ^ p = x ^ p * y ^ p := by
  have hmem : ⁅y, x⁆ ∈ _root_.commutator R :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x)
  have hzp : ⁅y, x⁆ ^ p = 1 :=
    Omega.pow_eq_one_of_class_le_two hp_odd hcl (hR' hmem)
  have h2 : 2 ∣ (p - 1) := by obtain ⟨m, hm⟩ := hp_odd; omega
  have hk : p * (p - 1) / 2 = p * ((p - 1) / 2) := Nat.mul_div_assoc p h2
  rw [mul_pow_eq_commutator_pow_mul_of_class_le_two hcl x y p, hk, pow_mul, hzp,
    one_pow, one_mul]

end RegularPGroup

/-! ## E.3 / E.4: the 1991 Feit--Thompson regular-operator results -/

section RegularOperator

open OddOrder.Isaacs.Ch03 OddOrder.Isaacs.Ch04

variable {R B : Type*} [Group R] [Group B]

/-- `Φ(H)` transported back into the ambient group along `H.subtype`. -/
def frattiniInG {G : Type*} [Group G] (H : Subgroup G) : Subgroup G :=
  (frattini ↥H).map H.subtype

/-- **BG Theorem E.3, standing hypotheses** (Feit and Thompson, 1991).

`p` and `q` are distinct odd primes, `R` is a `p`-group, `R₀` and `R₁` are
nonidentity subgroups of `R`, `B` is an operator group on `R` and `A ≤ B`, with
`p ∤ |B|`, `|A| = q`, `|R₀| = p`, `R₁` cyclic, `C_R(R₀) = R₀ × R₁`, and `A` fixes
`R₀` and acts regularly on `R`.

Every field is a genuine proposition about the data; there are no opaque `Prop`
placeholders.  The operator action is the repo's standard encoding
`act : B →* MulAut R` (see `OddOrder.Isaacs.Ch03.IsAInvariant`), and "acts
regularly" is BG's `C_R(α) = 1` for all `α ∈ A^#`, spelled pointwise. -/
structure RegularOperatorSetup (R B : Type*) [Group R] [Group B] (p q : ℕ) where
  /-- `p` is prime. -/
  p_prime : p.Prime
  /-- `p` is odd. -/
  p_odd : Odd p
  /-- `q` is prime. -/
  q_prime : q.Prime
  /-- `q` is odd. -/
  q_odd : Odd q
  /-- `p` and `q` are distinct. -/
  p_ne_q : p ≠ q
  /-- `R` is a `p`-group. -/
  R_pGroup : IsPGroup p R
  /-- `B` acts on `R` as a group of operators. -/
  act : B →* MulAut R
  /-- `p` does not divide `|B|`. -/
  p_not_dvd_card_B : ¬ p ∣ Nat.card B
  /-- The distinguished subgroup `A ≤ B`. -/
  A : Subgroup B
  /-- `|A| = q`. -/
  A_card : Nat.card ↥A = q
  /-- The distinguished subgroup `R₀ ≤ R`. -/
  R₀ : Subgroup R
  /-- `|R₀| = p`. -/
  R₀_card : Nat.card ↥R₀ = p
  /-- The distinguished subgroup `R₁ ≤ R`. -/
  R₁ : Subgroup R
  /-- `R₁ ≠ 1`. -/
  R₁_ne_bot : R₁ ≠ ⊥
  /-- `R₁` is cyclic. -/
  R₁_cyclic : IsCyclic ↥R₁
  /-- `C_R(R₀) = R₀ R₁` (half of `C_R(R₀) = R₀ × R₁`). -/
  centralizer_eq : Subgroup.centralizer (R₀ : Set R) = R₀ ⊔ R₁
  /-- `R₀ ∩ R₁ = 1` (the other half of `C_R(R₀) = R₀ × R₁`;
  `R₁` centralizes `R₀` because `R₁ ≤ R₀ ⊔ R₁ = C_R(R₀)`). -/
  R₀_disjoint_R₁ : Disjoint R₀ R₁
  /-- `A` fixes `R₀` setwise. -/
  A_fixes_R₀ : ∀ a ∈ A, (act a) • R₀ = R₀
  /-- `A` acts regularly on `R`: `C_R(α) = 1` for every `α ∈ A^#`. -/
  A_regular : ∀ a ∈ A, a ≠ 1 → ∀ x : R, act a x = x → x = 1

variable {p q : ℕ}

/-- `R₀` is `A`-invariant in the repo's `IsAInvariant` sense. -/
theorem RegularOperatorSetup.isAInvariant_R₀ (hyp : RegularOperatorSetup R B p q) :
    IsAInvariant (hyp.act.comp hyp.A.subtype) hyp.R₀ :=
  fun a => hyp.A_fixes_R₀ a.val a.property

/-- **BG Theorem E.3(a)** (proved, sorry-free): `q` divides `(p - 1)/2`.

BG's Step 1: `A` acts regularly on `R`, hence regularly on `R₀`, which has order
`p`; so the induced map `A → Aut(R₀) ≅ C_{p-1}` is injective and `q ∣ p - 1`.
Since `p` and `q` are odd, `q ∣ (p-1)/2` (and in particular `p ≥ 2q + 1 ≥ 7`). -/
theorem RegularOperatorSetup.card_A_dvd_half_p_sub_one [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) : q ∣ (p - 1) / 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  -- The restricted action of `A` on `R₀`.
  set ψ : ↥hyp.A →* MulAut ↥hyp.R₀ :=
    OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hyp.isAInvariant_R₀ with hψ
  -- `R₀` is nontrivial, since `|R₀| = p ≥ 2`.
  have hR₀ne : hyp.R₀ ≠ ⊥ := by
    intro h
    have hc := hyp.R₀_card
    rw [h, Subgroup.card_bot] at hc
    have := hyp.p_prime.one_lt
    omega
  haveI hnt : Nontrivial ↥hyp.R₀ := (Subgroup.nontrivial_iff_ne_bot _).mpr hR₀ne
  -- `ψ` is injective: a nontrivial `a ∈ A` acting trivially on `R₀` would fix a
  -- nonidentity element of `R`, contradicting regularity.
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    by_contra hane
    obtain ⟨h, hh⟩ := exists_ne (1 : ↥hyp.R₀)
    have hfix : hyp.act a.val h.val = h.val := by
      have := congrArg (fun (f : MulAut ↥hyp.R₀) => (f h).val) ha
      simpa [hψ, OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom_apply_val] using this
    have hval : (h : R) = 1 :=
      hyp.A_regular a.val a.property (by simpa using hane) h.val hfix
    exact hh (Subtype.ext (by simpa using hval))
  -- `q = |A|` divides `|Aut R₀| = φ(p) = p - 1`.
  haveI : IsCyclic ↥hyp.R₀ := isCyclic_of_prime_card hyp.R₀_card
  have hdvd : q ∣ p - 1 := by
    have h1 : Nat.card ↥hyp.A ∣ Nat.card (MulAut ↥hyp.R₀) :=
      Subgroup.card_dvd_of_injective ψ hinj
    rwa [hyp.A_card, IsCyclic.card_mulAut ↥hyp.R₀, hyp.R₀_card,
      Nat.totient_prime hyp.p_prime] at h1
  -- `q` is odd and `p - 1` is even, so `q ∣ (p-1)/2`.
  obtain ⟨m, hm⟩ := hyp.p_odd
  have hhalf : p - 1 = 2 * m := by omega
  have hcop : Nat.Coprime q 2 := hyp.q_odd.coprime_two_right
  have : q ∣ m := hcop.dvd_of_dvd_mul_left (by rwa [hhalf] at hdvd)
  simpa [hhalf] using this

/-! ### The structure of `C_R(R₀) = R₀ × R₁`

BG's Step 2 opens with the single sentence *"Since `C_R(R₀) = R₀ × R₁` we have
`R₀ ∩ Z = 1`"* (`Z = Ω₁(Z(S))` for the maximal `A`-invariant subgroup `S` of exponent
`p`).  Unpacked, the argument is: `|R₀| = p` forces `R₀ ⊓ Z ∈ {1, R₀}`, and `R₀ ≤ Z`
would put `S` inside `C_R(R₀)`, whose `p`-rank is at most `2` — contradicting the
`r(S) ≥ 3` obtained just before.  The three lemmas below supply the rank bound. -/

/-- `R₀` centralizes `R₁`.

This is the symmetric half of the setup datum `C_R(R₀) = R₀ R₁`: every `y ∈ R₁` lies
in `R₀ ⊔ R₁ = C_R(R₀)`, hence commutes with every `x ∈ R₀`. -/
theorem RegularOperatorSetup.R₀_le_centralizer_R₁ (hyp : RegularOperatorSetup R B p q) :
    hyp.R₀ ≤ Subgroup.centralizer (hyp.R₁ : Set R) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyC : y ∈ Subgroup.centralizer (hyp.R₀ : Set R) := by
    rw [hyp.centralizer_eq]
    exact (le_sup_right : hyp.R₁ ≤ hyp.R₀ ⊔ hyp.R₁) hy
  exact (Subgroup.mem_centralizer_iff.mp hyC x hx).symm

/-- **`C_R(R₀) = R₀ × R₁` is abelian.**

`R₀` has order `p`, hence is cyclic, and `R₁` is cyclic by hypothesis; the two
centralize each other, so their join is abelian
(`Ch4.S15.isMulCommutative_sup_of_le_centralizer`). -/
theorem RegularOperatorSetup.isMulCommutative_centralizer_R₀
    (hyp : RegularOperatorSetup R B p q) :
    IsMulCommutative ↥(Subgroup.centralizer (hyp.R₀ : Set R)) := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  haveI : IsCyclic ↥hyp.R₀ := isCyclic_of_prime_card hyp.R₀_card
  haveI : IsCyclic ↥hyp.R₁ := hyp.R₁_cyclic
  rw [hyp.centralizer_eq]
  exact OddOrder.BG.Ch4.S15.isMulCommutative_sup_of_le_centralizer
    IsCyclic.isMulCommutative IsCyclic.isMulCommutative hyp.R₀_le_centralizer_R₁

/-- **`|C_R(R₀)| = p · |R₁|`**, the cardinality form of the direct decomposition
`C_R(R₀) = R₀ × R₁`.

`R₀` normalizes `R₁` (it centralizes it), so the join is the set product
`↑R₀ * ↑R₁` (`Subgroup.coe_mul_of_left_le_normalizer_right`); the classical product
formula and `R₀ ∩ R₁ = 1` then give `|R₀ R₁| = |R₀| · |R₁| = p · |R₁|`. -/
theorem RegularOperatorSetup.card_centralizer_R₀ [Finite R]
    (hyp : RegularOperatorSetup R B p q) :
    Nat.card ↥(Subgroup.centralizer (hyp.R₀ : Set R)) = p * Nat.card ↥hyp.R₁ := by
  have hnorm : hyp.R₀ ≤ Subgroup.normalizer (hyp.R₁ : Set R) :=
    hyp.R₀_le_centralizer_R₁.trans (Subgroup.centralizer_le_normalizer _)
  have hcoe : (↑(hyp.R₀ ⊔ hyp.R₁) : Set R) = (hyp.R₀ : Set R) * (hyp.R₁ : Set R) :=
    Subgroup.coe_mul_of_left_le_normalizer_right hyp.R₀ hyp.R₁ hnorm
  have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card hyp.R₀ hyp.R₁
  have hinf : Nat.card ↥(hyp.R₀ ⊓ hyp.R₁) = 1 := by
    rw [disjoint_iff.mp hyp.R₀_disjoint_R₁]
    exact Subgroup.card_bot
  rw [hinf, mul_one, hyp.R₀_card] at hprod
  rw [hyp.centralizer_eq]
  exact (Nat.card_congr (Equiv.setCongr hcoe)).trans hprod

/-- **`r(C_R(R₀)) ≤ 2`.**

`C_R(R₀) = R₀ × R₁` contains the cyclic subgroup `R₁` with index `p`
(`card_centralizer_R₀`), so `pRank_le_two_of_isCyclic_of_index_le_prime` applies.

This is the rank bound behind BG's elided *"Since `C_R(R₀) = R₀ × R₁` we have
`R₀ ∩ Z = 1`"* in the proof of Theorem E.3(b). -/
theorem RegularOperatorSetup.pRank_centralizer_R₀_le_two [Finite R]
    (hyp : RegularOperatorSetup R B p q) :
    pRank ↥(Subgroup.centralizer (hyp.R₀ : Set R)) p ≤ 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  have hR₁le : hyp.R₁ ≤ Subgroup.centralizer (hyp.R₀ : Set R) := by
    rw [hyp.centralizer_eq]
    exact le_sup_right
  set K : Subgroup ↥(Subgroup.centralizer (hyp.R₀ : Set R)) :=
    hyp.R₁.subgroupOf (Subgroup.centralizer (hyp.R₀ : Set R)) with hKdef
  have hKcyc : IsCyclic ↥K :=
    (Subgroup.subgroupOfEquivOfLe hR₁le).isCyclic.mpr hyp.R₁_cyclic
  have hKcard : Nat.card ↥K = Nat.card ↥hyp.R₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₁le).toEquiv
  have hidx : K.index ≤ p := by
    have hmul := K.card_mul_index
    rw [hKcard, hyp.card_centralizer_R₀, mul_comm p] at hmul
    exact le_of_eq (Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul)
  exact pRank_le_two_of_isCyclic_of_index_le_prime hKcyc hidx

/-- **BG Theorem E.3(b), Step 2, (E.1)--(E.3)**: an exponent-`p` subgroup `S ≤ R` with
`p³ < |S|` has `r(S) ≥ 3`.

BG argues via `V ∈ SCN(S)`: `|S/V|` divides `|Aut V|` and `V` is elementary abelian
(as `exp S = p`), so `|V| ≤ p²` would force `|S/V| ≤ p` and `|S| ≤ p³`.  The repo already
records the conclusion of that argument as
`Ch1.S04.card_le_prime_cube_of_pRank_le_two_of_exponent_prime` (`r ≤ 2` and `exp = p` imply
`|·| ≤ p³`), so BG's (E.1)--(E.3) is exactly its contrapositive. -/
theorem three_le_pRank_of_prime_cube_lt_card {S : Type*} [Group S] [Finite S] {p : ℕ}
    [Fact p.Prime] (hS : IsPGroup p S) (hexp : ∀ x : S, x ^ p = 1)
    (hcard : p ^ 3 < Nat.card S) :
    3 ≤ pRank S p := by
  by_contra h
  exact absurd (OddOrder.BG.Ch1.S04.card_le_prime_cube_of_pRank_le_two_of_exponent_prime
    hS (by omega) hexp) (by omega)

/-- **BG Theorem E.3(b), Step 2**: a subgroup `S ≤ R` of `p`-rank at least `3` cannot
centralize `R₀`.

Otherwise `S ≤ C_R(R₀)`, whose `p`-rank is at most `2` (`pRank_centralizer_R₀_le_two`). -/
theorem RegularOperatorSetup.not_le_centralizer_R₀_of_three_le_pRank [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hS : 3 ≤ pRank ↥S p) :
    ¬ S ≤ Subgroup.centralizer (hyp.R₀ : Set R) := by
  intro hle
  have hmono : pRank ↥S p ≤ pRank ↥(Subgroup.centralizer (hyp.R₀ : Set R)) p :=
    pRank_le_of_injective (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have := hyp.pRank_centralizer_R₀_le_two
  omega

/-- **BG Theorem E.3(b), Step 2**: *"Since `C_R(R₀) = R₀ × R₁` we have `R₀ ∩ Z = 1`."*

BG states this in one line.  Unpacked: `Z` is central in `S` and `|R₀| = p` is prime, so
`R₀ ⊓ Z` is either `1` or all of `R₀`; in the latter case `R₀` would be central in `S`,
putting `S` inside `C_R(R₀)` and contradicting `r(S) ≥ 3`
(`not_le_centralizer_R₀_of_three_le_pRank`).

The hypothesis `hcent : S ≤ C_R(Z)` is the ambient spelling of `Z ≤ Z(S)`, which is how
BG's `Z = Ω₁(Z(S))` enters. -/
theorem RegularOperatorSetup.inf_eq_bot_of_three_le_pRank [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S Z : Subgroup R}
    (hcent : S ≤ Subgroup.centralizer (Z : Set R)) (hS : 3 ≤ pRank ↥S p) :
    hyp.R₀ ⊓ Z = ⊥ := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  -- `|R₀ ⊓ Z|` divides `|R₀| = p`, so it is `1` or `p`.
  have hdvd : Nat.card ↥(hyp.R₀ ⊓ Z) ∣ p := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : hyp.R₀ ⊓ Z ≤ hyp.R₀)
    rwa [hyp.R₀_card] at h
  rcases (Nat.dvd_prime hyp.p_prime).mp hdvd with h1 | hp
  · exact Subgroup.card_eq_one.mp h1
  · -- `R₀ ⊓ Z = R₀`, i.e. `R₀ ≤ Z`; then `S ≤ C_R(Z) ≤ C_R(R₀)`.
    exfalso
    have heq : hyp.R₀ ⊓ Z = hyp.R₀ :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : hyp.R₀ ⊓ Z ≤ hyp.R₀)
        (le_of_eq (hyp.R₀_card.trans hp.symm))
    have hR₀Z : hyp.R₀ ≤ Z := le_trans (le_of_eq heq.symm) inf_le_right
    exact hyp.not_le_centralizer_R₀_of_three_le_pRank hS
      (hcent.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hR₀Z)))

/-- `R₀` viewed inside a subgroup `S` containing it still has order `p`. -/
theorem RegularOperatorSetup.card_R₀_subgroupOf [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S) :
    Nat.card ↥(hyp.R₀.subgroupOf S) = p := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀S).toEquiv]
  exact hyp.R₀_card

/-- `r(C_S(R₀)) ≤ 2` for any `S` containing `R₀`: the centralizer taken inside `S` embeds in
`C_R(R₀)` along `S.subtype`, and that has rank `≤ 2` (`pRank_centralizer_R₀_le_two`).

BG obtains this from the sharper `|C_S(R₀)| = p²` of (E.4); the rank bound alone is what
Corollary 5.4 and Theorem 5.3(d) actually consume, and it needs no exponent hypothesis. -/
theorem RegularOperatorSetup.pRank_centralizer_subgroupOf_le_two [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S) :
    pRank ↥(Subgroup.centralizer ((hyp.R₀.subgroupOf S : Subgroup ↥S) : Set ↥S)) p ≤ 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set C : Subgroup ↥S :=
    Subgroup.centralizer ((hyp.R₀.subgroupOf S : Subgroup ↥S) : Set ↥S) with hCdef
  have hmem : ∀ x : ↥C, ((x : ↥S) : R) ∈ Subgroup.centralizer (hyp.R₀ : Set R) := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hcomm := Subgroup.mem_centralizer_iff.mp x.2 ⟨h, hR₀S hh⟩
      (by simpa [Subgroup.mem_subgroupOf] using hh)
    exact congrArg (fun y : ↥S => (y : R)) hcomm
  have hcomp : Function.Injective ((S.subtype).comp C.subtype) :=
    S.subtype_injective.comp C.subtype_injective
  have hfinj : Function.Injective
      (((S.subtype).comp C.subtype).codRestrict _ hmem) := fun a b hab =>
    hcomp (congrArg (fun y : ↥(Subgroup.centralizer (hyp.R₀ : Set R)) => (y : R)) hab)
  exact (pRank_le_of_injective hfinj).trans hyp.pRank_centralizer_R₀_le_two

/-- **BG Theorem E.3(b), Step 2**: *"Note that `S` is narrow."*

`R₀`, of order `p`, is a witness for Corollary 5.4
(`Ch1.S05.narrow_iff_exists_card_prime_centralizer_pRank_le_two`). -/
theorem RegularOperatorSetup.isNarrow_of_three_le_pRank [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hS : 3 ≤ pRank ↥S p) :
    IsNarrow p ↥S := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  exact (OddOrder.BG.Ch1.S05.narrow_iff_exists_card_prime_centralizer_pRank_le_two
    hyp.p_odd (hyp.R_pGroup.to_subgroup S) hS).mpr
    ⟨hyp.R₀.subgroupOf S, hyp.card_R₀_subgroupOf hR₀S,
      hyp.pRank_centralizer_subgroupOf_le_two hR₀S⟩

/-- **BG Theorem E.3(b), Step 2, first conclusion of (E.13)**: `R₀ ⊄ S'`.

BG derives this from `S = R₀T` with `S' ≤ T` and `R₀ ∩ T = 1` (E.5); in the repo the same
content is packaged as Theorem 5.3(d) (`Ch1.S05.narrow_centralizer_decomp`), whose second
clause is exactly `R₀ ∩ S' = 1` for a narrow `S`.  Since `|R₀| = p ≠ 1`, that forces
`R₀ ⊄ S'`. -/
theorem RegularOperatorSetup.not_le_derivedInG_of_three_le_pRank [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hS : 3 ≤ pRank ↥S p) :
    ¬ hyp.R₀ ≤ derivedInG S := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  intro hle
  -- Theorem 5.3(d) applied inside `↥S` with the order-`p` subgroup `R₀`.
  have hdecomp := OddOrder.BG.Ch1.S05.narrow_centralizer_decomp
    hyp.p_odd (hyp.R_pGroup.to_subgroup S) hS (hyp.isNarrow_of_three_le_pRank hR₀S hS)
    (hyp.R₀.subgroupOf S) (hyp.card_R₀_subgroupOf hR₀S)
    (hyp.pRank_centralizer_subgroupOf_le_two hR₀S)
  -- `R₀ ≤ S'` transports to `R₀.subgroupOf S ≤ commutator ↥S`, contradicting `⊓ = ⊥`.
  have hsub : hyp.R₀.subgroupOf S ≤ _root_.commutator ↥S := by
    intro x hx
    have hxR₀ : (x : R) ∈ hyp.R₀ := hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hle hxR₀)
    exact (Subtype.ext hyx.symm : x = y) ▸ hy
  have hbot : hyp.R₀.subgroupOf S = ⊥ :=
    le_bot_iff.mp (hdecomp.2.1 ▸ le_inf le_rfl hsub)
  have hcard := hyp.card_R₀_subgroupOf hR₀S
  rw [hbot, Subgroup.card_bot] at hcard
  exact hyp.p_prime.one_lt.ne hcard

/-- **BG Theorem E.3(b), Step 2, (E.4) and the first half of (E.5)**.

Applying Lemma 5.2 (`Ch1.S05.lemma52`) inside the narrow group `S`, with `Z = Ω₁(Z(S))`
and `T = C_S(Ω₁(Z₂(S)))`:

* `|Z| = p` — BG's (E.4) (BG gets it from `R₀ × Z ⊆ C_S(R₀) ⊆ R₀ × Ω₁(R₁)`);
* `|S : T| = p` — the index clause of BG's (E.5).

The maximal elementary abelian subgroup of order `p²` that Lemma 5.2 consumes is supplied by
narrowness itself (`narrow_iff_exists_maximalElementaryAbelian_card_prime_sq`), so BG's
explicit witness `E = C_S(R₀)` — and with it the computation `|C_S(R₀)| = p²` — is not
needed on this route. -/
theorem RegularOperatorSetup.card_omega1Center_and_index_centralizer [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hS : 3 ≤ pRank ↥S p) :
    Nat.card ↥(OddOrder.BG.Ch1.S05.omega1Center ↥S p) = p ∧
      (Subgroup.centralizer
        (omega1UpperCentralTwo ↥S p : Set ↥S)).index = p := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  obtain ⟨E, hEcard, hEstar⟩ :=
    (OddOrder.BG.Ch1.S05.narrow_iff_exists_maximalElementaryAbelian_card_prime_sq
      hyp.p_odd (hyp.R_pGroup.to_subgroup S) hS).mp
      (hyp.isNarrow_of_three_le_pRank hR₀S hS)
  have h := OddOrder.BG.Ch1.S05.lemma52
    hyp.p_odd (hyp.R_pGroup.to_subgroup S) hS E hEcard hEstar
  exact ⟨h.2.1.1, h.2.2⟩

/-- **BG Theorem E.3(b), Step 2, (E.4)**: `C_S(R₀) = R₀ × Ω₁(Z(S))`, of order `p²`.

BG sandwiches `R₀ × Z ⊆ C_S(R₀) ⊆ R₀ × Ω₁(R₁)` and reads off both `|Z| = p` and the
decomposition.  Here `|Z| = p` is already in hand from Lemma 5.2
(`card_omega1Center_and_index_centralizer`), and the upper bound comes more cheaply than
BG's: `C_S(R₀)` is elementary abelian — abelian because it sits in the abelian `C_R(R₀)`,
of exponent `p` by hypothesis on `S` — and `r(C_R(R₀)) ≤ 2`, so `|C_S(R₀)| ≤ p²`.  The
lower bound `R₀ × Z` already has order `p²` (`R₀ ∩ Z = 1` by
`inf_eq_bot_of_three_le_pRank`), so the two meet.  `Ω₁(R₁)` never enters. -/
theorem RegularOperatorSetup.centralizer_inf_eq_sup_omega1Center [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) :
    S ⊓ Subgroup.centralizer (hyp.R₀ : Set R)
        = hyp.R₀ ⊔ (OddOrder.BG.Ch1.S05.omega1Center ↥S p).map S.subtype ∧
      Nat.card ↥(S ⊓ Subgroup.centralizer (hyp.R₀ : Set R)) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  haveI : IsCyclic ↥hyp.R₀ := isCyclic_of_prime_card hyp.R₀_card
  set C : Subgroup R := Subgroup.centralizer (hyp.R₀ : Set R) with hCdef
  set Z : Subgroup R := (OddOrder.BG.Ch1.S05.omega1Center ↥S p).map S.subtype with hZdef
  -- `|Z| = p` (Lemma 5.2) and `Z ≤ S`, `Z` central in `S`.
  have hZcard : Nat.card ↥Z = p := by
    rw [hZdef, Subgroup.card_map_of_injective S.subtype_injective]
    exact (hyp.card_omega1Center_and_index_centralizer hR₀S hS).1
  have hZS : Z ≤ S := by
    rw [hZdef]
    rintro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hSZ : S ≤ Subgroup.centralizer (Z : Set R) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [hZdef] at hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    have hc := Subgroup.mem_center_iff.mp
      (OddOrder.BG.Ch1.S05.omega1Center_le_center hy) ⟨x, hx⟩
    simpa using (congrArg (fun z : ↥S => (z : R)) hc).symm
  -- `R₀ ∩ Z = 1`, so `|R₀ Z| = p²`.
  have hinf : hyp.R₀ ⊓ Z = ⊥ := hyp.inf_eq_bot_of_three_le_pRank hSZ hS
  have hR₀Z : hyp.R₀ ≤ Subgroup.centralizer (Z : Set R) := hR₀S.trans hSZ
  have hsupcard : Nat.card ↥(hyp.R₀ ⊔ Z) = p ^ 2 := by
    have hcoe : (↑(hyp.R₀ ⊔ Z) : Set R) = (hyp.R₀ : Set R) * (Z : Set R) :=
      Subgroup.coe_mul_of_left_le_normalizer_right hyp.R₀ Z
        (hR₀Z.trans (Subgroup.centralizer_le_normalizer _))
    have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card hyp.R₀ Z
    rw [hinf, Subgroup.card_bot, mul_one, hyp.R₀_card, hZcard] at hprod
    have hcong : Nat.card ↥(hyp.R₀ ⊔ Z) = Nat.card ↥((hyp.R₀ : Set R) * (Z : Set R)) :=
      Nat.card_congr (Equiv.setCongr hcoe)
    rw [hcong, hprod]; ring
  -- `R₀ Z ≤ C_S(R₀)`.
  have hle : hyp.R₀ ⊔ Z ≤ S ⊓ C := by
    refine sup_le (le_inf hR₀S ?_) (le_inf hZS ?_)
    · rw [hCdef]
      exact Subgroup.le_centralizer_iff_isMulCommutative.mpr IsCyclic.isMulCommutative
    · rw [hCdef, ← Subgroup.le_centralizer_iff]
      exact hR₀S.trans hSZ
  -- `C_S(R₀)` is elementary abelian inside `C_R(R₀)`, whose `p`-rank is `≤ 2`.
  have hEA : ((S ⊓ C).subgroupOf C).IsElementaryAbelian p := by
    refine ⟨fun x y => Subtype.ext ?_, fun x => Subtype.ext ?_⟩
    · exact hyp.isMulCommutative_centralizer_R₀.is_comm.comm (x : ↥C) (y : ↥C)
    · have hxS : ((x : ↥C) : R) ∈ S := (Subgroup.mem_subgroupOf.mp x.2).1
      have hp1 := congrArg (fun z : ↥S => (z : R)) (hexp ⟨((x : ↥C) : R), hxS⟩)
      exact Subtype.ext (by simpa using hp1)
  have hEcard : Nat.card ↥(S ⊓ C) ≤ p ^ 2 := by
    obtain ⟨k, hk⟩ := (hyp.R_pGroup.to_subgroup (S ⊓ C)).exists_card_eq
    have hlog := le_pRank ((S ⊓ C).subgroupOf C) hEA
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : S ⊓ C ≤ C)).toEquiv,
      hk, Nat.log_pow hyp.p_prime.one_lt] at hlog
    have h2 : pRank ↥C p ≤ 2 := hyp.pRank_centralizer_R₀_le_two
    rw [hk]
    exact Nat.pow_le_pow_right hyp.p_prime.pos (by omega)
  have heq : hyp.R₀ ⊔ Z = S ⊓ C :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hsupcard]; exact hEcard)
  exact ⟨heq.symm, by rw [← heq, hsupcard]⟩

/-- The centralizer of `R₀` computed inside `↥S` is the `subgroupOf` of the ambient
`S ⊓ C_R(R₀)`: an `x ∈ S` centralizes `R₀ ∩ S = R₀` iff `↑x` centralizes `R₀`. -/
theorem RegularOperatorSetup.centralizer_subgroupOf_eq
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S) :
    Subgroup.centralizer ((hyp.R₀.subgroupOf S : Subgroup ↥S) : Set ↥S)
      = (S ⊓ Subgroup.centralizer (hyp.R₀ : Set R)).subgroupOf S := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · refine fun h => ⟨x.2, fun g hg => ?_⟩
    exact congrArg (fun y : ↥S => (y : R))
      (h ⟨g, hR₀S hg⟩ (by simpa [Subgroup.mem_subgroupOf] using hg))
  · rintro ⟨-, h⟩ g hg
    exact Subtype.ext (h (g : R) (by simpa [Subgroup.mem_subgroupOf] using hg))

/-- **BG Theorem E.3(b), Step 2, (E.5)**: `|C_T(R₀)| = p`, where `T = C_S(Ω₁(Z₂(S)))`.

Theorem 5.3(d) (`Ch1.S05.narrow_centralizer_decomp`) gives the internal direct
decomposition `C_S(R₀) = R₀ × C_T(R₀)`; with `|C_S(R₀)| = p²` from (E.4) and `|R₀| = p`,
the cyclic factor `C_T(R₀)` has order `p`.

Together with `|S : T| = p` (`card_omega1Center_and_index_centralizer`) this is BG's
`|S : T| = |C_T(R₀)| = p`. -/
theorem RegularOperatorSetup.card_centralizer_inf_centralizer_eq [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) :
    Nat.card ↥(Subgroup.centralizer ((hyp.R₀.subgroupOf S : Subgroup ↥S) : Set ↥S) ⊓
      Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) = p := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set R₀' : Subgroup ↥S := hyp.R₀.subgroupOf S with hR₀'
  set CS : Subgroup ↥S := Subgroup.centralizer ((R₀' : Subgroup ↥S) : Set ↥S) with hCS
  set T : Subgroup ↥S :=
    Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hT
  obtain ⟨-, -, hR₀T, hdecomp⟩ := OddOrder.BG.Ch1.S05.narrow_centralizer_decomp
    hyp.p_odd (hyp.R_pGroup.to_subgroup S) hS (hyp.isNarrow_of_three_le_pRank hR₀S hS)
    R₀' (hyp.card_R₀_subgroupOf hR₀S) (hyp.pRank_centralizer_subgroupOf_le_two hR₀S)
  -- `|C_S(R₀)| = p²` via (E.4), transported into `↥S`.
  have hCScard : Nat.card ↥CS = p ^ 2 := by
    rw [hCS, hR₀', hyp.centralizer_subgroupOf_eq hR₀S,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
        S ⊓ Subgroup.centralizer (hyp.R₀ : Set R) ≤ S)).toEquiv]
    exact (hyp.centralizer_inf_eq_sup_omega1Center hR₀S hexp hS).2
  -- `C_S(R₀) = R₀ × (C_S(R₀) ⊓ T)` with `R₀ ⊓ T = ⊥`, so `p² = p · |C_T(R₀)|`.
  have hnorm : R₀' ≤ Subgroup.normalizer ((CS ⊓ T : Subgroup ↥S) : Set ↥S) :=
    (Subgroup.le_centralizer_iff.mpr (inf_le_left.trans (le_of_eq hCS))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcoe : (↑(R₀' ⊔ (CS ⊓ T)) : Set ↥S) = (R₀' : Set ↥S) * ((CS ⊓ T : Subgroup ↥S) : Set ↥S) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
  have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card R₀' (CS ⊓ T)
  have hinfbot : R₀' ⊓ (CS ⊓ T) = ⊥ :=
    le_bot_iff.mp ((le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans (le_of_eq hR₀T))
  rw [hinfbot, Subgroup.card_bot, mul_one, hyp.card_R₀_subgroupOf hR₀S] at hprod
  have hcong : Nat.card ↥(R₀' ⊔ (CS ⊓ T)) =
      Nat.card ↥((R₀' : Set ↥S) * ((CS ⊓ T : Subgroup ↥S) : Set ↥S)) :=
    Nat.card_congr (Equiv.setCongr hcoe)
  rw [← hdecomp, hCScard, hprod] at hcong
  have hmul : p * p = p * Nat.card ↥(CS ⊓ T) := by rw [← sq]; exact hcong
  exact (Nat.eq_of_mul_eq_mul_left hyp.p_prime.pos hmul).symm

/-- **BG Theorem E.3(b), Step 2, the (E.6) counting step**: `|H| ≤ |⁅R₀, H⁆| · p` for any
`H ≤ T`.

This is BG's *"a short argument using the mapping `H → [R, H]` given by `x ↦ [v,x]`"*: for a
generator `v` of `R₀` that map is constant exactly on the cosets of `C_H(v)`, so
`|H : C_H(v)| ≤ |⁅R₀, H⁆|`; and `C_H(v) ≤ C_T(R₀)`, of order `p` by (E.5).

The counting itself is `Ch1.S05.card_le_card_mul_of_commutator_mem_of_card_centralizer_le`
— the same lemma that drives Theorem 5.5's own `H_i` chain, which is why BG can say
"follow the part of the proof of Theorem 5.5 that comes after (5.5)". -/
theorem RegularOperatorSetup.card_le_card_commutator_mul_prime [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {H : Subgroup ↥S}
    (hHT : H ≤ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) :
    Nat.card ↥H ≤ Nat.card ↥⁅hyp.R₀.subgroupOf S, H⁆ * p := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set R₀' : Subgroup ↥S := hyp.R₀.subgroupOf S with hR₀'def
  have hR₀'card : Nat.card ↥R₀' = p := hyp.card_R₀_subgroupOf hR₀S
  -- pick a generator `v` of the order-`p` group `R₀`
  haveI : Nontrivial ↥R₀' := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro h
    rw [h, Subgroup.card_bot] at hR₀'card
    exact hyp.p_prime.one_lt.ne hR₀'card
  obtain ⟨w, hw⟩ := exists_ne (1 : ↥R₀')
  have hvR₀ : (w : ↥S) ∈ R₀' := w.2
  have hord : orderOf (w : ↥S) = p := by
    have h1 : orderOf w ∣ Nat.card ↥R₀' := orderOf_dvd_natCard w
    rw [hR₀'card] at h1
    have h2 : orderOf (w : ↥S) = orderOf w := Subgroup.orderOf_coe w
    rcases (Nat.dvd_prime hyp.p_prime).mp h1 with h | h
    · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp (h2.trans h))) hw
    · exact h2.trans h
  have hzp : Subgroup.zpowers (w : ↥S) = R₀' :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hvR₀)
      (by rw [hR₀'card, Nat.card_zpowers, hord])
  refine OddOrder.BG.Ch1.S05.card_le_card_mul_of_commutator_mem_of_card_centralizer_le
    (v := (w : ↥S)) (fun x hx => Subgroup.commutator_mem_commutator hvR₀ hx) ?_
  -- `C_H(v) ≤ C_T(R₀)`, which has order `p`.
  have hsub : Subgroup.centralizer ({(w : ↥S)} : Set ↥S) ⊓ H ≤
      Subgroup.centralizer ((R₀' : Subgroup ↥S) : Set ↥S) ⊓
        Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) := by
    refine inf_le_inf ?_ hHT
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [← hzp] at hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hc : Commute (w : ↥S) x := Subgroup.mem_centralizer_iff.mp hx (w : ↥S) rfl
    exact hc.zpow_left k
  calc Nat.card ↥(Subgroup.centralizer ({(w : ↥S)} : Set ↥S) ⊓ H)
      ≤ Nat.card ↥(Subgroup.centralizer ((R₀' : Subgroup ↥S) : Set ↥S) ⊓
          Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) :=
        Nat.card_le_card_of_injective (Subgroup.inclusion hsub)
          (Subgroup.inclusion_injective hsub)
    _ = p := hyp.card_centralizer_inf_centralizer_eq hR₀S hexp hS

/-- **BG Theorem E.3(b), Step 2: the arithmetic core of (E.10)--(E.12)**.

In a finite **cyclic** group: if `u ≠ 1` satisfies `u^q = 1` for a prime `q`, if `u₀`
satisfies `u₀^q = 1`, and if `u₀ uⁱ ≠ 1` for every `i < n`, then `n ≤ q − 1`.

This is BG's closing count — *"the nonzero integers (mod p) form a cyclic group of order
`p−1` and `r^q ≡ 1`… therefore `q − 1 ≥ j + n − 1 ≥ n`"*.  `u` has order exactly `q`;
cyclicity is what puts `u₀` inside `⟨u⟩`, so `u₀ = uʲ` with `1 ≤ j ≤ q−1`; then
`u₀ uⁱ = u^{j+i}` avoiding `1` forces the interval `[j, j+n−1]` to miss `q`.

Stated for an abstract cyclic group rather than `(ZMod p)ˣ`: nothing here is about `ZMod`,
and the consumer supplies cyclicity of the unit group. -/
theorem le_pred_of_forall_mul_pow_ne_one {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {q n : ℕ} (hq : q.Prime) {u u₀ : C} (hu : u ^ q = 1) (hune : u ≠ 1) (hu₀ : u₀ ^ q = 1)
    (hne : ∀ i < n, u₀ * u ^ i ≠ 1) : n ≤ q - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · omega
  -- `u` has order exactly `q`
  have hordu : orderOf u = q := by
    rcases (Nat.dvd_prime hq).mp (orderOf_dvd_of_pow_eq_one hu) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hune
    · exact h
  -- cyclicity puts `u₀` in `⟨u⟩`
  have hmem : u₀ ∈ Subgroup.zpowers u := by
    rcases (Nat.dvd_prime hq).mp (orderOf_dvd_of_pow_eq_one hu₀) with h | h
    · rw [orderOf_eq_one_iff.mp h]; exact Subgroup.one_mem _
    · have hcard : Nat.card ↥(Subgroup.zpowers u₀) = Nat.card ↥(Subgroup.zpowers u) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, h, hordu]
      exact OddOrder.GroupTheory.cyclic_subgroup_eq_of_card_eq hcard ▸
        Subgroup.mem_zpowers u₀
  obtain ⟨j, hj⟩ : ∃ j : ℕ, u ^ j = u₀ :=
    (Submonoid.mem_powers_iff u₀ u).mp (mem_powers_iff_mem_zpowers.mpr hmem)
  -- reduce the exponent below `q`
  set j' := j % q with hj'def
  have hj'lt : j' < q := Nat.mod_lt _ hq.pos
  have hj' : u ^ j' = u₀ := by rw [hj'def, ← hordu, pow_mod_orderOf, hj]
  have hj'pos : 0 < j' := by
    rcases Nat.eq_zero_or_pos j' with h | h
    · exact absurd (by simpa [h] using hj'.symm) (by simpa using hne 0 hnpos)
    · exact h
  -- `u₀ uⁱ = u^{j'+i} ≠ 1` says `q ∤ j' + i`
  by_contra hlt
  push Not at hlt
  have hqn : q ≤ n := by omega
  have hi : q - j' < n := by omega
  refine hne (q - j') hi ?_
  rw [← hj', ← pow_add]
  have : j' + (q - j') = q := by omega
  rw [this, hu]

/-- A finite `p`-group of order at most `p³` has nilpotency class `≤ 2`, i.e. `G' ≤ Z(G)`.

This is what BG's elided *"examination of the `p`-groups of order at most `p³`"* actually
needs; the classification of those groups is not required. -/
private theorem commutator_le_center_of_card_le_prime_cube {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (hcard : Nat.card G ≤ p ^ 3) :
    _root_.commutator G ≤ Subgroup.center G := by
  haveI : Group.IsNilpotent G := hG.isNilpotent
  have hcl : Group.nilpotencyClass G ≤ 2 :=
    OddOrder.BG.Ch1.S04.nilpotencyClass_le_of_card_le_pow hG (by norm_num)
      (by simpa using hcard)
  have hlcs : ⁅_root_.commutator G, (⊤ : Subgroup G)⁆ = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hcl
  have hce := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hlcs
  intro g hg
  rw [Subgroup.mem_center_iff]
  intro h
  exact Subgroup.mem_centralizer_iff.mp (hce hg) h (Subgroup.mem_top h)

/-- In a finite `p`-group a *proper* subgroup has index divisible by `p`, so `K < H` gives
`p · |K| ≤ |H|`.  Used twice below, for the two ends of BG's (E.6) chain step. -/
private theorem prime_mul_card_le_card_of_lt {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hG : IsPGroup p G) {K H : Subgroup G} (hlt : K < H) :
    p * Nat.card ↥K ≤ Nat.card ↥H := by
  have hidx_ne : (K.subgroupOf H).index ≠ 1 := fun h1 =>
    hlt.ne (le_antisymm hlt.le
      (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h1)))
  have hdvd : (K.subgroupOf H).index ∣ Nat.card ↥H := Subgroup.index_dvd_card _
  obtain ⟨k, hk⟩ := (hG.to_subgroup H).exists_card_eq
  rw [hk] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  have hple : p ≤ (K.subgroupOf H).index := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact absurd (by simpa using hj) hidx_ne
    · rw [hj]
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ j := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hjpos
  have hmul : Nat.card ↥K * (K.subgroupOf H).index = Nat.card ↥H := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hlt.le).toEquiv]
    exact Subgroup.card_mul_index _
  calc p * Nat.card ↥K = Nat.card ↥K * p := mul_comm _ _
    _ ≤ Nat.card ↥K * (K.subgroupOf H).index := Nat.mul_le_mul_left _ hple
    _ = Nat.card ↥H := hmul

/-- **BG Theorem E.3(b), Step 2, (E.6)**: one chain step has index exactly `p` —
`|H| = p · |⁅R₀, H⁆|` for a nontrivial normal `H ≤ T`.

Two bounds meet.  `≤`: the counting step `card_le_card_commutator_mul_prime`.  `≥`:
`⁅R₀, H⁆ = ⁅H, R₀⁆ < H` because `S` is nilpotent and `H` is normal and nontrivial
(`Isaacs.Ch04.commutator_lt_self_of_isNilpotent_ambient`), and a *proper* subgroup of a
`p`-group has index divisible by `p`.

This is the inductive step of BG's series `T = H₀ ⊃ H₁ ⊃ ⋯ ⊃ Hₙ = 1`, whose factors BG
records as `|Hᵢ₋₁ : Hᵢ| = p`. -/
theorem RegularOperatorSetup.card_eq_prime_mul_card_commutator [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {H : Subgroup ↥S} [H.Normal]
    (hHne : H ≠ ⊥)
    (hHT : H ≤ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) :
    Nat.card ↥H = p * Nat.card ↥⁅hyp.R₀.subgroupOf S, H⁆ := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  haveI : Group.IsNilpotent ↥S := (hyp.R_pGroup.to_subgroup S).isNilpotent
  set R₀' : Subgroup ↥S := hyp.R₀.subgroupOf S with hR₀'def
  set K : Subgroup ↥S := ⁅R₀', H⁆ with hKdef
  -- `⁅R₀, H⁆ = ⁅H, R₀⁆ < H` by nilpotency.
  have hlt : K < H := by
    rw [hKdef, Subgroup.commutator_comm]
    exact OddOrder.Isaacs.Ch04.commutator_lt_self_of_isNilpotent_ambient hHne
  have hge : p * Nat.card ↥K ≤ Nat.card ↥H :=
    prime_mul_card_le_card_of_lt (hyp.R_pGroup.to_subgroup S) hlt
  have hle : Nat.card ↥H ≤ Nat.card ↥K * p :=
    hyp.card_le_card_commutator_mul_prime hR₀S hexp hS hHT
  rw [mul_comm p] at hge ⊢
  exact le_antisymm hle hge

/-- **BG Theorem E.3(b), Step 2, (E.6)**: `⁅R₀, H⁆ = ⁅S, H⁆` for nontrivial normal `H ≤ T`.

BG *asserts* the identification `Hᵢ = [R, Hᵢ₋₁] = [R₀, Hᵢ₋₁]`.  It is a **consequence** of
the counting, not an input to it: `⁅R₀,H⁆ ≤ ⁅S,H⁆` is monotonicity, and conversely `⁅S,H⁆`
is a proper subgroup of the `p`-group `H` (nilpotency), so
`|⁅S,H⁆| ≤ |H|/p = |⁅R₀,H⁆|` by `card_eq_prime_mul_card_commutator`.

The identification is what makes BG's chain *characteristic*: `⁅S, ·⁆` preserves normality
in `S`, whereas `⁅R₀, ·⁆` need not, `R₀` being non-normal in `S`.  So the chain should be
**defined** by the `⁅S, ·⁆` form and only then recognised as the `⁅R₀, ·⁆` form. -/
theorem RegularOperatorSetup.commutator_R₀_eq_commutator_top [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {H : Subgroup ↥S} [H.Normal]
    (hHne : H ≠ ⊥)
    (hHT : H ≤ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) :
    ⁅hyp.R₀.subgroupOf S, H⁆ = ⁅(⊤ : Subgroup ↥S), H⁆ := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  haveI : Group.IsNilpotent ↥S := (hyp.R_pGroup.to_subgroup S).isNilpotent
  have hmono : ⁅hyp.R₀.subgroupOf S, H⁆ ≤ ⁅(⊤ : Subgroup ↥S), H⁆ :=
    Subgroup.commutator_mono le_top le_rfl
  refine Subgroup.eq_of_le_of_card_ge hmono ?_
  -- `⁅S,H⁆ = ⁅H,S⁆ < H`, so `p · |⁅S,H⁆| ≤ |H| = p · |⁅R₀,H⁆|`.
  have hlt : ⁅(⊤ : Subgroup ↥S), H⁆ < H := by
    rw [Subgroup.commutator_comm]
    exact OddOrder.Isaacs.Ch04.commutator_lt_self_of_isNilpotent_ambient hHne
  have hge : p * Nat.card ↥⁅(⊤ : Subgroup ↥S), H⁆ ≤ Nat.card ↥H :=
    prime_mul_card_le_card_of_lt (hyp.R_pGroup.to_subgroup S) hlt
  rw [hyp.card_eq_prime_mul_card_commutator hR₀S hexp hS hHne hHT] at hge
  exact Nat.le_of_mul_le_mul_left hge hyp.p_prime.pos

/-- **BG Theorem E.3(b), Step 2, (E.5)**: `S = R₀T`.

BG records `T char S`, `|S : T| = p` and `R₀ ∩ T = 1`, then writes `S = R₀T`.  The last step
is a cardinality count: `T` is normal (indeed `T char S` is already an instance in the repo,
`GroupTheory.centralizer_omega1UpperCentralTwo_characteristic`), so `|R₀T| = |R₀| · |T| =
p · |T| = |S|`.

Note `hexp` is not needed: narrowness alone drives Theorem 5.3(d). -/
theorem RegularOperatorSetup.sup_centralizer_eq_top [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hS : 3 ≤ pRank ↥S p) :
    hyp.R₀.subgroupOf S ⊔
      Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) = ⊤ := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set R₀' : Subgroup ↥S := hyp.R₀.subgroupOf S with hR₀'def
  set T : Subgroup ↥S :=
    Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hTdef
  obtain ⟨-, -, hR₀T, -⟩ := OddOrder.BG.Ch1.S05.narrow_centralizer_decomp
    hyp.p_odd (hyp.R_pGroup.to_subgroup S) hS (hyp.isNarrow_of_three_le_pRank hR₀S hS)
    R₀' (hyp.card_R₀_subgroupOf hR₀S) (hyp.pRank_centralizer_subgroupOf_le_two hR₀S)
  -- `|R₀ T| = |R₀| · |T| = p · |T|`
  have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card R₀' T
  rw [hR₀T, Subgroup.card_bot, mul_one, hyp.card_R₀_subgroupOf hR₀S] at hprod
  have hcong : Nat.card ↥(R₀' ⊔ T) = Nat.card ↥((R₀' : Set ↥S) * (T : Set ↥S)) :=
    Nat.card_congr (Equiv.setCongr (Subgroup.mul_normal R₀' T))
  -- `|S| = |T| · [S : T] = |T| · p`
  have hSc : Nat.card ↥T * T.index = Nat.card ↥S := T.card_mul_index
  rw [(hyp.card_omega1Center_and_index_centralizer hR₀S hS).2] at hSc
  refine Subgroup.eq_of_le_of_card_ge le_top ?_
  rw [Subgroup.card_top, hcong, hprod, ← hSc, mul_comm]

/-! ### (E.6): BG's descending series

BG's chain `T = H₀ ⊃ H₁ ⊃ ⋯ ⊃ Hₙ = 1` with `Hᵢ = [R, Hᵢ₋₁]` is the repo's
`Isaacs.Ch04.iterCommutator T ⊤` (iterated *right* commutator with the whole group), so no
new definition is introduced.  BG's other description `Hᵢ = [R₀, Hᵢ₋₁]` is recovered from
`commutator_R₀_eq_commutator_top`. -/

/-- Every term of `iterCommutator T ⊤` is normal when `T` is. -/
private theorem normal_iterCommutator {G : Type*} [Group G] {T : Subgroup G} [T.Normal] :
    ∀ n, (OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) n).Normal
  | 0 => ‹T.Normal›
  | n + 1 => by
      haveI := normal_iterCommutator (T := T) n
      exact Subgroup.commutator_normal _ _

/-- `iterCommutator T ⊤` descends: `⁅H, ⊤⁆ ≤ H` for normal `H`. -/
private theorem iterCommutator_antitone {G : Type*} [Group G] {T : Subgroup G} [T.Normal] :
    ∀ n, OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (n + 1) ≤
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) n := fun n => by
  haveI := normal_iterCommutator (T := T) n
  exact Subgroup.commutator_le_left _ _

/-- `iterCommutator T ⊤ n ≤ T` for every `n`. -/
private theorem iterCommutator_le_start {G : Type*} [Group G] {T : Subgroup G} [T.Normal] :
    ∀ n, OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) n ≤ T
  | 0 => le_rfl
  | n + 1 => (iterCommutator_antitone n).trans (iterCommutator_le_start n)

/-- **BG Theorem E.3(b), Step 2, (E.6)**: every factor of the chain has order `p`.

For BG's series `Hᵢ = iterCommutator T ⊤ i`, as long as `Hᵢ ≠ 1` we have
`|Hᵢ| = p · |Hᵢ₊₁|` — BG's `|Hᵢ₋₁ : Hᵢ| = p`.

The two descriptions of the chain meet here: the *definition* uses `⁅Hᵢ, S⁆`, which keeps
each term normal in `S`, while the *counting* (`card_eq_prime_mul_card_commutator`) is about
`⁅R₀, Hᵢ⁆`; `commutator_R₀_eq_commutator_top` identifies them. -/
theorem RegularOperatorSetup.card_iterCommutator_eq [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {T : Subgroup ↥S} [T.Normal]
    (hT : T ≤ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) {i : ℕ}
    (hne : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i ≠ ⊥) :
    Nat.card ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i) =
      p * Nat.card ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (i + 1)) := by
  haveI := normal_iterCommutator (T := T) i
  have hHT : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i ≤
      Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) :=
    (iterCommutator_le_start i).trans hT
  have hstep := hyp.card_eq_prime_mul_card_commutator hR₀S hexp hS hne hHT
  rw [hyp.commutator_R₀_eq_commutator_top hR₀S hexp hS hne hHT] at hstep
  rw [hstep, OddOrder.Isaacs.Ch04.iterCommutator_succ, Subgroup.commutator_comm]

/-- **BG Theorem E.3(b), Step 2, (E.6)**: `|T| = pⁱ · |Hᵢ|` for as long as `Hᵢ ≠ 1`.

Iterating `card_iterCommutator_eq`.  Since `iterCommutator T ⊤` reaches `⊥`
(`Isaacs.Ch04.iterCommutator_eq_bot_of_isNilpotent_ambient`), at the last nontrivial index
this reads `|T| = pⁿ` — BG's "Thus `|T| = pⁿ`". -/
theorem RegularOperatorSetup.card_start_eq_pow_mul [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {T : Subgroup ↥S} [T.Normal]
    (hT : T ≤ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) :
    ∀ i : ℕ, OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i ≠ ⊥ →
      Nat.card ↥T =
        p ^ i * Nat.card ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i)
  | 0, _ => by simp [OddOrder.Isaacs.Ch04.iterCommutator_zero]
  | i + 1, hne => by
      have hprev : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i ≠ ⊥ := by
        intro h
        exact hne (le_bot_iff.mp ((iterCommutator_antitone i).trans (le_of_eq h)))
      rw [hyp.card_start_eq_pow_mul hR₀S hexp hS hT i hprev,
        hyp.card_iterCommutator_eq hR₀S hexp hS hT hprev, pow_succ]
      ring

/-- **BG Theorem E.3(b), Step 2, (E.7)**: `H₁ = S'` and `|S / S'| = p²`.

BG: *"Since `|H₀/H₁| = p` and `H₁ = [R₀,H₀] = [R₀,T] ≤ R₀T = S`, we have `|S/H₁| = p²` and
`S₂ = [S,S] ⊆ H₁ = [R₀,T] ⊆ S₂`."*

`|S : H₁| = p²` because `|S : T| = p` (E.5) and `|T : H₁| = p` (E.6).  Then `S/H₁` has order
`p²`, hence is abelian, giving `S' ≤ H₁`; and `H₁ = ⁅T, S⁆ ≤ ⁅S, S⁆ = S'` directly.  So the
two coincide and `|S/S'| = p²`.

With `S = Ω₁(R)` this is exactly E.3(b)'s third clause. -/
theorem RegularOperatorSetup.commutator_eq_and_card_quotient [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) :
    OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) 1
      = _root_.commutator ↥S ∧
    Nat.card (↥S ⧸ _root_.commutator ↥S) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set T : Subgroup ↥S :=
    Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hTdef
  set H₁ : Subgroup ↥S := OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) 1 with hH₁def
  haveI : H₁.Normal := normal_iterCommutator (T := T) 1
  have hTindex : T.index = p := (hyp.card_omega1Center_and_index_centralizer hR₀S hS).2
  have hScard : Nat.card ↥T * p = Nat.card ↥S := by
    rw [← hTindex]; exact T.card_mul_index
  -- `p³ ≤ |S|` from `r(S) ≥ 3`, so `T ≠ ⊥`.
  have hp3 : p ^ 3 ≤ Nat.card ↥S := by
    obtain ⟨A, hA, hAlog⟩ :=
      exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥S) (by norm_num) hS
    calc p ^ 3 ≤ p ^ Nat.log p (Nat.card ↥A) :=
          Nat.pow_le_pow_right hyp.p_prime.pos hAlog
      _ ≤ Nat.card ↥A := Nat.pow_log_le_self p (Nat.card_pos (α := ↥A)).ne'
      _ ≤ Nat.card ↥S :=
        Nat.card_le_card_of_injective (fun x : ↥A => (x : ↥S)) Subtype.val_injective
  have hTne : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) 0 ≠ ⊥ := by
    intro h
    rw [OddOrder.Isaacs.Ch04.iterCommutator_zero] at h
    rw [h, Subgroup.card_bot, one_mul] at hScard
    rw [← hScard] at hp3
    have hlt : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hyp.p_prime.one_lt (by norm_num)
    omega
  -- `|S| = p² · |H₁|`, so `[S : H₁] = p²`.
  have hstep := hyp.card_iterCommutator_eq hR₀S hexp hS (le_refl T) hTne
  rw [OddOrder.Isaacs.Ch04.iterCommutator_zero, ← hH₁def] at hstep
  have hH₁index : H₁.index = p ^ 2 := by
    have hmul : Nat.card ↥H₁ * H₁.index = Nat.card ↥S := H₁.card_mul_index
    have hSp2 : Nat.card ↥S = Nat.card ↥H₁ * p ^ 2 := by rw [← hScard, hstep]; ring
    rw [hSp2] at hmul
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥H₁)) hmul
  -- `S/H₁` has order `p²`, hence is abelian, so `S' ≤ H₁`; and `H₁ = ⁅T,S⁆ ≤ S'`.
  have hquot : Nat.card (↥S ⧸ H₁) = p ^ 2 := hH₁index
  haveI : IsMulCommutative (↥S ⧸ H₁) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hquot
  have hSle : _root_.commutator ↥S ≤ H₁ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have hone : (QuotientGroup.mk' H₁) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact ‹IsMulCommutative (↥S ⧸ H₁)›.is_comm.comm _ _
    exact (QuotientGroup.eq_one_iff _).mp hone
  have hH₁le : H₁ ≤ _root_.commutator ↥S := by
    rw [hH₁def, OddOrder.Isaacs.Ch04.iterCommutator_succ,
      OddOrder.Isaacs.Ch04.iterCommutator_zero, commutator_def]
    exact Subgroup.commutator_mono le_top le_rfl
  have heq : H₁ = _root_.commutator ↥S := le_antisymm hH₁le hSle
  exact ⟨heq, by rw [← heq]; exact hquot⟩

/-- **BG Theorem E.3(b), Step 2, the elided small case for (E.7)**: `|S/S'| = p²` when
`|S| ≤ p³`.

This is where BG's *"an examination of the `p`-groups of order at most `p³`"* is genuinely
needed — unlike the clause `R₀ ⊄ S'`, which `S' ≤ Z(S)` alone already settles
(`not_le_derivedInG_of_derived_central`).  It is also the first point at which BG's
hypothesis that `S` contains `R₀` **properly** does any work.

* `S` abelian: exponent `p` makes it elementary abelian, and `R₀ ≤ S` puts `S` inside
  `C_R(R₀)`, of `p`-rank `≤ 2`; so `|S| ≤ p²`, while `R₀ < S` forces `|S| ≥ p²`.  Then
  `S' = 1` and `|S/S'| = |S| = p²`.
* `S` nonabelian: then `|S| = p³`; `S/Z(S)` is non-cyclic, so `|Z(S)| = p`, and `cl(S) ≤ 2`
  with `S' ≠ 1` gives `S' = Z(S)` of order `p`, whence `|S/S'| = p³/p = p²`. -/
theorem RegularOperatorSetup.card_quotient_commutator_of_card_le_prime_cube [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ < S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hcard : Nat.card ↥S ≤ p ^ 3) :
    Nat.card (↥S ⧸ _root_.commutator ↥S) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  have hSpg : IsPGroup p ↥S := hyp.R_pGroup.to_subgroup S
  -- `R₀ < S` gives `p² ≤ |S|`.
  have hR₀lt : hyp.R₀.subgroupOf S < (⊤ : Subgroup ↥S) :=
    lt_of_le_of_ne le_top fun h => absurd (Subgroup.subgroupOf_eq_top.mp h) hR₀S.not_ge
  have hp2 : p ^ 2 ≤ Nat.card ↥S := by
    have := prime_mul_card_le_card_of_lt hSpg hR₀lt
    rw [hyp.card_R₀_subgroupOf hR₀S.le, Subgroup.card_top] at this
    calc p ^ 2 = p * p := sq p
      _ ≤ Nat.card ↥S := this
  by_cases habel : IsMulCommutative ↥S
  · -- `S` elementary abelian of rank `≤ 2`, so `|S| = p²` and `S' = 1`.
    have hSC : S ≤ Subgroup.centralizer (hyp.R₀ : Set R) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg (fun z : ↥S => (z : R))
        (habel.is_comm.comm (⟨g, hR₀S.le hg⟩ : ↥S) ⟨x, hx⟩)
    have hEA : IsElementaryAbelian p ↥S := ⟨fun x y => habel.is_comm.comm x y, hexp⟩
    have hrank : pRank ↥S p ≤ 2 :=
      (pRank_le_of_injective (f := Subgroup.inclusion hSC)
        (Subgroup.inclusion_injective hSC)).trans hyp.pRank_centralizer_R₀_le_two
    have hle : Nat.card ↥S ≤ p ^ 2 := by
      obtain ⟨k, hk⟩ := hSpg.exists_card_eq
      have hlog := hEA.log_card_le_pRank
      rw [hk, Nat.log_pow hyp.p_prime.one_lt] at hlog
      rw [hk]
      exact Nat.pow_le_pow_right hyp.p_prime.pos (hlog.trans hrank)
    haveI := habel
    have hcomm : _root_.commutator ↥S = ⊥ := commutator_eq_bot ↥S
    rw [hcomm]
    show (⊥ : Subgroup ↥S).index = p ^ 2
    rw [Subgroup.index_bot]
    omega
  · -- `S` nonabelian: `|S| = p³`, `|Z(S)| = p`, `S' = Z(S)`.
    have hcentre := commutator_le_center_of_card_le_prime_cube hSpg hcard
    have hcommne : _root_.commutator ↥S ≠ ⊥ := by
      intro h
      refine habel (IsMulCommutative.of_comm fun a b => ?_)
      have hmem : ⁅a, b⁆ ∈ (⊥ : Subgroup ↥S) := h ▸ Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact commutatorElement_eq_one_iff_commute.mp (Subgroup.mem_bot.mp hmem)
    -- `|Z(S)| ≤ p`: otherwise `|S : Z(S)| ≤ p`, so `S/Z(S)` is cyclic and `S` abelian.
    have hZle : Nat.card ↥(Subgroup.center ↥S) ≤ p := by
      by_contra hgt
      push Not at hgt
      obtain ⟨j, hj⟩ := (hSpg.to_subgroup (Subgroup.center ↥S)).exists_card_eq
      have hZp2 : p ^ 2 ≤ Nat.card ↥(Subgroup.center ↥S) := by
        rw [hj]
        refine Nat.pow_le_pow_right hyp.p_prime.pos ?_
        by_contra hj2
        push Not at hj2
        rw [hj] at hgt
        have hjle : p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hyp.p_prime.pos (by omega)
        rw [pow_one] at hjle
        omega
      have hidx : (Subgroup.center ↥S).index * Nat.card ↥(Subgroup.center ↥S) =
          Nat.card ↥S := (Subgroup.center ↥S).index_mul_card
      have hidxle : (Subgroup.center ↥S).index ≤ p := by
        nlinarith [hidx, hcard, hZp2, hyp.p_prime.pos, sq_nonneg p]
      haveI : IsCyclic (↥S ⧸ Subgroup.center ↥S) := by
        refine isCyclic_of_card_dvd_prime (p := p) ?_
        obtain ⟨m, hm⟩ := (hSpg.to_quotient (Subgroup.center ↥S)).exists_card_eq
        have hqidx : Nat.card (↥S ⧸ Subgroup.center ↥S) = (Subgroup.center ↥S).index := rfl
        have hm1 : m ≤ 1 := by
          by_contra hm2
          push Not at hm2
          have : p ^ 2 ≤ Nat.card (↥S ⧸ Subgroup.center ↥S) := by
            rw [hm]; exact Nat.pow_le_pow_right hyp.p_prime.pos hm2
          rw [hqidx] at this
          nlinarith [hidxle, hyp.p_prime.one_lt]
        rw [hm]
        interval_cases m
        · exact one_dvd p
        · rw [pow_one]
      exact habel (isMulCommutative_of_isCyclic_quotient_center_self ↥S)
    -- `S' ≤ Z(S)` with `S' ≠ 1` and `|Z(S)| ≤ p` forces `|S'| = |Z(S)| = p`.
    have hScomm : Nat.card ↥(_root_.commutator ↥S) = p := by
      obtain ⟨j, hj⟩ := (hSpg.to_subgroup (_root_.commutator ↥S)).exists_card_eq
      have hjpos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with rfl | h
        · exact absurd (Subgroup.card_eq_one.mp (by simpa using hj)) hcommne
        · exact h
      have hlecent : Nat.card ↥(_root_.commutator ↥S) ≤ p :=
        le_trans (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hcentre)) hZle
      have hge : p ≤ Nat.card ↥(_root_.commutator ↥S) := by
        rw [hj]
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ j := Nat.pow_le_pow_right hyp.p_prime.pos hjpos
      omega
    -- `|S| = p³`, so the quotient has order `p²`.
    have hScube : Nat.card ↥S = p ^ 3 := by
      obtain ⟨k, hk⟩ := hSpg.exists_card_eq
      rcases Nat.lt_or_ge k 3 with hk2 | hk3
      · exfalso
        have hup : Nat.card ↥S ≤ p ^ 2 := by
          rw [hk]; exact Nat.pow_le_pow_right hyp.p_prime.pos (by omega)
        exact habel (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p)
          (le_antisymm hup hp2))
      · have hk3' : k = 3 := by
          by_contra h
          have h4 : 4 ≤ k := by omega
          rw [hk] at hcard
          have : p ^ 4 ≤ p ^ k := Nat.pow_le_pow_right hyp.p_prime.pos h4
          have hlt : p ^ 3 < p ^ 4 :=
            Nat.pow_lt_pow_right hyp.p_prime.one_lt (by norm_num)
          omega
        rw [hk, hk3']
    show (_root_.commutator ↥S).index = p ^ 2
    have hmul : Nat.card ↥(_root_.commutator ↥S) * (_root_.commutator ↥S).index =
        Nat.card ↥S := (_root_.commutator ↥S).card_mul_index
    rw [hScomm, hScube] at hmul
    refine Nat.eq_of_mul_eq_mul_left hyp.p_prime.pos ?_
    rw [hmul]; ring

/-- **BG Theorem E.3(b), Step 2, the elided small case**: if `S' ≤ Z(S)` then `R₀ ⊄ S'`.

BG dispatches `|S| ≤ p³` by *"an examination of the `p`-groups of order at most `p³`"*.  No
examination is needed for the clause `R₀ ⊄ S'`: all that matters is that such an `S` has
nilpotency class `≤ 2`, i.e. `S' ≤ Z(S)`.  For if `R₀ ≤ S'`, then `S` centralizes `S'` hence
centralizes `R₀`, so `S ≤ C_R(R₀)`, which is **abelian**
(`isMulCommutative_centralizer_R₀`); then `S' = 1`, forcing `R₀ = 1` and contradicting
`|R₀| = p`.

Note this needs no `R₀ ≤ S` hypothesis: `R₀ ≤ S'` already puts `R₀` inside `S`. -/
theorem RegularOperatorSetup.not_le_derivedInG_of_derived_central [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R}
    (hcent : S ≤ Subgroup.centralizer (derivedInG S : Set R)) :
    ¬ hyp.R₀ ≤ derivedInG S := by
  intro hle
  have hSC : S ≤ Subgroup.centralizer (hyp.R₀ : Set R) :=
    hcent.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle))
  haveI : IsMulCommutative ↥S := IsMulCommutative.of_comm fun x y => by
    have hxy := hyp.isMulCommutative_centralizer_R₀.is_comm.comm
      (⟨(x : R), hSC x.2⟩ : ↥(Subgroup.centralizer (hyp.R₀ : Set R)))
      ⟨(y : R), hSC y.2⟩
    exact Subtype.ext
      (congrArg (fun z : ↥(Subgroup.centralizer (hyp.R₀ : Set R)) => (z : R)) hxy)
  have hbot : derivedInG S = ⊥ := by
    rw [derivedInG, commutator_eq_bot, Subgroup.map_bot]
  rw [hbot, le_bot_iff] at hle
  have hc := hyp.R₀_card
  rw [hle, Subgroup.card_bot] at hc
  exact hyp.p_prime.one_lt.ne hc

/-- `|S| ≤ p³` forces `S' ≤ Z(S)`, the hypothesis of
`not_le_derivedInG_of_derived_central`.

`Ch1.S04.nilpotencyClass_le_of_card_le_pow` gives `cl(S) ≤ 2`, i.e. `γ₃(S) = ⁅S', S⁆ = 1`;
that is exactly `S' ≤ Z(S)`, which transported to the ambient group reads
`S ≤ C_R(S')`. -/
theorem RegularOperatorSetup.derived_central_of_card_le_prime_cube [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hcard : Nat.card ↥S ≤ p ^ 3) :
    S ≤ Subgroup.centralizer (derivedInG S : Set R) := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  have hcentre := commutator_le_center_of_card_le_prime_cube
    (hyp.R_pGroup.to_subgroup S) hcard
  -- transport to the ambient group
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at *
  intro g hg
  obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
  have hcomm := congrArg (fun z : ↥S => (z : R))
    (Subgroup.mem_center_iff.mp (hcentre hg') ⟨x, hx⟩)
  simpa using hcomm.symm

/-- **BG Theorem E.3(b), Step 2, first conclusion of (E.13) — unconditionally**: for *any*
subgroup `S ≤ R` of exponent `p` containing `R₀`, `R₀ ⊄ S'`.

This is Step 2's `R₀ ⊄ S'` with both of BG's branches discharged: `|S| ≤ p³` by
`not_le_derivedInG_of_derived_central` (BG's elided *"examination of the `p`-groups of order
at most `p³`"*) and `|S| > p³` by the narrow route
(`not_le_derivedInG_of_three_le_pRank`), the two meeting at
`three_le_pRank_of_prime_cube_lt_card`.

⚠ BG additionally assumes `S` is `A`-invariant and `R₀ < S` *properly*; neither is used for
this clause. -/
theorem RegularOperatorSetup.not_le_derivedInG [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) :
    ¬ hyp.R₀ ≤ derivedInG S := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  rcases le_or_gt (Nat.card ↥S) (p ^ 3) with hle | hgt
  · exact hyp.not_le_derivedInG_of_derived_central
      (hyp.derived_central_of_card_le_prime_cube hle)
  · exact hyp.not_le_derivedInG_of_three_le_pRank hR₀S
      (three_le_pRank_of_prime_cube_lt_card (hyp.R_pGroup.to_subgroup S) hexp hgt)

/-- `R₀ ≤ Ω₁(R)`: every element of `R₀` has order dividing `|R₀| = p`. -/
theorem RegularOperatorSetup.R₀_le_omega [Finite R]
    (hyp : RegularOperatorSetup R B p q) : hyp.R₀ ≤ Omega R p 1 := by
  intro x hx
  refine Omega.mem_of_pow_eq_one ?_
  have h := pow_card_eq_one' (G := ↥hyp.R₀) (x := ⟨x, hx⟩)
  rw [hyp.R₀_card] at h
  simpa using congrArg (fun z : ↥hyp.R₀ => (z : R)) h

/-- **The engine behind BG (E.9)**: an automorphism `φ` of a group of prime order `p` is a
power map, `φ x = xʳ`; and if `φ^q = 1` then `r^q ≡ 1 (mod p)`.

BG applies this twice — first to `R₀` itself (the opening of (E.9)), then to each section
`Hᵢ/Hᵢ₊₁` of the chain, which (E.6) shows also has order `p`.  Stated abstractly so both
uses go through the same lemma, and with an **integer** exponent, as BG does. -/
theorem exists_zpow_eq_of_card_eq_prime {C : Type*} [Group C] {p q : ℕ} (hp : p.Prime)
    (hC : Nat.card C = p) (φ : MulAut C) (hφ : φ ^ q = 1) :
    ∃ r : ℤ, (∀ x : C, φ x = x ^ r) ∧ ((r : ZMod p) ^ q = 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; exact hp.pos.ne')
  haveI : IsCyclic C := isCyclic_of_prime_card hC
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  obtain ⟨k, hk⟩ := hg (φ g)
  have hord : orderOf g = p := by
    have htop : Subgroup.zpowers g = ⊤ := by ext x; simpa using hg x
    have hc := Nat.card_zpowers g
    rw [htop, Subgroup.card_top, hC] at hc
    exact hc.symm
  refine ⟨k, fun x => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hg x
    rw [← hm, map_zpow, ← hk, ← zpow_mul, ← zpow_mul, mul_comm]
  · have hiter : ∀ n : ℕ, (φ ^ n) g = g ^ (k ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hstep : (φ ^ (n + 1)) g = (φ ^ n) (φ g) := by rw [pow_succ]; rfl
        rw [hstep, ← hk, map_zpow, ih, ← zpow_mul, ← pow_succ]
    have hgq : g ^ (k ^ q) = g := by rw [← hiter q, hφ]; rfl
    have hz : g ^ (k ^ q - 1) = 1 := by rw [zpow_sub, hgq, zpow_one, mul_inv_cancel]
    have hdvd : (p : ℤ) ∣ k ^ q - 1 := by
      rw [← hord]; exact orderOf_dvd_iff_zpow_eq_one.mpr hz
    have hzero : ((k ^ q - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    push_cast at hzero
    exact sub_eq_zero.mp hzero

/-- **BG Theorem E.3(b), Step 2, (E.9), opening sentence**: *"Then `vᵃ = vʳ` for some integer
`r` such that `r^q ≡ 1 (mod p)`."*

`A` fixes `R₀`, which has prime order `p`, and `a^q = 1` because `|A| = q`; so
`exists_zpow_eq_of_card_eq_prime` applies to the induced automorphism. -/
theorem RegularOperatorSetup.exists_zpow_eq_act_of_mem_A [Finite R]
    (hyp : RegularOperatorSetup R B p q) {a : B} (ha : a ∈ hyp.A) :
    ∃ r : ℤ, (∀ v ∈ hyp.R₀, hyp.act a v = v ^ r) ∧ ((r : ZMod p) ^ q = 1) := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set ψ : ↥hyp.A →* MulAut ↥hyp.R₀ :=
    OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hyp.isAInvariant_R₀ with hψ
  have haq : (⟨a, ha⟩ : ↥hyp.A) ^ q = 1 := by
    have h := pow_card_eq_one' (G := ↥hyp.A) (x := ⟨a, ha⟩)
    rwa [hyp.A_card] at h
  obtain ⟨r, hr, hrq⟩ := exists_zpow_eq_of_card_eq_prime hyp.p_prime hyp.R₀_card
    (ψ ⟨a, ha⟩) (by rw [← map_pow, haq, map_one])
  refine ⟨r, fun v hv => ?_, hrq⟩
  have h2 := congrArg (fun z : ↥hyp.R₀ => (z : R)) (hr ⟨v, hv⟩)
  simpa [hψ, OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom_apply_val] using h2

/-- **BG Theorem E.3(b), Step 2, (E.11)**: `r ≢ 1 (mod p)` for `a ∈ A^#`.

If `a` acted on `R₀` as the *identity* power map it would fix `R₀ ≠ 1` pointwise, and `A`
acts regularly — `C_R(α) = 1` for `α ∈ A^#`.  This is the first point in Step 2 where the
setup's regularity hypothesis does any work. -/
theorem RegularOperatorSetup.zpow_exponent_ne_one [Finite R]
    (hyp : RegularOperatorSetup R B p q) {a : B} (ha : a ∈ hyp.A) (hane : a ≠ 1)
    {r : ℤ} (hr : ∀ v ∈ hyp.R₀, hyp.act a v = v ^ r) :
    (r : ZMod p) ≠ 1 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  intro h1
  -- `p ∣ r - 1`, so the `r`-th power map is the identity on `R₀`.
  have hdvd : (p : ℤ) ∣ r - 1 := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_
    push_cast
    rw [h1, sub_self]
  obtain ⟨c, hc⟩ := hdvd
  have hfix : ∀ v ∈ hyp.R₀, hyp.act a v = v := by
    intro v hv
    have hvp : v ^ p = 1 := by
      have h := pow_card_eq_one' (G := ↥hyp.R₀) (x := ⟨v, hv⟩)
      rw [hyp.R₀_card] at h
      simpa using congrArg (fun z : ↥hyp.R₀ => (z : R)) h
    have hsub : v ^ (r - 1) = 1 := by
      rw [hc, zpow_mul, zpow_natCast, hvp, one_zpow]
    calc hyp.act a v = v ^ r := hr v hv
      _ = v ^ ((r - 1) + 1) := by congr 1; ring
      _ = v ^ (r - 1) * v ^ (1 : ℤ) := zpow_add v _ _
      _ = v := by rw [hsub, zpow_one, one_mul]
  -- regularity then kills `R₀`
  have hbot : hyp.R₀ = ⊥ := by
    refine le_bot_iff.mp fun v hv => ?_
    exact Subgroup.mem_bot.mpr (hyp.A_regular a ha hane v (hfix v hv))
  have hc' := hyp.R₀_card
  rw [hbot, Subgroup.card_bot] at hc'
  exact hyp.p_prime.one_lt.ne hc'

/-- **BG Theorem E.3(b), Step 2, (E.8)**: `Hᵢ = S_{i+1}` — BG's chain out of `T` *is* the
lower central series of `S`, from its second term on.

BG derives this "similarly, by induction" after (E.7).  The induction is immediate once
(E.7) has identified `H₁ = S'`: both `Hᵢ₊₁ = ⁅Hᵢ, S⁆` and `γᵢ₊₁(S) = ⁅γᵢ(S), S⁆` are the
*same* recursion, so they agree forever after agreeing once.

(Indices: BG writes `S = S₁ ⊃ S₂ ⊃ ⋯`, so BG's `S_{i+1}` is mathlib's
`lowerCentralSeries ⊤ i`.) -/
theorem RegularOperatorSetup.iterCommutator_eq_lowerCentralSeries [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) :
    ∀ i : ℕ, OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) (i + 1)
      = Subgroup.lowerCentralSeries (⊤ : Subgroup ↥S) (i + 1)
  | 0 => by
      rw [Subgroup.top_lowerCentralSeries_one]
      exact (hyp.commutator_eq_and_card_quotient hR₀S hexp hS).1
  | i + 1 => by
      rw [OddOrder.Isaacs.Ch04.iterCommutator_succ, Subgroup.lowerCentralSeries_succ,
        hyp.iterCommutator_eq_lowerCentralSeries hR₀S hexp hS i]

/-- **BG Theorem E.3(b), Step 2, (E.7) — unconditionally**: `|S/S'| = p²` for every
exponent-`p` subgroup `S` properly containing `R₀`.

Both of BG's branches joined at `three_le_pRank_of_prime_cube_lt_card`, exactly as for
`not_le_derivedInG`. -/
theorem RegularOperatorSetup.card_quotient_commutator [Finite R]
    (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ < S)
    (hexp : ∀ x : ↥S, x ^ p = 1) :
    Nat.card (↥S ⧸ _root_.commutator ↥S) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  rcases le_or_gt (Nat.card ↥S) (p ^ 3) with hle | hgt
  · exact hyp.card_quotient_commutator_of_card_le_prime_cube hR₀S hexp hle
  · exact (hyp.commutator_eq_and_card_quotient hR₀S.le hexp
      (three_le_pRank_of_prime_cube_lt_card (hyp.R_pGroup.to_subgroup S) hexp hgt)).2

/-- `R₀ < Ω₁(R)` **properly**: `R₁ ≠ 1` is a `p`-group, so it contains an element of order
`p`, which lies in `Ω₁(R)` but not in `R₀` (the two are disjoint).

This is where the setup's cyclic factor `R₁` finally earns its keep: every earlier step of
Step 2 went through without it, but E.3(b)'s third clause is *false* for `S = R₀` (then
`|S/S'| = p`), so properness has to come from somewhere. -/
theorem RegularOperatorSetup.R₀_lt_omega [Finite R]
    (hyp : RegularOperatorSetup R B p q) : hyp.R₀ < Omega R p 1 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  refine lt_of_le_of_ne hyp.R₀_le_omega ?_
  intro heq
  -- an element of order `p` in `R₁`
  obtain ⟨k, hk⟩ := (hyp.R_pGroup.to_subgroup hyp.R₁).exists_card_eq
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hk)) hyp.R₁_ne_bot
    · exact h
  have hdvd : p ∣ Nat.card ↥hyp.R₁ := by
    rw [hk]; exact dvd_pow_self p hkpos.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥hyp.R₁) p hdvd
  have hzp : ((z : R)) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    simpa using congrArg (fun w : ↥hyp.R₁ => (w : R)) this
  have hzmem : (z : R) ∈ Omega R p 1 := Omega.mem_of_pow_eq_one (by simpa using hzp)
  have hzR₀ : (z : R) ∈ hyp.R₀ := heq ▸ hzmem
  have hzbot : (z : R) ∈ (⊥ : Subgroup R) :=
    (disjoint_iff.mp hyp.R₀_disjoint_R₁) ▸ Subgroup.mem_inf.mpr ⟨hzR₀, z.2⟩
  have hz1 : z = 1 := Subtype.ext (Subgroup.mem_bot.mp hzbot)
  rw [hz1, orderOf_one] at hz
  exact hyp.p_prime.one_lt.ne hz

/-- **BG Theorem E.3(b), first clause**: `Ω₁(R)` has exponent `p`.

**Status: honestly stated, not proved.**  BG's Steps 2--3: pick an `A`-invariant
subgroup `S` of exponent `p` maximal subject to containing `R₀ × Ω₁(R₁)`, bound
`|Ω₁(N_{Ω₁(R)}(S)) / S| ≤ p²` via `SCN`, narrowness (Lemma 5.2, Theorem 5.3(d))
and Lemma 4.5, then contradict maximality with Proposition E.2 — so this needs
`omega_pow_eq_one_of_lowerCentralSeries_eq_bot` (hence E.1) plus BG §5's narrow
`p`-group machinery. -/
theorem RegularOperatorSetup.omega_pow_eq_one [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) {g : R} (hg : g ∈ Omega R p 1) :
    g ^ p = 1 := by
  sorry

/-- **BG Theorem E.3(b), second clause**: `R₀ ⊄ (Ω₁(R))'`.

**Status: proved**, from Step 2's `R₀ ⊄ S'` (`not_le_derivedInG`) applied to `S = Ω₁(R)`.
The only input still owed is that `Ω₁(R)` has exponent `p` — the *first* clause,
`omega_pow_eq_one`, which is BG's Step 3 and remains `sorry`.  Citing it here is exactly
the intended dependency direction: BG proves (b) as one statement, Step 2 first and Step 3
on top of it. -/
theorem RegularOperatorSetup.R₀_not_le_derived_omega [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) :
    ¬ hyp.R₀ ≤ derivedInG (Omega R p 1) :=
  hyp.not_le_derivedInG hyp.R₀_le_omega fun x =>
    Subtype.ext (by simpa using hyp.omega_pow_eq_one x.2)

/-- **BG Theorem E.3(b), third clause**: `|Ω₁(R) / (Ω₁(R))'| = p²`.

**Status: proved**, from Step 2's (E.7) (`card_quotient_commutator`) applied to
`S = Ω₁(R)`, with `R₀ < Ω₁(R)` from `R₀_lt_omega`.  As for the second clause, the only
input still owed is the exponent statement `omega_pow_eq_one` — the first clause, BG's
Step 3, which remains `sorry`. -/
theorem RegularOperatorSetup.card_omega_abelianization [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) :
    Nat.card (↥(Omega R p 1) ⧸ _root_.commutator ↥(Omega R p 1)) = p ^ 2 :=
  hyp.card_quotient_commutator hyp.R₀_lt_omega fun x =>
    Subtype.ext (by simpa using hyp.omega_pow_eq_one x.2)

/-- **BG Theorem E.3(c)**: `|Ω₁(R)| ≤ p^q`.

**Status: honestly stated, not proved.**  BG's Step 2 counting argument: the
eigenvalues `rᵢ ≡ r₀ rⁱ (mod p)` of `α` on the `A`-invariant series
`T = H₀ ⊃ H₁ ⊃ ⋯ ⊃ Hₙ = 1` are all `≢ 1`, and `r` has order dividing `q` in
`(ℤ/p)ˣ`, forcing `n ≤ q - 1` and `|S| = p^{n+1} ≤ p^q`. -/
theorem RegularOperatorSetup.card_omega_le [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) :
    Nat.card ↥(Omega R p 1) ≤ p ^ q := by
  sorry

/-- **BG Theorem E.3(d)**: if `B` fixes `R₀ Φ(Ω₁(R))` then `B` fixes `R₀`.

**Status: honestly stated, not proved.**  BG's Step 4: every element of
`R₀ Φ(S) - Φ(S)` is `S`-conjugate into `R₀^#`, so `SB = S N_{SB}(R₀)`; a
Schur--Zassenhaus complement plus regularity of `A` pins the conjugating element
down to `1`. -/
theorem RegularOperatorSetup.B_fixes_R₀_of_fixes_frattini [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q)
    (hB : ∀ b : B, (hyp.act b) • (hyp.R₀ ⊔ frattiniInG (Omega R p 1)) =
      hyp.R₀ ⊔ frattiniInG (Omega R p 1)) :
    ∀ b : B, (hyp.act b) • hyp.R₀ = hyp.R₀ := by
  sorry

/-- **BG Proposition E.4**: in the situation of Theorem E.3, with
`S = Ω₁(R)`, if `|S| ≥ p⁴`, `B` acts regularly on `R`, and `B` does not fix `R₀`,
then `C_S(Z₂(S))` is abelian of index `p` in `S`.

**Status: honestly stated, not proved.**  BG's argument runs inside the
2-dimensional `𝔽_p`-space `S/S'`, comparing the eigenvalues `r, r₀` of `α` and
`t, t₀` of `β` on `R₀S'/S'` and `T/S'`, and derives the contradiction
`t₀ = t` from `j + 2 = k - i`.  It consumes all of Theorem E.3. -/
theorem RegularOperatorSetup.centralizer_upperCentralSeries_abelian_index_p
    [Finite R] [Finite B] (hyp : RegularOperatorSetup R B p q)
    (hcard : p ^ 4 ≤ Nat.card ↥(Omega R p 1))
    (hB_regular : ∀ b : B, b ≠ 1 → ∀ x : R, hyp.act b x = x → x = 1)
    (hB_not_fixes : ¬ ∀ b : B, (hyp.act b) • hyp.R₀ = hyp.R₀) :
    IsMulCommutative
        ↥(Subgroup.centralizer
          ((Subgroup.upperCentralSeries ↥(Omega R p 1) 2 : Subgroup ↥(Omega R p 1)) :
            Set ↥(Omega R p 1))) ∧
      (Subgroup.centralizer
          ((Subgroup.upperCentralSeries ↥(Omega R p 1) 2 : Subgroup ↥(Omega R p 1)) :
            Set ↥(Omega R p 1))).index = p := by
  sorry

end RegularOperator

/-! ## E.5: the maximal-subgroup application -/

section MaximalApplication

open OddOrder.BG.Ch3.S12 OddOrder.BG.Ch4.S14

variable {G : Type*} [Group G]

/-- **BG Corollary E.5**.  Let `G` be a minimal simple group of odd order, `M` a
maximal subgroup of `G`, `x ∈ M_σ` of prime order `p` with `C_G(x) ⊄ M`, and
`N ∈ ℳ(C_G(x))` with `N ∉ ℳ_𝓕`.  Assume in addition that

* (i) `|M / M'|` is prime, or
* (ii) `Ω₁(O_p(M))` has no normal abelian subgroup of index `p`.

Then every maximal subgroup of `G` is of Type I or Type II.

**Status: honestly stated, not proved.**  The hypothesis block is exactly the one
consumed by the formalized BG Corollary 15.9
(`OddOrder.BG.Ch4.S16.centralizer_escape_final_local`), with `orderOf x = p`
added; note `x ∈ M_σ` together with `orderOf x = p` gives `x ∈ M_σ^#` for free.
The proof needs (ii) ⇒ (i) via Theorem E.3 and Proposition E.4 applied to
`O_p(M), K₁, E`, and then the §14 counting argument
(`|𝒞_G(L̃)|`-disjointness, Lemma 14.5, Theorem 14.7) to rule out a maximal
subgroup that is neither Type I nor Type II.  So it is gated on E.3/E.4 above. -/
theorem maximalSubgroups_isTypeI_or_isTypeII [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M N : Subgroup G} {x : G} {p : ℕ}
    (hM : M ∈ maximalSubgroups G) (hp : p.Prime)
    (hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hord : orderOf x = p)
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (hNmem : N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hNnotF : N ∉ maximalTypeFFamily G)
    (halt : ((derivedInG M).subgroupOf M).index.Prime ∨
      ¬ ∃ A : Subgroup ↥(Omega ↥(opiCoreInG {p} M) p 1),
          A.Normal ∧ IsMulCommutative ↥A ∧ A.index = p) :
    ∀ L : Subgroup G, L ∈ maximalSubgroups G →
      OddOrder.GroupTheory.IsTypeI L ∨ OddOrder.GroupTheory.IsTypeII L := by
  sorry

end MaximalApplication

end OddOrder.BG.AppE
