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
| E.3(b)(c)(d), E.4, E.5 main clauses | honest statements, `sorry` |
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

**Status: honestly stated, not proved** (BG Step 2, via `S = R₀T` with
`R₀ ∩ T = 1` and `S' ≤ T`). -/
theorem RegularOperatorSetup.R₀_not_le_derived_omega [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) :
    ¬ hyp.R₀ ≤ derivedInG (Omega R p 1) := by
  sorry

/-- **BG Theorem E.3(b), third clause**: `|Ω₁(R) / (Ω₁(R))'| = p²`.

**Status: honestly stated, not proved** (BG (E.7): `H₁ = S²` and `|S/S²| = p²`). -/
theorem RegularOperatorSetup.card_omega_abelianization [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) :
    Nat.card (↥(Omega R p 1) ⧸ _root_.commutator ↥(Omega R p 1)) = p ^ 2 := by
  sorry

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
