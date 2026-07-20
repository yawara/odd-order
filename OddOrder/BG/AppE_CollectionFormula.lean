/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S04_SmallRankBasic
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.GroupTheory.HallCollection
import OddOrder.GroupTheory.HallPetresco
import OddOrder.GroupTheory.OmegaSubgroup
import OddOrder.GroupTheory.RegularPGroup

/-!
# BG Appendix E, E.1 and E.2: the collection formula and regular `p`-groups

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, pp. 157--159 — Philip Hall's commutator collection
formula `(E.1)` and its regular-`p`-group consequences `(E.2)`.

This is the upstream half of `OddOrder/BG/AppE_FurtherResults.lean`, split off when that
file reached the repo's 2000-line limit (issue 0134).  The module name of the downstream
file is unchanged, so consumers are unaffected.

Everything here is **proved and sorry-free**.  The general machinery lives one level
further upstream, in `OddOrder/GroupTheory/`: `HallCollection.lean` (the ordered tail and
its collapse lemmas), `HallPetresco.lean` (`(E.1)` in general form, via Mann's route), and
`RegularPGroup.lean` (BG's unnumbered "Step 1", stated for arbitrary groups).
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

end OddOrder.BG.AppE
