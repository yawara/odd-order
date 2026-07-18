/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S04_SmallRankBasic
import OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults
import OddOrder.GroupTheory.CriticalSubgroup
import OddOrder.GroupTheory.HallCollection
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
| E.1 general (`hallCollection`) | honest statement, `sorry` (needs Hall's collecting process) |
| E.1 class `≤ 3` (`hallCollection_of_class_le_three`) | **proved, sorry-free** (all `n`) |
| E.1 class `≤ 2` (`hallCollection_of_class_le_two`) | **proved, sorry-free** (subsumed by the above) |
| E.1 general framework | `OddOrder/GroupTheory/HallCollection.lean`, **sorry-free** |
| E.2 Step 1 (`pow_mul_of_commutator_pow_eq_one`) | **proved**, but cites the sorried E.1 |
| E.2(a) (`omega_pow_eq_one_of_lowerCentralSeries_eq_bot`) | honest statement, `sorry` |
| E.2(a) class `≤ 2` | already in repo: `GroupTheory.Omega.pow_eq_one_of_class_le_two` |
| E.2(b) (`pow_mul_of_commutator_le_omega`) | **proved** from E.2(a) + Step 1 |
| E.2(b) class `≤ 2` (`pow_mul_of_class_le_two`) | **proved, sorry-free** |
| E.3(a) (`card_A_dvd_half_p_sub_one`) | **proved, sorry-free** |
| E.3(b)(c)(d), E.4, E.5 | honest statements, `sorry` |
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

**Status: honestly stated, not proved.**  The proof is Hall's commutator
collecting process (BG cites Suzuki, *Group Theory II*, pp. 37--41; also Huppert,
*Endliche Gruppen I*, pp. 315--318).  Proved sorry-free below for nilpotence
class `≤ 3` (`hallCollection_of_class_le_three`, all `n` at once), which subsumes
the class-`≤ 2` case (`hallCollection_of_class_le_two`).

**Precise obstruction to the general case.**  The reusable framework lives in
`OddOrder/GroupTheory/HallCollection.lean` (all sorry-free): the exact one-step
recursion `pow_succ_collect`

`xⁿ yⁿ = (x y)ⁿ T  ⟹  x^{n+1} y^{n+1} = (x y)^{n+1} (⁅x⁻¹, ((x y)ⁿ)⁻¹⁆ T)^y`,

the weight law `commutatorElement_mem_lowerCentralSeries_add`
(`[G_i, G_j] ≤ G_{i+j}`), and the reduction `exists_hallCollection_of_residue`,
which shows that E.1 for a fixed `n` is exactly a congruence *modulo* `γ_n`
(the top exponent `C(n, n) = 1` absorbs any `γ_n`-residue, so there is no hidden
exactness to prove).

What is missing is the induction on the *weight* `k`.  Suppose the weights
`2, …, k - 1` have been collected, leaving a residue `w(n) ∈ γ_k`.  One must
produce `c_k ∈ γ_k` with `w(n) ≡ c_k^{C(n,k)} (mod γ_{k+1})`, i.e. one must know
that `w(n)` is a `C(n,k)`-th power in the abelian group `γ_k / γ_{k+1}`.  That is
a genuine divisibility statement, and it is what Hall's collecting process
establishes: in the free group `γ_k / γ_{k+1}` is free abelian on the basic
commutators of weight `k`, and the coefficient of each basic commutator in
`w(n)` is a `ℤ`-polynomial in `n` divisible by `C(n,k)`.

Two prerequisites for that argument are absent from both mathlib and this
repository: (i) free nilpotent groups together with a basis of *basic
commutators* for each factor `γ_k / γ_{k+1}` (mathlib has `FreeGroup` but no
free nilpotent quotient and no basic-commutator basis — `Mathlib/GroupTheory/
Commutator/**` and `Mathlib/GroupTheory/Nilpotent.lean` contain neither
`Petrescu` nor `collecting`), and (ii) the polynomiality in `n` of the collection
coefficients (Hall polynomials / Lazard).  Building (i) is the real cost; once
it exists, the weight induction above closes E.1 by the standard argument.

The class-`≤ 3` case avoids all of this because there the residue lives in the
*central* factor `γ₃`, whose two generators are explicit — see
`class_three_tail_aux`. -/
theorem hallCollection (x y : G) (n : ℕ) :
    ∃ c : ℕ → G,
      (∀ r, 2 ≤ r → r ≤ n → c r ∈ (⊤ : Subgroup G).lowerCentralSeries (r - 1)) ∧
      x ^ n * y ^ n = (x * y) ^ n * collectionTail c n := by
  sorry

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
      show _ ∈ (⊤ : Subgroup G).lowerCentralSeries 1
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
      simp only [if_pos rfl]
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

/-- **BG Proposition E.2, Step 1.**  If `R` has nilpotence class at most `p - 1`
(equivalently `γ_p(R) = 1`, i.e. `lowerCentralSeries R (p-1) = ⊥` in mathlib's
indexing) and `R'` has exponent dividing `p`, then `x ↦ x ^ p` is a
homomorphism.

Proof (BG's Step 1): apply E.1 with `n = p`.  The last collected term `c_p` lies
in `γ_p(R) = 1`; each earlier `c_r` (`2 ≤ r ≤ p-1`) lies in `γ_{r-1}(R) ≤ R'`,
so `c_r ^ p = 1`, and `p ∣ C(p, r)` for `0 < r < p`, whence `c_r ^ {C(p,r)} = 1`.

**Status: proved**, but the proof cites the still-sorried `hallCollection`, so it
is not yet axiom-clean.  For class `≤ 2` see `pow_mul_of_class_le_two`, which is
sorry-free. -/
theorem pow_mul_of_commutator_pow_eq_one {p : ℕ} (hp : p.Prime)
    (hgamma : (⊤ : Subgroup R).lowerCentralSeries (p - 1) = ⊥)
    (hexp : ∀ g ∈ _root_.commutator R, g ^ p = 1) (x y : R) :
    x ^ p * y ^ p = (x * y) ^ p := by
  obtain ⟨c, hc, hform⟩ := hallCollection x y p
  have htail : collectionTail c p = 1 := by
    rw [collectionTail, hallTail]
    refine List.prod_eq_one ?_
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    obtain ⟨hr2, hrlt⟩ := List.mem_range'_1.mp hr
    have hp2 := hp.two_le
    have hrle : r ≤ p := by omega
    have hmem := hc r hr2 hrle
    rcases eq_or_lt_of_le hrle with rfl | hlt
    · -- `c_p ∈ γ_p(R) = 1`.
      rw [hgamma, Subgroup.mem_bot] at hmem
      rw [hmem, one_pow]
    · -- `2 ≤ r < p`: `c_r ∈ R'` and `p ∣ C(p, r)`.
      have hle : (⊤ : Subgroup R).lowerCentralSeries (r - 1) ≤
          (⊤ : Subgroup R).lowerCentralSeries 1 :=
        Subgroup.lowerCentralSeries_antitone ⊤ (by omega)
      rw [Subgroup.top_lowerCentralSeries_one] at hle
      obtain ⟨k, hk⟩ := hp.dvd_choose_self (by omega) hlt
      rw [hk, pow_mul, hexp _ (hle hmem), one_pow]
  rw [hform, htail, mul_one]

/-- **BG Proposition E.2(a).**  If `R` is a `p`-group of nilpotence class at most
`p - 1`, then `Ω₁(R)` has exponent `1` or `p`.

**Status: honestly stated, not proved.**  BG's Step 2 is an induction on `|R|`:
reduce to `R = ⟨x, y⟩` with `x, y` of order dividing `p`, take a maximal (hence
normal, index `p`) subgroup `M ⊇ ⟨y⟩`, apply the inductive hypothesis to get
`Ω₁(M)` of exponent `p`, note `R / Ω₁(M)` is cyclic so `R' ≤ Ω₁(M)`, and finish
with Step 1 (`pow_mul_of_commutator_pow_eq_one`).  That induction, plus Step 1's
dependence on `hallCollection`, is what remains.

For nilpotence class `≤ 2` and odd `p` this is already available sorry-free in
the repo as `OddOrder.GroupTheory.Omega.pow_eq_one_of_class_le_two`. -/
theorem omega_pow_eq_one_of_lowerCentralSeries_eq_bot [Finite R] {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R) (hgamma : (⊤ : Subgroup R).lowerCentralSeries (p - 1) = ⊥)
    {g : R} (hg : g ∈ Omega R p 1) : g ^ p = 1 := by
  sorry

/-- **BG Proposition E.2(b).**  If `R` is a `p`-group of nilpotence class at most
`p - 1` and `R' ≤ Ω₁(R)`, then `x ↦ x ^ p` is a homomorphism.

**Status: proved** from E.2(a) and Step 1 — exactly BG's derivation
("(b) will follow from (a) and Step 1").  It therefore inherits their sorries. -/
theorem pow_mul_of_commutator_le_omega [Finite R] {p : ℕ} [hp : Fact p.Prime]
    (hR : IsPGroup p R) (hgamma : (⊤ : Subgroup R).lowerCentralSeries (p - 1) = ⊥)
    (hR' : _root_.commutator R ≤ Omega R p 1) (x y : R) :
    (x * y) ^ p = x ^ p * y ^ p :=
  (pow_mul_of_commutator_pow_eq_one hp.out hgamma
    (fun _ hg => omega_pow_eq_one_of_lowerCentralSeries_eq_bot hR hgamma (hR' hg)) x y).symm

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
