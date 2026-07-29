/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.LinearCharacter
import OddOrder.GroupTheory.WielandtFixedPoint
import OddOrder.BG.Ch3_MaximalSubgroups.S13_Corollary132

/-!
# `|N| = |C_N(X)|^{|X|}` for `K`-invariant `2`-subgroups

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §1, Proposition, p. 117:

> But `[K, P] ⋊ P` is a Frobenius group acting on `S/Q₀` and `[K, P]` acts
> without fixed points on `S/Q₀` …

This file assembles `⁅K, X⁆` for `X ≤ V`, the kernel of that Frobenius group.
The plan is to feed `Q` and `Q₀` themselves to Wielandt's formula rather than the
quotient `S/Q₀`, which is shorter: the fixed-point-freeness of the kernel comes
straight from Ch. I §2 Proposition 1(a) (`K` acts fixed-point-freely on `Q`),
whereas the corresponding statement for `S/Q₀` would need extra work.

The Frobenius structure needs `W = 1` only through `⁅K, X⁆ ≠ 1`: if `X`
centralized `K` it would lie in `W = C_V(K)`.

## Main results

* `Hypothesis.commutator_K_le_K` — `⁅K, X⁆ ≤ K` for `X ≤ D`.
* `Hypothesis.commutator_K_ne_bot` — `⁅K, X⁆ ≠ 1` for `1 ≠ X ≤ V` when `W = 1`.
* `Hypothesis.conj_mem_commutator_K_of_mem` — `X` normalizes `⁅K, X⁆`.
* `Hypothesis.isFrobeniusGroup_commutator_K_sup` — `⁅K, X⁆ ⋊ X` is a Frobenius
  group when `|X|` is prime to `|K|`.
* `Hypothesis.natCard_eq_pow_natCard_inf_centralizer` — Wielandt's formula
  `|N| = |C_N(X)|^{|X|}` for every `H`-invariant `2`-subgroup `N ≤ Q`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open scoped Pointwise
open scoped commutatorElement

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-! ## `⁅K, X⁆` -/

/-- `⁅K, X⁆ ≤ K` for any `X ≤ D`. -/
theorem commutator_K_le_K {X : Subgroup G} (hXD : X ≤ hyp.D) : ⁅hyp.K, X⁆ ≤ hyp.K := by
  rw [Subgroup.commutator_le]
  intro k hk x hx
  have : k * (x * k⁻¹ * x⁻¹) ∈ hyp.K :=
    hyp.K.mul_mem hk (hyp.conj_mem_K_of_mem_D (hXD hx) (hyp.K.inv_mem hk))
  simpa [commutatorElement_def, mul_assoc] using this

/-- **`⁅K, X⁆ ≠ 1`** for `1 ≠ X ≤ V` when `W = 1`: otherwise `X` would
centralize `K`, so `X ≤ C_V(K) = W = 1`. -/
theorem commutator_K_ne_bot (hW : hyp.W = ⊥) {X : Subgroup G} (hXV : X ≤ hyp.V)
    (hXne : X ≠ ⊥) : ⁅hyp.K, X⁆ ≠ ⊥ := by
  intro hbot
  refine hXne (le_bot_iff.mp ?_)
  rw [← hW]
  intro x hx
  refine ⟨hXV hx, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  have hkK : k ∈ hyp.K := by rw [← SetLike.mem_coe, hyp.coe_K]; exact hk
  have hmem : ⁅k, x⁆ ∈ ⁅hyp.K, X⁆ := Subgroup.commutator_mem_commutator hkK hx
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at hmem
  exact hmem.eq

/-- `X ≤ D` normalizes `⁅K, X⁆`: conjugation by `x ∈ X` carries `K` to `K` and
`X` to `X`, hence the commutator subgroup to itself (`Subgroup.map_commutator`). -/
theorem conj_mem_commutator_K_of_mem {X : Subgroup G} (hXD : X ≤ hyp.D) {x : G}
    (hx : x ∈ X) {z : G} (hz : z ∈ ⁅hyp.K, X⁆) : x * z * x⁻¹ ∈ ⁅hyp.K, X⁆ := by
  have hmap : (⁅hyp.K, X⁆).map (MulAut.conj x).toMonoidHom ≤ ⁅hyp.K, X⁆ := by
    rw [Subgroup.map_commutator]
    refine Subgroup.commutator_mono ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact hyp.conj_mem_K_of_mem_D (hXD hx) hk
    · rintro _ ⟨y, hy, rfl⟩
      exact X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)
  exact hmap ⟨z, hz, rfl⟩

/-! ## The Frobenius group `⁅K, X⁆ ⋊ X` -/

/-- **`⁅K, X⁆ ⋊ X` is a Frobenius group** (Peterfalvi Part II, Ch. III §1, p. 117).

`K` is cyclic (`K_isCyclic`) and `X ≤ V ≤ D` normalizes it (`D_le_normalizer_K`), so
under a coprime action the commutator meets the centralizer trivially
(`BG.Ch3.S13.commutator_inf_centralizer_eq_bot_of_isCommutative`); `X` has prime
order and `⁅K, X⁆ ≠ 1` because `W = 1`.  Isaacs Thm 6.4 in the form
`isFrobeniusGroup_of_prime_complement_fixedFree` then applies.

⚠ The coprimality hypothesis is not automatic in Ch. III: `|K| = |Q₀| − 1` and
`|X| = p`, so it says `p ∤ q − 1`, equivalently `p ∤ q₀ − 1` where
`q₀ = |C_{Q₀}(X)|` (Fermat, using `q = q₀^p`).  The book asserts the Frobenius
property unconditionally; that is only valid when this holds — automatic in Ch. II,
where `|Q₀| = 2^p`.  The complementary case `p ∣ q₀ − 1` is handled by
Hilbert 90 instead (`OddOrder.RingAut.exists_ne_zero_mul_pow_eq`). -/
theorem isFrobeniusGroup_commutator_K_sup (hW : hyp.W = ⊥) {X : Subgroup G}
    (hXV : X ≤ hyp.V) (hXne : X ≠ ⊥) (hp : (Nat.card ↥X).Prime)
    (hcop : Nat.Coprime (Nat.card ↥X) (Nat.card ↥hyp.K)) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(⁅hyp.K, X⁆ ⊔ X)
      ((⁅hyp.K, X⁆).subgroupOf (⁅hyp.K, X⁆ ⊔ X))
      (X.subgroupOf (⁅hyp.K, X⁆ ⊔ X)) := by
  classical
  have hXD : X ≤ hyp.D := hXV.trans hyp.V_le_D
  set U : Subgroup G := ⁅hyp.K, X⁆ with hU
  set L : Subgroup G := U ⊔ X with hL
  have hUL : U ≤ L := le_sup_left
  have hXL : X ≤ L := le_sup_right
  have hUK : U ≤ hyp.K := hyp.commutator_K_le_K hXD
  -- `X` normalizes `U`, hence so does `L`
  have hXnorm : X ≤ Subgroup.normalizer (U : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hyp.conj_mem_commutator_K_of_mem hXD hg hz, fun hz => ?_⟩
    have h2 := hyp.conj_mem_commutator_K_of_mem hXD (X.inv_mem hg) hz
    simpa [mul_assoc] using h2
  have hLnorm : L ≤ Subgroup.normalizer (U : Set G) :=
    sup_le Subgroup.le_normalizer hXnorm
  haveI : (U.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUL).mpr hLnorm
  -- `U ⊓ X = ⊥` since `U ≤ K` and `X ≤ V`
  have hUX : U ⊓ X = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : y ∈ hyp.K ⊓ hyp.V := ⟨hUK hy.1, hXV hy.2⟩
    rwa [hyp.K_inf_V_eq_bot] at this
  -- the complement
  have hdisj : Disjoint (U.subgroupOf L) (X.subgroupOf L) := by
    rw [Subgroup.disjoint_def]
    intro y hy1 hy2
    have : (y : G) ∈ U ⊓ X :=
      ⟨Subgroup.mem_subgroupOf.mp hy1, Subgroup.mem_subgroupOf.mp hy2⟩
    rw [hUX, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hsup : (U.subgroupOf L) ⊔ (X.subgroupOf L) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUL hXL, ← hL, Subgroup.subgroupOf_self]
  have hcompl : Subgroup.IsComplement' (U.subgroupOf L) (X.subgroupOf L) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
    rw [← Subgroup.normal_mul, hsup]
    rfl
  -- the remaining hypotheses of Isaacs Thm 6.4
  have hXcard : Nat.card ↥(X.subgroupOf L) = Nat.card ↥X := by
    rw [← Subgroup.inf_subgroupOf_right]
    have h1 : Nat.card ↥((X ⊓ L).subgroupOf L) = Nat.card ↥(X ⊓ L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : X ⊓ L ≤ L)).toEquiv
    rw [h1, inf_eq_left.mpr hXL]
  have hUne : U.subgroupOf L ≠ ⊥ := by
    intro hbot
    refine hyp.commutator_K_ne_bot hW hXV hXne ?_
    rw [eq_bot_iff]
    intro y hy
    have hyL : y ∈ L := hUL hy
    have : (⟨y, hyL⟩ : ↥L) ∈ U.subgroupOf L := Subgroup.mem_subgroupOf.mpr hy
    rw [hbot, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg (Subtype.val (p := fun z => z ∈ L)) this
  have hKcomm : ∀ a ∈ hyp.K, ∀ b ∈ hyp.K, a * b = b * a := by
    haveI := hyp.K_isCyclic
    letI : CommGroup ↥hyp.K := IsCyclic.commGroup
    intro a ha b hb
    exact congrArg (Subtype.val (p := fun z => z ∈ hyp.K))
      (mul_comm (⟨a, ha⟩ : ↥hyp.K) ⟨b, hb⟩)
  have hbot : ⁅hyp.K, X⁆ ⊓ Subgroup.centralizer (X : Set G) = ⊥ :=
    OddOrder.BG.Ch3.S13.commutator_inf_centralizer_eq_bot_of_isCommutative hKcomm
      (hXD.trans hyp.D_le_normalizer_K) hcop
  have hFix : ∀ n ∈ U.subgroupOf L,
      (∀ a ∈ X.subgroupOf L, a * n * a⁻¹ = n) → n = 1 := by
    intro n hn hfix
    have hnU : (n : G) ∈ U := Subgroup.mem_subgroupOf.mp hn
    have hnC : (n : G) ∈ Subgroup.centralizer (X : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
      have hgL : g ∈ L := hXL hg
      have hgX : (⟨g, hgL⟩ : ↥L) ∈ X.subgroupOf L := Subgroup.mem_subgroupOf.mpr hg
      have := congrArg (Subtype.val (p := fun z => z ∈ L)) (hfix _ hgX)
      have hval : g * (n : G) * g⁻¹ = (n : G) := this
      calc g * (n : G) = (g * (n : G) * g⁻¹) * g := by group
        _ = (n : G) * g := by rw [hval]
    have : (n : G) ∈ (⊥ : Subgroup G) := hbot ▸ ⟨hnU, hnC⟩
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  exact OddOrder.Isaacs.Ch06.isFrobeniusGroup_of_prime_complement_fixedFree hcompl
    (by rw [hXcard]; exact hp) hUne hFix


/-! ## Wielandt's formula for `H`-invariant subgroups of `Q` -/

/-- **`|N| = |C_N(X)|^{|X|}`** for every `H`-invariant subgroup `N ≤ Q`
(Peterfalvi Part II, Ch. III §1, p. 117, in the corrected form).

The Frobenius group `⁅K, X⁆ ⋊ X` acts on `N`, and its kernel acts
fixed-point-freely because `K` already does on `Q` (Ch. I §2 Proposition 1(a),
`Q_inf_centralizer_eq_bot_of_mem_KSet`).  Wielandt's fixed-point formula
(Peterfalvi (9.1), `natCard_eq_pow_natCard_inf_centralizer_of_kernel_fpf`) then
gives the order relation.

Applied with `N = Q` and `N = Q₀` this is what contradicts the `PSL(2, ℓ)`
branch of Ch. I §3 Proposition 1(c) in case (3): there `C_Q(X) = C_{Q₀}(X)`, so
the two instances give `|Q| = |Q₀|`, against `|Q| = |Q₀|³`. -/
theorem natCard_eq_pow_natCard_inf_centralizer (hW : hyp.W = ⊥) {X : Subgroup G}
    (hXV : X ≤ hyp.V) (hXne : X ≠ ⊥) (hp : (Nat.card ↥X).Prime)
    (hcop : Nat.Coprime (Nat.card ↥X) (Nat.card ↥hyp.K))
    {N : Subgroup G} (hNQ : N ≤ hyp.Q) (hN2 : IsPGroup 2 ↥N)
    (hNnorm : ∀ h ∈ hyp.H, ∀ y ∈ N, h * y * h⁻¹ ∈ N) :
    Nat.card ↥N = Nat.card ↥(N ⊓ Subgroup.centralizer (X : Set G)) ^ Nat.card ↥X := by
  classical
  have hXD : X ≤ hyp.D := hXV.trans hyp.V_le_D
  set U : Subgroup G := ⁅hyp.K, X⁆ with hU
  have hUK : U ≤ hyp.K := hyp.commutator_K_le_K hXD
  have hUD : U ≤ hyp.D := hUK.trans hyp.K_le_D
  have hUXD : U ⊔ X ≤ hyp.D := sup_le hUD hXD
  -- the acting group normalizes `N`
  have hnorm : U ⊔ X ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    have hgH : g ∈ hyp.H := hyp.D_le_H (hUXD hg)
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hNnorm g hgH z hz, fun hz => ?_⟩
    have h2 := hNnorm g⁻¹ (hyp.H.inv_mem hgH) _ hz
    simpa [mul_assoc] using h2
  -- `N` is solvable and coprime to the acting group
  have hsolv : IsSolvable ↥N := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := hN2.isNilpotent
    infer_instance
  have hcop2 : Nat.Coprime (Nat.card ↥N) (Nat.card ↥(U ⊔ X)) := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk]
    refine Nat.Coprime.pow_left k ?_
    have hdvd : Nat.card ↥(U ⊔ X) ∣ Nat.card ↥hyp.D := Subgroup.card_dvd_of_le hUXD
    have hodd : Odd (Nat.card ↥(U ⊔ X)) := hyp.D_odd.of_dvd_nat hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (by simpa [Nat.two_dvd_ne_zero] using Nat.odd_iff.mp hodd)
  -- the kernel `⁅K, X⁆` acts fixed-point-freely on `N ≤ Q`
  have hUne : U ≠ ⊥ := hyp.commutator_K_ne_bot hW hXV hXne
  obtain ⟨k, hkU, hk1⟩ : ∃ k, k ∈ U ∧ k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hUne (le_bot_iff.mp fun y hy => Subgroup.mem_bot.mpr (hcon y hy))
  have hkKSet : k ∈ hyp.KSet := by
    rw [← hyp.coe_K]; exact hUK hkU
  have hUfpf : ∀ n ∈ N, (∀ u ∈ U, u * n * u⁻¹ = n) → n = 1 := by
    intro n hn hfix
    have hnQ : n ∈ hyp.Q := hNQ hn
    have hnC : n ∈ Subgroup.centralizer ({k} : Set G) := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hval := hfix k hkU
      calc n * k = k * (k⁻¹ * n * k) := by group
        _ = k * n := by
            congr 1
            calc k⁻¹ * n * k = k⁻¹ * (k * n * k⁻¹) * k := by rw [hval]
              _ = n := by group
    have : n ∈ hyp.Q ⊓ Subgroup.centralizer ({k} : Set G) := ⟨hnQ, hnC⟩
    rw [hyp.Q_inf_centralizer_eq_bot_of_mem_KSet hkKSet hk1, Subgroup.mem_bot] at this
    exact this
  exact OddOrder.GroupTheory.natCard_eq_pow_natCard_inf_centralizer_of_kernel_fpf
    hnorm (hyp.isFrobeniusGroup_commutator_K_sup hW hXV hXne hp hcop) hsolv hcop2 hUfpf


end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
