/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.FeitSibleyTheorem
import Mathlib.GroupTheory.PGroup

/-!
# Peterfalvi Appendix IV: Feit–Sibley — reduction-step machinery (pp. 146–148)

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix IV, pp. 146–148.  Machinery for the reduction steps (1)–(3) of the proof
of the Theorem (campaign issue 1054), on top of the supporting layer of
`OddOrder.Peterfalvi.Appendices.FeitSibleyTheorem`.

This file provides the **quotient-level fixed-point-free bounds**: the reductions
repeatedly bound quotient orders such as `|Z/Q₂|`, `|Q₁/Q₂|` from below by `d + 1`
("since `D` acts without fixed points on …").  The subgroup-level bounds
(`d_dvd_card_sub_one_of_le_Q1` etc. in `FeitSibleyTheorem`) extend to quotients
because fixed-point-freeness descends: a nonidentity `δ ∈ D` cannot fix a
nontrivial coset `wN` of a `D`-invariant `N ≤ Q₁` — a prime-order power `δ'` of `δ`
would act on the finite set `wN`, whose size `|N|` is prime to `ord δ'`
(`|Q|` and `|D|` are coprime), so `δ'` would fix some point `y ∈ wN`
(`IsPGroup.card_modEq_card_fixedPoints`), and `y ≠ 1` since `1 ∉ wN`,
contradicting `D_fixedPointFree_on_Q1`.
-/

namespace OddOrder.Peterfalvi.Appendices.FeitSibley

open OddOrder.RepresentationTheory

open scoped Pointwise commutatorElement ComplexOrder

variable {G : Type*} [Group G]

namespace Hypothesis

variable (hyp : Hypothesis G)

/-! ## Fixed-point-freeness descends to cosets and quotients -/

/-- **A nonidentity `δ ∈ D` moves every nontrivial coset of a `D`-invariant
`N ≤ Q₁`**: if conjugation by `δ` keeps `w ∈ Q₁` inside its own left `N`-coset
(`w⁻¹ · (δwδ⁻¹) ∈ N`), then `w ∈ N`.  Core of the quotient-level
fixed-point-free bounds of the reduction steps (1)–(3) (pp. 146–148).

Proof: the elements of `D` keeping `w` in its coset form a subgroup `K`
containing `δ`; a prime-order power `δ' ∈ K` (order `p ∣ ord δ ∣ |D|`, so
`p ∤ |N|` by `coprime_Q_D`) acts by conjugation on the coset `w • N` of size
`|N| ≢ 0 (mod p)`, hence fixes some `y ∈ w • N`
(`IsPGroup.card_modEq_card_fixedPoints`); if `w ∉ N` then `1 ∉ w • N`, so
`y ≠ 1` contradicts `D_fixedPointFree_on_Q1`. -/
theorem mem_of_inv_mul_conj_mem_of_ne_one [Finite G] {N : Subgroup G}
    (hNQ1 : N ≤ hyp.Q1)
    (hNinv : ∀ δ ∈ hyp.D, ∀ z ∈ N, δ * z * δ⁻¹ ∈ N)
    {δ w : G} (hδD : δ ∈ hyp.D) (hδ1 : δ ≠ 1) (hw : w ∈ hyp.Q1)
    (hconj : w⁻¹ * (δ * w * δ⁻¹) ∈ N) :
    w ∈ N := by
  classical
  by_contra hwN
  -- the subgroup of elements of `D` keeping `w` inside its own left `N`-coset
  set K : Subgroup G :=
    { carrier := {g | g ∈ hyp.D ∧ w⁻¹ * (g * w * g⁻¹) ∈ N}
      one_mem' := ⟨hyp.D.one_mem, by simp⟩
      mul_mem' := by
        rintro g₁ g₂ ⟨hg₁D, hg₁⟩ ⟨hg₂D, hg₂⟩
        refine ⟨hyp.D.mul_mem hg₁D hg₂D, ?_⟩
        have hkey : w⁻¹ * ((g₁ * g₂) * w * (g₁ * g₂)⁻¹)
            = (w⁻¹ * (g₁ * w * g₁⁻¹)) * (g₁ * (w⁻¹ * (g₂ * w * g₂⁻¹)) * g₁⁻¹) := by
          group
        rw [hkey]
        exact N.mul_mem hg₁ (hNinv g₁ hg₁D _ hg₂)
      inv_mem' := by
        rintro g ⟨hgD, hg⟩
        refine ⟨hyp.D.inv_mem hgD, ?_⟩
        have hkey : w⁻¹ * (g⁻¹ * w * g⁻¹⁻¹)
            = g⁻¹ * (w⁻¹ * (g * w * g⁻¹))⁻¹ * g⁻¹⁻¹ := by
          group
        rw [hkey]
        exact hNinv g⁻¹ (hyp.D.inv_mem hgD) _ (N.inv_mem hg) } with hK_def
  have hδK : δ ∈ K := ⟨hδD, hconj⟩
  -- a prime-order power `δ'` of `δ`
  have hord1 : orderOf δ ≠ 1 := fun h => hδ1 (orderOf_eq_one_iff.mp h)
  set p := (orderOf δ).minFac with hp_def
  have hp : p.Prime := Nat.minFac_prime hord1
  haveI : Fact p.Prime := ⟨hp⟩
  have hordpos : 0 < orderOf δ := orderOf_pos δ
  set δ' := δ ^ (orderOf δ / p) with hδ'_def
  have hδ'ord : orderOf δ' = p := by
    rw [hδ'_def, orderOf_pow,
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd (Nat.minFac_dvd _))]
    exact Nat.div_div_self (Nat.minFac_dvd _) hordpos.ne'
  have hδ'1 : δ' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hδ'ord
    exact hp.one_lt.ne hδ'ord
  have hδ'D : δ' ∈ hyp.D := hyp.D.pow_mem hδD _
  have hδ'K : δ' ∈ K := K.pow_mem hδK _
  have hzpK : Subgroup.zpowers δ' ≤ K := Subgroup.zpowers_le.mpr hδ'K
  -- the coset `w • N` and the conjugation action of `⟨δ'⟩` on it
  set C : Set G := w • (N : Set G) with hC_def
  have hmemC : ∀ x : G, x ∈ C ↔ w⁻¹ * x ∈ N := fun x => by
    simp [hC_def, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  have hclosure : ∀ g ∈ Subgroup.zpowers δ', ∀ x ∈ C, g * x * g⁻¹ ∈ C := by
    intro g hg x hx
    obtain ⟨hgD, hgw⟩ := hzpK hg
    rw [hmemC] at hx ⊢
    have hkey : w⁻¹ * (g * x * g⁻¹)
        = (w⁻¹ * (g * w * g⁻¹)) * (g * (w⁻¹ * x) * g⁻¹) := by
      group
    rw [hkey]
    exact N.mul_mem hgw (hNinv g hgD _ hx)
  haveI : Finite ↥C := Set.Finite.to_subtype (Set.toFinite C)
  letI : SMul ↥(Subgroup.zpowers δ') ↥C :=
    ⟨fun g x => ⟨(g : G) * x * (g : G)⁻¹, hclosure g g.2 x x.2⟩⟩
  have hsmul_def : ∀ (g : ↥(Subgroup.zpowers δ')) (x : ↥C),
      ((g • x : ↥C) : G) = (g : G) * x * (g : G)⁻¹ := fun _ _ => rfl
  letI : MulAction ↥(Subgroup.zpowers δ') ↥C :=
    { one_smul := fun x => Subtype.ext (by rw [hsmul_def]; simp)
      mul_smul := fun g₁ g₂ x => Subtype.ext (by
        rw [hsmul_def, hsmul_def, hsmul_def]
        simp only [Subgroup.coe_mul]
        group) }
  -- `⟨δ'⟩` is a `p`-group and `p ∤ |C| = |N|`
  have hpgroup : IsPGroup p ↥(Subgroup.zpowers δ') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hδ'ord, pow_one])
  have hpD : p ∣ Nat.card ↥hyp.D := by
    have h1 : orderOf (⟨δ, hδD⟩ : ↥hyp.D) = orderOf δ := by
      simp [← orderOf_injective hyp.D.subtype Subtype.coe_injective
        (⟨δ, hδD⟩ : ↥hyp.D)]
    have h2 : orderOf δ ∣ Nat.card ↥hyp.D := by
      rw [← h1]; exact orderOf_dvd_natCard _
    exact dvd_trans (Nat.minFac_dvd _) h2
  have hpN : ¬ p ∣ Nat.card ↥N := by
    intro hdvdN
    have hNQ : Nat.card ↥N ∣ Nat.card ↥hyp.Q :=
      Subgroup.card_dvd_of_le (le_trans hNQ1 hyp.Q1_le_Q)
    have hgcd : p ∣ Nat.gcd (Nat.card ↥hyp.Q) (Nat.card ↥hyp.D) :=
      Nat.dvd_gcd (hdvdN.trans hNQ) hpD
    rw [Nat.Coprime.gcd_eq_one hyp.coprime_Q_D] at hgcd
    exact hp.ne_one (Nat.dvd_one.mp hgcd)
  have hcardC : Nat.card ↥C = Nat.card ↥N := by
    rw [hC_def]
    simpa using Set.natCard_smul_set w (N : Set G)
  -- `δ'` fixes a point of the coset
  have hmod := hpgroup.card_modEq_card_fixedPoints ↥C
  have hfixne :
      Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers δ') ↥C) ≠ 0 := by
    intro h0
    rw [h0, hcardC] at hmod
    exact hpN (Nat.modEq_zero_iff_dvd.mp hmod)
  obtain ⟨⟨⟨y, hyC⟩, hyfix⟩⟩ :
      Nonempty ↥(MulAction.fixedPoints ↥(Subgroup.zpowers δ') ↥C) :=
    (Nat.card_ne_zero.mp hfixne).1
  have hyfix' : δ' * y * δ'⁻¹ = y :=
    congrArg Subtype.val (hyfix ⟨δ', Subgroup.mem_zpowers δ'⟩)
  -- the fixed point is a nonidentity element of `Q₁` fixed by `δ' ≠ 1`
  have hy1 : y ≠ 1 := by
    intro h1
    have hyN := (hmemC y).mp hyC
    rw [h1, mul_one] at hyN
    exact hwN (by simpa using N.inv_mem hyN)
  have hyQ1 : y ∈ hyp.Q1 := by
    have hyN := (hmemC y).mp hyC
    have hy : y = w * (w⁻¹ * y) := by group
    rw [hy]
    exact hyp.Q1.mul_mem hw (hNQ1 hyN)
  exact hy1 (hyp.D_fixedPointFree_on_Q1 δ' hδ'D hδ'1 y hyQ1 hyfix')

/-- **`d ∣ |W⧸N| − 1` for a `D`-invariant section `N ≤ W ≤ Q₁`** (the
quotient-level form of `d_dvd_card_sub_one_of_le_Q1`): `D` acts by conjugation
on the coset space `W⧸N` with `1` as unique fixed point
(`mem_of_inv_mul_conj_mem_of_ne_one`) and free elsewhere, so the orbit count
gives `d ∣ |W⧸N| − 1`.  This is the "f.p.f." input of the reduction steps
(1)–(3): `|Z/Q₂| ≡ 1 (mod d)` etc. (pp. 146–148). -/
theorem d_dvd_card_quotient_sub_one_of_le_Q1 [Finite G] {N W : Subgroup G}
    (hNW : N ≤ W) (hWQ1 : W ≤ hyp.Q1)
    (hNinv : ∀ δ ∈ hyp.D, ∀ z ∈ N, δ * z * δ⁻¹ ∈ N)
    (hWinv : ∀ δ ∈ hyp.D, ∀ z ∈ W, δ * z * δ⁻¹ ∈ W) :
    hyp.d ∣ Nat.card (↥W ⧸ N.subgroupOf W) - 1 := by
  classical
  by_cases hd1 : hyp.d = 1
  · rw [hd1]; exact one_dvd _
  -- the conjugation action of `D` on the coset space `W ⧸ (N ∩ W)`
  letI : SMul ↥hyp.D (↥W ⧸ N.subgroupOf W) :=
    ⟨fun δ => Quotient.map'
      (fun w => (⟨(δ : G) * w * (δ : G)⁻¹, hWinv δ δ.2 w w.2⟩ : ↥W))
      (fun a b hab => by
        rw [QuotientGroup.leftRel_apply] at hab ⊢
        rw [Subgroup.mem_subgroupOf] at hab ⊢
        change ((δ : G) * a * (δ : G)⁻¹)⁻¹ * ((δ : G) * b * (δ : G)⁻¹) ∈ N
        have hkey : ((δ : G) * a * (δ : G)⁻¹)⁻¹ * ((δ : G) * b * (δ : G)⁻¹)
            = (δ : G) * ((a : G)⁻¹ * b) * (δ : G)⁻¹ := by
          group
        rw [hkey]
        exact hNinv δ δ.2 _ hab)⟩
  have hsmul_mk : ∀ (δ : ↥hyp.D) (w : ↥W),
      δ • (Quotient.mk'' w : ↥W ⧸ N.subgroupOf W)
        = Quotient.mk'' (⟨(δ : G) * w * (δ : G)⁻¹, hWinv δ δ.2 w w.2⟩ : ↥W) :=
    fun _ _ => rfl
  letI : MulAction ↥hyp.D (↥W ⧸ N.subgroupOf W) :=
    { one_smul := fun x => by
        induction x using Quotient.inductionOn' with
        | h w =>
          rw [hsmul_mk]
          congr 1
          exact Subtype.ext (by simp)
      mul_smul := fun δ₁ δ₂ x => by
        induction x using Quotient.inductionOn' with
        | h w =>
          rw [hsmul_mk, hsmul_mk, hsmul_mk]
          congr 1
          exact Subtype.ext (by
            simp only [Subgroup.coe_mul]
            group) }
  -- `1` is a fixed point
  have h1fix : (Quotient.mk'' (1 : ↥W) : ↥W ⧸ N.subgroupOf W)
      ∈ MulAction.fixedPoints ↥hyp.D (↥W ⧸ N.subgroupOf W) := by
    intro δ
    rw [hsmul_mk]
    congr 1
    exact Subtype.ext (by simp)
  -- a nonidentity `δ` fixing a coset forces the trivial coset
  have hkey : ∀ (δ : ↥hyp.D), δ ≠ 1 → ∀ (x : ↥W ⧸ N.subgroupOf W),
      δ • x = x → x = Quotient.mk'' (1 : ↥W) := by
    intro δ hδ1 x
    induction x using Quotient.inductionOn' with
    | h w =>
      intro hfix
      rw [hsmul_mk] at hfix
      have hmem : ((⟨(δ : G) * w * (δ : G)⁻¹, hWinv δ δ.2 w w.2⟩ : ↥W))⁻¹ * w
          ∈ N.subgroupOf W := by
        have h := Quotient.eq''.mp hfix
        rwa [QuotientGroup.leftRel_apply] at h
      rw [Subgroup.mem_subgroupOf] at hmem
      have hmem' : ((δ : G) * w * (δ : G)⁻¹)⁻¹ * (w : G) ∈ N := hmem
      have hconj : (w : G)⁻¹ * ((δ : G) * w * (δ : G)⁻¹) ∈ N := by
        have h2 := N.inv_mem hmem'
        rwa [mul_inv_rev, inv_inv] at h2
      have hδG1 : (δ : G) ≠ 1 := fun h => hδ1 (Subtype.ext (by simpa using h))
      have hwN : (w : G) ∈ N :=
        hyp.mem_of_inv_mul_conj_mem_of_ne_one (le_trans hNW hWQ1) hNinv
          δ.2 hδG1 (hWQ1 w.2) hconj
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      rw [Subgroup.mem_subgroupOf]
      change (w : G)⁻¹ * (1 : G) ∈ N
      rw [mul_one]
      exact N.inv_mem hwN
  have huniq : ∀ x : ↥W ⧸ N.subgroupOf W,
      x ∈ MulAction.fixedPoints ↥hyp.D (↥W ⧸ N.subgroupOf W) →
      x = Quotient.mk'' (1 : ↥W) := by
    intro x hx
    haveI : Nontrivial ↥hyp.D := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      have hpos : 0 < Nat.card ↥hyp.D := Nat.card_pos
      have hne : Nat.card ↥hyp.D ≠ 1 := hd1
      omega
    obtain ⟨δ0, hδ0⟩ := exists_ne (1 : ↥hyp.D)
    exact hkey δ0 hδ0 x (hx δ0)
  have hfree : ∀ x : ↥W ⧸ N.subgroupOf W,
      x ∉ MulAction.fixedPoints ↥hyp.D (↥W ⧸ N.subgroupOf W) →
      Nat.card (MulAction.orbit ↥hyp.D x) = Nat.card ↥hyp.D := by
    intro x hx
    have hstab : MulAction.stabilizer ↥hyp.D x = ⊥ := by
      rw [eq_bot_iff]
      intro δ hδ
      rw [Subgroup.mem_bot]
      by_contra hδ1
      apply hx
      have hx1 : x = Quotient.mk'' (1 : ↥W) :=
        hkey δ hδ1 x (MulAction.mem_stabilizer_iff.mp hδ)
      rw [hx1]
      exact h1fix
    have hinj : Function.Injective (fun δ : ↥hyp.D => δ • x) := by
      intro δ₁ δ₂ heq
      have heq' : δ₁ • x = δ₂ • x := heq
      have hmem : δ₂⁻¹ * δ₁ ∈ MulAction.stabilizer ↥hyp.D x := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, heq', ← mul_smul,
          inv_mul_cancel, one_smul]
      rw [hstab, Subgroup.mem_bot] at hmem
      exact (inv_mul_eq_one.mp hmem).symm
    exact Nat.card_range_of_injective hinj
  exact OddOrder.GroupTheory.FreeActionOrbitCount.dvd_card_sub_one_of_free_off_unique_fixed
    (Quotient.mk'' (1 : ↥W)) h1fix huniq hfree

/-- **`|W⧸N| ≥ d + 1` for a proper `D`-invariant section `N < W ≤ Q₁`**:
`d ∣ |W⧸N| − 1` and `|W⧸N| > 1`.  The quotient-level form of
`d_add_one_le_card_of_le_Q1`, giving the reduction steps' lower bounds
`|Z/Q₂| ≥ d + 1`, `|Q₁/Q₂| ≥ (d+1)²` (via two Sylow components) on
pp. 146–148. -/
theorem d_add_one_le_card_quotient_of_le_Q1 [Finite G] {N W : Subgroup G}
    (hNW : N ≤ W) (hWQ1 : W ≤ hyp.Q1)
    (hNinv : ∀ δ ∈ hyp.D, ∀ z ∈ N, δ * z * δ⁻¹ ∈ N)
    (hWinv : ∀ δ ∈ hyp.D, ∀ z ∈ W, δ * z * δ⁻¹ ∈ W)
    (hWN : ¬ W ≤ N) :
    hyp.d + 1 ≤ Nat.card (↥W ⧸ N.subgroupOf W) := by
  have hdvd := hyp.d_dvd_card_quotient_sub_one_of_le_Q1 hNW hWQ1 hNinv hWinv
  have hlt : 1 < Nat.card (↥W ⧸ N.subgroupOf W) := by
    obtain ⟨w, hwW, hwN⟩ := SetLike.not_le_iff_exists.mp hWN
    have hne : (Quotient.mk'' (⟨w, hwW⟩ : ↥W) : ↥W ⧸ N.subgroupOf W)
        ≠ Quotient.mk'' (1 : ↥W) := by
      intro h
      have hmem := Quotient.eq''.mp h
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hmem
      apply hwN
      have h2 : w⁻¹ * (1 : G) ∈ N := hmem
      rw [mul_one] at h2
      simpa using N.inv_mem h2
    haveI : Nontrivial (↥W ⧸ N.subgroupOf W) := ⟨_, _, hne⟩
    exact Finite.one_lt_card
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0, mul_zero] at hk; omega
    · exact h
  have hle : hyp.d ≤ hyp.d * k := Nat.le_mul_of_pos_right hyp.d hkpos
  omega

/-! ## Index arithmetic for the counting bound (1.1)

The reductions read the two-quotient difference of
`card_quot_sub_le_of_forall_deg_of_sum_le` as
`|H⧸S'Q₂| − |H⧸S'Q₁| = d·|S⧸S'|·(|Q₁⧸Q₂| − 1)` and drop `|S⧸S'| ≥ 1`.  The
bridges: `Q₁ ∩ S'Q₂ = Q₂` (direct-product intersection), the index tower
`|H⧸R| = |Q₁⧸(Q₁ ∩ R)|·|H⧸RQ₁|` (second isomorphism at the `relIndex` level),
and `d ∣ |H⧸RQ₁|` (`RQ₁ ≤ Q`, `[H:Q] = d`). -/

/-- **Subgroups of `S` normalise subgroups of `Q₁`**: elementwise commutation
(`S_commutes_Q1`) puts any `A' ≤ S` inside the normaliser of any `B' ≤ Q₁`, so
`A' ⊔ B'` is the set product `A'·B'`
(`Subgroup.coe_mul_of_left_le_normalizer_right`). -/
theorem le_normalizer_of_le_S_of_le_Q1 {A' B' : Subgroup G}
    (hA' : A' ≤ hyp.S) (hB' : B' ≤ hyp.Q1) :
    A' ≤ Subgroup.normalizer (B' : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    have hc : s * q = q * s := hyp.S_commutes_Q1 s (hA' hs) q (hB' hq)
    have hfix : s * q * s⁻¹ = q := by rw [hc]; group
    rw [hfix]
    exact hq
  · intro hq
    have hc : s⁻¹ * (s * q * s⁻¹) = (s * q * s⁻¹) * s⁻¹ :=
      hyp.S_commutes_Q1 s⁻¹ (hyp.S.inv_mem (hA' hs)) _ (hB' hq)
    have hq' : q = s * q * s⁻¹ := by
      calc q = s⁻¹ * (s * q * s⁻¹) * s := by group
        _ = (s * q * s⁻¹) * s⁻¹ * s := by rw [hc]
        _ = s * q * s⁻¹ := by group
    rw [hq']
    exact hq

/-- **Direct-product intersection**: `Q₁ ⊓ (A' ⊔ B') = B'` for `A' ≤ S`,
`B' ≤ Q₁`.  Since `A'` centralises `Q₁ ⊇ B'` (`S_commutes_Q1`), the join is the
set product `A'·B'`, and the `A'`-part of a member of `Q₁` lands in
`S ⊓ Q₁ = 1`.  Instantiated at `R = S'⊔Q₂` (reduction (1)) and `SZ` (the (1.2)
index `|Q⧸SZ| = |Q₁⧸Z|`). -/
theorem Q1_inf_sup_eq {A' B' : Subgroup G} (hA' : A' ≤ hyp.S) (hB' : B' ≤ hyp.Q1) :
    hyp.Q1 ⊓ (A' ⊔ B') = B' := by
  refine le_antisymm ?_ (le_inf hB' le_sup_right)
  rintro x ⟨hxQ1, hxsup⟩
  have hnorm : A' ≤ Subgroup.normalizer (B' : Set G) :=
    hyp.le_normalizer_of_le_S_of_le_Q1 hA' hB'
  have hxmul : x ∈ (A' : Set G) * (B' : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A' B' hnorm]
    exact hxsup
  obtain ⟨s, hs, q, hq, heq⟩ := hxmul
  have hsQ1 : s ∈ hyp.Q1 := by
    have hseq : s = x * q⁻¹ := by rw [← heq]; group
    rw [hseq]
    exact hyp.Q1.mul_mem hxQ1 (hyp.Q1.inv_mem (hB' hq))
  have hs1 : s = 1 := by
    have hmem : s ∈ hyp.S ⊓ hyp.Q1 := ⟨hA' hs, hsQ1⟩
    rwa [hyp.S_inf_Q1_eq_bot, Subgroup.mem_bot] at hmem
  have hxq : x = q := by rw [← heq, hs1]; simp
  rw [hxq]
  exact hq

/-- **The index tower** `|H⧸R| = |Q₁⧸Q₂|·|H⧸RQ₁|` for `R ⊴ H` (in-`H` form)
with `Q₁ ⊓ R = Q₂`: `relIndex` multiplicativity along `R ≤ RQ₁ ≤ H` plus the
second isomorphism `R.relIndex (R ⊔ Q₁) = (R ⊓ Q₁).relIndex Q₁`
(`relIndex_sup_left`/`inf_relIndex_right`). -/
theorem card_quot_eq_card_quot_Q1_mul [Finite G] {R Q₂ : Subgroup G}
    (hinf : hyp.Q1 ⊓ R = Q₂)
    [(R.subgroupOf hyp.H).Normal] :
    Nat.card (↥hyp.H ⧸ R.subgroupOf hyp.H)
      = Nat.card (↥hyp.Q1 ⧸ Q₂.subgroupOf hyp.Q1)
        * Nat.card (↥hyp.H ⧸ ((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H))) := by
  classical
  have hNK : (R.subgroupOf hyp.H) ⊓ (hyp.Q1.subgroupOf hyp.H)
      = Q₂.subgroupOf hyp.H := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, ← hinf]
    exact and_comm
  have h2 : (R.subgroupOf hyp.H).relIndex
        ((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H))
      = Q₂.relIndex hyp.Q1 := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, hNK,
      Subgroup.relIndex_subgroupOf (hyp.Q1_le_Q.trans hyp.Q_le_H)]
  have h3 : Nat.card (↥hyp.Q1 ⧸ Q₂.subgroupOf hyp.Q1) = Q₂.relIndex hyp.Q1 :=
    (Subgroup.index_eq_card _).symm
  calc Nat.card (↥hyp.H ⧸ R.subgroupOf hyp.H)
      = (R.subgroupOf hyp.H).index := (Subgroup.index_eq_card _).symm
    _ = (R.subgroupOf hyp.H).relIndex
          ((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H))
        * ((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H)).index :=
        (Subgroup.relIndex_mul_index le_sup_left).symm
    _ = Nat.card (↥hyp.Q1 ⧸ Q₂.subgroupOf hyp.Q1)
        * Nat.card (↥hyp.H ⧸ ((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H))) := by
        rw [h2, ← h3, Subgroup.index_eq_card]

/-- **`d` divides `|H⧸RQ₁|`** for `R ≤ Q`: `RQ₁ ≤ Q`, so `[H:Q] = d`
(`index_Q_subgroupOf_eq_d`) divides `[H : RQ₁]`. -/
theorem d_dvd_card_quot_sup_Q1 [Finite G] {R : Subgroup G} (hRQ : R ≤ hyp.Q) :
    hyp.d ∣ Nat.card (↥hyp.H ⧸ ((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H))) := by
  have hle : (R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H)
      ≤ hyp.Q.subgroupOf hyp.H := by
    refine sup_le ?_ ?_
    · intro y hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact hRQ hy
    · intro y hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact hyp.Q1_le_Q hy
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [hyp.index_Q_subgroupOf_eq_d] at hdvd
  rwa [Subgroup.index_eq_card] at hdvd

/-- **The (1.1) quotient extraction**: from the counting bound
`|H⧸R| − |H⧸RQ₁| ≤ d²·c` (the output of
`card_quot_sub_le_of_forall_deg_of_sum_le` at `c = 2a`), the `Q₁`-side factor
obeys `|Q₁⧸Q₂| − 1 ≤ d·c`: the difference is `|H⧸RQ₁|·(|Q₁⧸Q₂| − 1)` with
`|H⧸RQ₁| ≥ d`.  This is Peterfalvi's "`|Q₁/Q₂| − 1 ≤ 2ψ(1)/d` (drop
`|S/S'| ≥ 1`)" on p. 146. -/
theorem card_quot_Q1_sub_one_le_of_card_quot_sub_le [Finite G] {R Q₂ : Subgroup G}
    (hRQ : R ≤ hyp.Q) (hinf : hyp.Q1 ⊓ R = Q₂)
    [(R.subgroupOf hyp.H).Normal]
    {c : ℝ}
    (hcount : (Nat.card (↥hyp.H ⧸ R.subgroupOf hyp.H) : ℝ)
        - (Nat.card (↥hyp.H ⧸ ((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H))) : ℝ)
      ≤ (hyp.d : ℝ) ^ 2 * c) :
    (Nat.card (↥hyp.Q1 ⧸ Q₂.subgroupOf hyp.Q1) : ℝ) - 1 ≤ (hyp.d : ℝ) * c := by
  classical
  set q : ℕ := Nat.card (↥hyp.Q1 ⧸ Q₂.subgroupOf hyp.Q1) with hq_def
  set M : ℕ := Nat.card (↥hyp.H ⧸ ((R.subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H)))
    with hM_def
  have hbridge := hyp.card_quot_eq_card_quot_Q1_mul (Q₂ := Q₂) hinf
  have hkey : (M : ℝ) * ((q : ℝ) - 1) ≤ (hyp.d : ℝ) ^ 2 * c := by
    rw [hbridge, ← hq_def, ← hM_def] at hcount
    push_cast at hcount
    nlinarith [hcount]
  have hq1 : 1 ≤ (q : ℝ) := by
    have : 0 < q := Nat.card_pos
    exact_mod_cast this
  have hMd : (hyp.d : ℝ) ≤ (M : ℝ) := by
    have hdvd := hyp.d_dvd_card_quot_sup_Q1 hRQ
    have : hyp.d ≤ M := Nat.le_of_dvd Nat.card_pos hdvd
    exact_mod_cast this
  have hstep : (hyp.d : ℝ) * ((q : ℝ) - 1) ≤ (hyp.d : ℝ) * ((hyp.d : ℝ) * c) := by
    calc (hyp.d : ℝ) * ((q : ℝ) - 1)
        ≤ (M : ℝ) * ((q : ℝ) - 1) :=
          mul_le_mul_of_nonneg_right hMd (by linarith)
      _ ≤ (hyp.d : ℝ) ^ 2 * c := hkey
      _ = (hyp.d : ℝ) * ((hyp.d : ℝ) * c) := by ring
  have hd_pos : (0 : ℝ) < (hyp.d : ℝ) := by exact_mod_cast hyp.d_pos
  exact le_of_mul_le_mul_left hstep hd_pos

/-- **`S ⊔ Q₁ = Q`**: the subgroup-lattice form of the set product
`S_mul_Q1_eq_Q`. -/
theorem sup_S_Q1_eq_Q : hyp.S ⊔ hyp.Q1 = hyp.Q := by
  refine le_antisymm (sup_le hyp.S_le_Q hyp.Q1_le_Q) ?_
  intro q hq
  rw [← SetLike.mem_coe, ← hyp.S_mul_Q1_eq_Q] at hq
  obtain ⟨s, hs, y, hy, heq⟩ := hq
  rw [← heq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hy)

/-- **The (1.2) index conversion**: `[Q : SZ] = |Q₁⧸Z|` for `Z ≤ Q₁`, in the
doubly relativised form output by `exists_deg_sq_le_of_mem_SsetOf`
(`a² ≤ [Q-in-H : D₀-in]` at `D₀ = S ⊔ Z`).  Combines the index tower
`card_quot_eq_card_quot_Q1_mul` at `R = S⊔Z` (`Q₁ ⊓ SZ = Z`,
`SZ ⊔ Q₁ = Q`) with `[H : Q] = d` and cancellation. -/
theorem index_subgroupOf_sup_S_eq [Finite G] {Z : Subgroup G} (hZQ1 : Z ≤ hyp.Q1)
    [((hyp.S ⊔ Z).subgroupOf hyp.H).Normal] :
    (((hyp.S ⊔ Z).subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).index
      = Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) := by
  classical
  have hinf : hyp.Q1 ⊓ (hyp.S ⊔ Z) = Z := hyp.Q1_inf_sup_eq le_rfl hZQ1
  have hbridge := hyp.card_quot_eq_card_quot_Q1_mul (R := hyp.S ⊔ Z) hinf
  have hsup : ((hyp.S ⊔ Z).subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H)
      = hyp.Q.subgroupOf hyp.H := by
    rw [← Subgroup.subgroupOf_sup
      (sup_le (hyp.S_le_Q.trans hyp.Q_le_H)
        ((hZQ1.trans hyp.Q1_le_Q).trans hyp.Q_le_H))
      (hyp.Q1_le_Q.trans hyp.Q_le_H)]
    congr 1
    rw [sup_assoc, sup_eq_right.mpr hZQ1, hyp.sup_S_Q1_eq_Q]
  rw [hsup] at hbridge
  have hle : (hyp.S ⊔ Z).subgroupOf hyp.H ≤ hyp.Q.subgroupOf hyp.H := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (sup_le hyp.S_le_Q (hZQ1.trans hyp.Q1_le_Q)) hy
  have htower : (((hyp.S ⊔ Z).subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).index
      * (hyp.Q.subgroupOf hyp.H).index = ((hyp.S ⊔ Z).subgroupOf hyp.H).index :=
    Subgroup.relIndex_mul_index hle
  have hQd : Nat.card (↥hyp.H ⧸ hyp.Q.subgroupOf hyp.H) = hyp.d := by
    rw [← Subgroup.index_eq_card, hyp.index_Q_subgroupOf_eq_d]
  rw [hyp.index_Q_subgroupOf_eq_d,
    Subgroup.index_eq_card ((hyp.S ⊔ Z).subgroupOf hyp.H), hbridge, hQd] at htower
  exact Nat.eq_of_mul_eq_mul_right hyp.d_pos htower

/-- **The `Q₁`-internal index tower** `|Q₁⧸Q₂| = |Q₁⧸Z|·|Z⧸Q₂|` for
`Q₂ ≤ Z ≤ Q₁` (`relIndex` multiplicativity; no normality needed for the coset
counts). -/
theorem card_quot_Q1_eq_mul {Q₂ Z : Subgroup G} (hQ₂Z : Q₂ ≤ Z) (hZQ1 : Z ≤ hyp.Q1) :
    Nat.card (↥hyp.Q1 ⧸ Q₂.subgroupOf hyp.Q1)
      = Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) * Nat.card (↥Z ⧸ Q₂.subgroupOf Z) := by
  have h := Subgroup.relIndex_mul_relIndex Q₂ Z hyp.Q1 hQ₂Z hZQ1
  have e1 : Nat.card (↥hyp.Q1 ⧸ Q₂.subgroupOf hyp.Q1) = Q₂.relIndex hyp.Q1 :=
    (Subgroup.index_eq_card _).symm
  have e2 : Nat.card (↥hyp.Q1 ⧸ Z.subgroupOf hyp.Q1) = Z.relIndex hyp.Q1 :=
    (Subgroup.index_eq_card _).symm
  have e3 : Nat.card (↥Z ⧸ Q₂.subgroupOf Z) = Q₂.relIndex Z :=
    (Subgroup.index_eq_card _).symm
  rw [e1, e2, e3, ← h, mul_comm]

/-- **The reduction (1) final arithmetic**: the counting bound
`q₂ − 1 ≤ 2da` (1.1), the degree bound `a² ≤ qz` (1.2), the tower
`q₂ = qz·zq`, and the fixed-point-free lower bounds `zq ≥ d+1`,
`q₂ ≥ (d+1)²` are jointly contradictory.  Chain:
`zq·(q₂−1)² ≤ 4d²·a²·zq ≤ 4d²·qz·zq = 4d²·q₂` and
`q₂·(q₂−2) < (q₂−1)²`, so `zq·(q₂−2) < 4d²`; but
`zq·(q₂−2) ≥ (d+1)·((d+1)²−2) ≥ 4d²` since `(d−1)(d²+1) ≥ 0`.
(Sharper than the book's `(d+1)²−2 < 4d whence d ≤ 2`: the product form is
already contradictory for every `d ≥ 1`, so no separate `d = 1` case is
needed.) -/
theorem false_of_reduction_one_bounds {d a q₂ qz zq : ℕ}
    (hd : 1 ≤ d)
    (h1 : (q₂ : ℝ) - 1 ≤ (d : ℝ) * (2 * a))
    (h2 : a ^ 2 ≤ qz)
    (h3 : q₂ = qz * zq)
    (h4 : d + 1 ≤ zq)
    (h5 : (d + 1) ^ 2 ≤ q₂) : False := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h2R : (a : ℝ) ^ 2 ≤ (qz : ℝ) := by exact_mod_cast h2
  have h3R : (q₂ : ℝ) = (qz : ℝ) * (zq : ℝ) := by exact_mod_cast h3
  have h4R : (d : ℝ) + 1 ≤ (zq : ℝ) := by exact_mod_cast h4
  have h5R : ((d : ℝ) + 1) ^ 2 ≤ (q₂ : ℝ) := by exact_mod_cast h5
  have haR : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hq₂4 : (4 : ℝ) ≤ (q₂ : ℝ) := by nlinarith
  have hzq0 : (0 : ℝ) < (zq : ℝ) := by linarith
  -- `(q₂ − 1)² ≤ 4d²a²`
  have k1 : ((q₂ : ℝ) - 1) ^ 2 ≤ 4 * (d : ℝ) ^ 2 * (a : ℝ) ^ 2 := by
    nlinarith [mul_le_mul h1 h1 (by linarith) (by positivity)]
  -- `zq·(q₂ − 1)² ≤ 4d²·q₂`
  have k2 : (zq : ℝ) * ((q₂ : ℝ) - 1) ^ 2 ≤ 4 * (d : ℝ) ^ 2 * (q₂ : ℝ) := by
    calc (zq : ℝ) * ((q₂ : ℝ) - 1) ^ 2
        ≤ (zq : ℝ) * (4 * (d : ℝ) ^ 2 * (a : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left k1 hzq0.le
      _ ≤ (zq : ℝ) * (4 * (d : ℝ) ^ 2 * (qz : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hzq0.le
          nlinarith
      _ = 4 * (d : ℝ) ^ 2 * (q₂ : ℝ) := by rw [h3R]; ring
  -- strict drop to `zq·(q₂ − 2) < 4d²`
  have k3 : (zq : ℝ) * ((q₂ : ℝ) * ((q₂ : ℝ) - 2)) < (zq : ℝ) * ((q₂ : ℝ) - 1) ^ 2 := by
    apply mul_lt_mul_of_pos_left _ hzq0
    nlinarith
  have k5 : (zq : ℝ) * ((q₂ : ℝ) - 2) < 4 * (d : ℝ) ^ 2 := by
    have k4 : (zq : ℝ) * ((q₂ : ℝ) - 2) * (q₂ : ℝ) < 4 * (d : ℝ) ^ 2 * (q₂ : ℝ) := by
      nlinarith [k3, k2]
    exact lt_of_mul_lt_mul_right k4 (by linarith)
  -- lower bound `(d+1)·((d+1)² − 2) ≤ zq·(q₂ − 2)` and the closing estimate
  have k6 : ((d : ℝ) + 1) * (((d : ℝ) + 1) ^ 2 - 2) ≤ (zq : ℝ) * ((q₂ : ℝ) - 2) := by
    apply mul_le_mul h4R (by linarith) (by nlinarith) hzq0.le
  nlinarith [k5, k6,
    mul_nonneg (by linarith : (0 : ℝ) ≤ (d : ℝ) - 1)
      (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2 + 1)]

/-! ## The centrality input of the (1.2) degree bound

`exists_deg_sq_le_of_mem_SsetOf` consumes the centrality of `D₀/R` in `Q/R`
(as a `map (mk' …) ≤ center …` statement).  In reduction (1) this is supplied
at `R = S'Q₃`, `D₀ = SZ` where `Z/Q₃ = Z(Q₁/Q₃)`: the commutator
`⁅SZ, Q⁆ = ⁅S,S⁆·⁅Z,Q₁⁆ ⊆ S'Q₃` splits along the direct product `Q = S × Q₁`. -/

/-- **The direct-product commutator split**: `⁅x, q⁆ ∈ S' ⊔ Q₃` for
`x ∈ S ⊔ Z`, `q ∈ Q`, provided `⁅Z, Q₁⁆ ⊆ Q₃`.  Writing `x = s·z`, `q = s₁·y₁`
along `Q = S × Q₁` and commuting the factors,
`⁅s·z, s₁·y₁⁆ = ⁅s, s₁⁆·⁅z, y₁⁆ ∈ ⁅S,S⁆·Q₃`. -/
theorem commutator_mem_sup_Sder_of_central {Q₃ Z : Subgroup G}
    (hZQ1 : Z ≤ hyp.Q1)
    (hcentral : ∀ z ∈ Z, ∀ y ∈ hyp.Q1, ⁅z, y⁆ ∈ Q₃)
    {x q : G} (hx : x ∈ hyp.S ⊔ Z) (hq : q ∈ hyp.Q) :
    ⁅x, q⁆ ∈ hyp.Sder ⊔ Q₃ := by
  -- decompose `x = s·z` along `S ⊔ Z = S·Z`
  have hnorm : hyp.S ≤ Subgroup.normalizer (Z : Set G) :=
    hyp.le_normalizer_of_le_S_of_le_Q1 le_rfl hZQ1
  have hxmul : x ∈ (hyp.S : Set G) * (Z : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right hyp.S Z hnorm]
    exact hx
  obtain ⟨s, hs, z, hz, hxeq⟩ := hxmul
  -- decompose `q = s₁·y₁` along `Q = S·Q₁`
  rw [← SetLike.mem_coe, ← hyp.S_mul_Q1_eq_Q] at hq
  obtain ⟨s₁, hs₁, y₁, hy₁, hqeq⟩ := hq
  -- the commutator splits into the `S`- and `Q₁`-commutators
  have hc1 : Commute z s₁ := (hyp.S_commutes_Q1 s₁ hs₁ z (hZQ1 hz)).symm
  have hc2 : Commute s⁻¹ y₁⁻¹ :=
    hyp.S_commutes_Q1 s⁻¹ (hyp.S.inv_mem hs) y₁⁻¹ (hyp.Q1.inv_mem hy₁)
  have hw : z * y₁ * (z⁻¹ * y₁⁻¹) ∈ hyp.Q1 :=
    hyp.Q1.mul_mem (hyp.Q1.mul_mem (hZQ1 hz) hy₁)
      (hyp.Q1.mul_mem (hyp.Q1.inv_mem (hZQ1 hz)) (hyp.Q1.inv_mem hy₁))
  have hc3 : (s⁻¹ * s₁⁻¹) * (z * y₁ * (z⁻¹ * y₁⁻¹))
      = (z * y₁ * (z⁻¹ * y₁⁻¹)) * (s⁻¹ * s₁⁻¹) :=
    hyp.S_commutes_Q1 _ (hyp.S.mul_mem (hyp.S.inv_mem hs) (hyp.S.inv_mem hs₁)) _ hw
  have hkey : ⁅x, q⁆ = ⁅s, s₁⁆ * ⁅z, y₁⁆ := by
    calc ⁅x, q⁆
        = (s * z) * (s₁ * y₁) * ((z⁻¹ * s⁻¹) * (y₁⁻¹ * s₁⁻¹)) := by
          rw [← hxeq, ← hqeq, commutatorElement_def]; group
      _ = (s * s₁) * (z * y₁) * ((z⁻¹ * y₁⁻¹) * (s⁻¹ * s₁⁻¹)) := by
          rw [hc1.mul_mul_mul_comm, hc2.mul_mul_mul_comm]
      _ = (s * s₁) * ((z * y₁ * (z⁻¹ * y₁⁻¹)) * (s⁻¹ * s₁⁻¹)) := by group
      _ = (s * s₁) * ((s⁻¹ * s₁⁻¹) * (z * y₁ * (z⁻¹ * y₁⁻¹))) := by rw [hc3]
      _ = ⁅s, s₁⁆ * ⁅z, y₁⁆ := by
          rw [commutatorElement_def, commutatorElement_def]; group
  rw [hkey]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hs hs₁))
    (Subgroup.mem_sup_right (hcentral z hz y₁ hy₁))

/-- **Element-level commutators give the `map ≤ center` input**: if
`⁅D₀, Q⁆ ⊆ R` elementwise, then the image of `D₀` in `Q/R` (in the doubly
relativised form consumed by `exists_deg_sq_le_of_mem_SsetOf`) is central. -/
theorem map_mk_le_center_of_commutator_mem {R D₀ : Subgroup G}
    [((R.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).Normal]
    (hcomm : ∀ x ∈ D₀, ∀ q ∈ hyp.Q, ⁅x, q⁆ ∈ R) :
    ((D₀.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).map
        (QuotientGroup.mk' ((R.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)))
      ≤ Subgroup.center ((↥(hyp.Q.subgroupOf hyp.H)) ⧸
          ((R.subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))) := by
  rintro xbar ⟨x, hxD₀, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro qbar
  refine QuotientGroup.induction_on qbar fun q => ?_
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    QuotientGroup.eq]
  have hmem : (q * x)⁻¹ * (x * q) = ⁅x⁻¹, q⁻¹⁆ := by
    rw [commutatorElement_def]; group
  rw [hmem, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have hcoe : ((((⁅x⁻¹, q⁻¹⁆ : ↥(hyp.Q.subgroupOf hyp.H)) : ↥hyp.H)) : G)
      = ⁅(((x : ↥hyp.H) : G))⁻¹, (((q : ↥hyp.H) : G))⁻¹⁆ := by
    simp [commutatorElement_def]
  rw [hcoe]
  have hxG : ((x : ↥hyp.H) : G) ∈ D₀ := by
    have h := hxD₀
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h
    exact h
  have hqG : ((q : ↥hyp.H) : G) ∈ hyp.Q := Subgroup.mem_subgroupOf.mp q.2
  exact hcomm _ (D₀.inv_mem hxG) _ (hyp.Q.inv_mem hqG)

/-- **The (1.2) centrality input at `R = S'⊔Q₃`, `D₀ = S⊔Z`** for a central
section `⁅Z, Q₁⁆ ⊆ Q₃` (the lift of `Z/Q₃ ≤ Z(Q₁/Q₃)`): the image of `SZ` in
`Q/S'Q₃` is central, in the exact shape `exists_deg_sq_le_of_mem_SsetOf`
consumes. -/
theorem map_mk_sup_S_le_center_of_central {Q₃ Z : Subgroup G}
    (hZQ1 : Z ≤ hyp.Q1)
    (hcentral : ∀ z ∈ Z, ∀ y ∈ hyp.Q1, ⁅z, y⁆ ∈ Q₃)
    [(((hyp.Sder ⊔ Q₃).subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).Normal] :
    (((hyp.S ⊔ Z).subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).map
        (QuotientGroup.mk' (((hyp.Sder ⊔ Q₃).subgroupOf hyp.H).subgroupOf
          (hyp.Q.subgroupOf hyp.H)))
      ≤ Subgroup.center ((↥(hyp.Q.subgroupOf hyp.H)) ⧸
          (((hyp.Sder ⊔ Q₃).subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H))) :=
  hyp.map_mk_le_center_of_commutator_mem fun _ hx _ hq =>
    hyp.commutator_mem_sup_Sder_of_central hZQ1 hcentral hx hq

/-! ## The reduction (1) one-step lemma (p. 146)

Peterfalvi's induction step "if `𝒮(S'Q₂)` is coherent and `𝒮(S'Q₃)` is not,
then …, a contradiction": the counterexample extraction plus the (1.1)/(1.2)
bounds and the fixed-point-free lower bounds are jointly impossible. -/

/-- `[Q₁, Q₁] ≤ Q₁` (mirror of `Sder_le_S`). -/
theorem Q1der_le_Q1 : ⁅hyp.Q1, hyp.Q1⁆ ≤ hyp.Q1 := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  exact hyp.Q1.mul_mem (hyp.Q1.mul_mem (hyp.Q1.mul_mem hg hh) (hyp.Q1.inv_mem hg))
    (hyp.Q1.inv_mem hh)

/-- **`𝒮(R)` is closed under complex conjugation** for any kernel condition `R`
(the general-`R` form of `conj_mem_SsetOf_Qder`): conjugation preserves
membership in `𝒮` (`conj_mem_Sset`), and the `LeKer` constancy transports
through `star`. -/
theorem conj_mem_SsetOf [Finite G] {R : Subgroup G} {χ : ClassFunction ↥hyp.H ℂ}
    (hχ : χ ∈ hyp.SsetOf R) : χ.conj ∈ hyp.SsetOf R := by
  obtain ⟨hχS, hker⟩ := hχ
  refine ⟨hyp.conj_mem_Sset hχS, fun x hx => ?_⟩
  rw [ClassFunction.conj_apply, ClassFunction.conj_apply, hker x hx]

section StepLemma

variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable [Fintype ↥hyp.H] [Invertible (Nat.card ↥hyp.H : ℂ)]
variable [Invertible (Nat.card ↥(hyp.Q.subgroupOf hyp.H) : ℂ)]

/-- **The reduction (1) one-step lemma** (p. 146): coherence of `𝒮(S'Q₂)`
propagates to `𝒮(S'Q₃)` given the chief-factor data `Q₃ ≤ Q₂ ≤ Z ≤ Q₁` — `Z`
the lift of `Z(Q₁/Q₃)` (`⁅Z, Q₁⁆ ⊆ Q₃`), `Q₂ ⊊ Z`, `Q₂` and `Z` `D`-invariant,
and the two-prime lower bound `|Q₁⧸Q₂| ≥ (d+1)²`.

Proof: suppose not.  The counterexample extraction
(`exists_counterexample_of_not_coherent` at `B = 𝒮(S'Q₂)`, `Y = 𝒮(S'Q₃)`, with
the degree-`d` anchor from `𝒮(Q') ⊆ 𝒮(S'Q₂)`) produces `ψ ∈ 𝒮(S'Q₃)` of degree
`d·a` with `∑_{𝒮(S'Q₂)} m(x)² ≤ 2a`.  The counting bound (1.1) turns this into
`|Q₁⧸Q₂| − 1 ≤ 2da` (`card_quot_sub_le_of_forall_deg_of_sum_le` →
`card_quot_Q1_sub_one_le_of_card_quot_sub_le`); the degree bound (1.2) gives
`a² ≤ |Q₁⧸Z|` (`exists_deg_sq_le_of_mem_SsetOf` at `D₀ = SZ` with the
direct-product centrality `map_mk_sup_S_le_center_of_central` and the index
conversion `index_subgroupOf_sup_S_eq`); with the tower
`|Q₁⧸Q₂| = |Q₁⧸Z|·|Z⧸Q₂|` and the fixed-point-free bounds `|Z⧸Q₂| ≥ d+1`,
`|Q₁⧸Q₂| ≥ (d+1)²`, the arithmetic `false_of_reduction_one_bounds` closes the
contradiction. -/
theorem ssetOf_coherent_step
    (hd : Odd hyp.d) (hQ1odd : Odd (Nat.card ↥hyp.Q1))
    (hlt : hyp.S ⊔ hyp.Qder < hyp.Q)
    {Q₂ Q₃ Z : Subgroup G}
    (hQ₂der : Q₂ ≤ ⁅hyp.Q1, hyp.Q1⁆) (hQ₃Q₂ : Q₃ ≤ Q₂)
    (hZQ1 : Z ≤ hyp.Q1) (hQ₂Z : Q₂ ≤ Z) (hZQ₂ : ¬ Z ≤ Q₂)
    (hcentralZ : ∀ z ∈ Z, ∀ y ∈ hyp.Q1, ⁅z, y⁆ ∈ Q₃)
    (hQ₂inv : ∀ δ ∈ hyp.D, ∀ z ∈ Q₂, δ * z * δ⁻¹ ∈ Q₂)
    (hZinv : ∀ δ ∈ hyp.D, ∀ z ∈ Z, δ * z * δ⁻¹ ∈ Z)
    (h2primes : (hyp.d + 1) ^ 2 ≤ Nat.card (↥hyp.Q1 ⧸ Q₂.subgroupOf hyp.Q1))
    [((hyp.Sder ⊔ Q₂).subgroupOf hyp.H).Normal]
    [((hyp.Sder ⊔ Q₃).subgroupOf hyp.H).Normal]
    [(((hyp.Sder ⊔ Q₂).subgroupOf hyp.H) ⊔ (hyp.Q1.subgroupOf hyp.H)).Normal]
    [(((hyp.Sder ⊔ Q₃).subgroupOf hyp.H).subgroupOf (hyp.Q.subgroupOf hyp.H)).Normal]
    [((hyp.S ⊔ Z).subgroupOf hyp.H).Normal]
    (hcoh₂ : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.SsetOf (hyp.Sder ⊔ Q₂)) hyp.A)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (hyp.SsetOf (hyp.Sder ⊔ Q₃)) hyp.A) := by
  classical
  by_contra hfail
  have hQ₂Q1 : Q₂ ≤ hyp.Q1 := hQ₂der.trans hyp.Q1der_le_Q1
  -- families: base `B = 𝒮(S'Q₂) ⊆ Y = 𝒮(S'Q₃) ⊆ 𝒮`
  have hBY : hyp.SsetOf (hyp.Sder ⊔ Q₂) ⊆ hyp.SsetOf (hyp.Sder ⊔ Q₃) :=
    hyp.ssetOf_antitone (sup_le_sup_left hQ₃Q₂ _)
  have hYS : hyp.SsetOf (hyp.Sder ⊔ Q₃) ⊆ hyp.Sset := fun _ hx => hx.1
  have hYfin : (hyp.SsetOf (hyp.Sder ⊔ Q₃)).Finite := hyp.Sset_finite.subset hYS
  -- the degree-`d` anchor of the Remark, via `𝒮(Q') ⊆ 𝒮(S'Q₂)`
  obtain ⟨χ₀, hχ₀Qder⟩ := hyp.ssetOf_Qder_nonempty hlt
  have hχ₀B : χ₀ ∈ hyp.SsetOf (hyp.Sder ⊔ Q₂) :=
    hyp.ssetOf_antitone (hyp.sup_Sder_le_Qder hQ₂der) hχ₀Qder
  -- counterexample extraction: `ψ` of degree `d·a` with `∑_B m² ≤ 2a`
  obtain ⟨ψ, a, m, hψY, hapos, hψdeg, hmdeg, hmsum⟩ :=
    hyp.exists_counterexample_of_not_coherent hd hQ1odd hBY hYS hYfin
      (fun _ hχ => hyp.conj_mem_SsetOf hχ) (fun _ hχ => hyp.conj_mem_SsetOf hχ)
      hcoh₂ hχ₀B (hyp.apply_one_eq_d_of_mem_SsetOf_Qder hχ₀Qder) hfail
  -- (1.1): `|Q₁⧸Q₂| − 1 ≤ d·2a`
  have h11 := hyp.card_quot_Q1_sub_one_le_of_card_quot_sub_le
    (sup_le (hyp.Sder_le_S.trans hyp.S_le_Q) (hQ₂Q1.trans hyp.Q1_le_Q))
    (hyp.Q1_inf_sup_eq hyp.Sder_le_S hQ₂Q1)
    (hyp.card_quot_sub_le_of_forall_deg_of_sum_le (hyp.Sder ⊔ Q₂)
      (hYfin.subset hBY) hmdeg hmsum)
  -- (1.2): `a² ≤ |Q₁⧸Z|`
  obtain ⟨a', ha'deg, ha'sq⟩ := hyp.exists_deg_sq_le_of_mem_SsetOf
    (hyp.Sder ⊔ Q₃) (hyp.S ⊔ Z)
    (sup_le (hyp.Sder_le_S.trans hyp.S_le_Q) ((hQ₃Q₂.trans hQ₂Q1).trans hyp.Q1_le_Q))
    (sup_le_sup hyp.Sder_le_S (hQ₃Q₂.trans hQ₂Z))
    (sup_le hyp.S_le_Q (hZQ1.trans hyp.Q1_le_Q))
    (hyp.map_mk_sup_S_le_center_of_central hZQ1 hcentralZ) hψY
  have haa' : a' = a := by
    have hdne : (hyp.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.d_pos.ne'
    have heq : (hyp.d : ℂ) * (a' : ℂ) = (hyp.d : ℂ) * (a : ℂ) :=
      ha'deg.symm.trans hψdeg
    exact_mod_cast mul_left_cancel₀ hdne heq
  rw [haa', hyp.index_subgroupOf_sup_S_eq hZQ1] at ha'sq
  -- assemble the arithmetic contradiction
  exact false_of_reduction_one_bounds hyp.d_pos h11 ha'sq
    (hyp.card_quot_Q1_eq_mul hQ₂Z hZQ1)
    (hyp.d_add_one_le_card_quotient_of_le_Q1 hQ₂Z hZQ1 hQ₂inv hZinv hZQ₂) h2primes

end StepLemma

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
