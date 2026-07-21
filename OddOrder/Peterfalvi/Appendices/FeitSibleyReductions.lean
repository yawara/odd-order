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

open scoped Pointwise commutatorElement

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

end Hypothesis

end OddOrder.Peterfalvi.Appendices.FeitSibley
