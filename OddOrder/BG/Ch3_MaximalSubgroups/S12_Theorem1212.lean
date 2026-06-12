/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1211
import OddOrder.BG.Ch1_Preliminary.S01b_Prop116

/-!
# BG §12: Theorem 12.12 — regular 場合の Frobenius 因子分解

**スコープ**: BG Theorem 12.12 (mmd L3336)。`SubgroupESetup M E E₁ E₂ E₃` の下で、
すべての `(τ₁(M)∪τ₃(M))`-元 `e ∈ E#` が `C_{M_σ}(e)=1` を満たす (regular) とき、
(a) `E` は abelian normal `A₀` を含み `∀ x ∈ M_σ#, C_E(x) ⊆ A₀`;
(b) `E` は `E` と同 exponent の補群 `E₀` を含み `M_σ E₀` は kernel `M_σ` の Frobenius 群。

本ファイルでは新規補題 **Proposition 3.9** (coprime FPF p-作用 ⟹ cyclic) を形式化し、
3 大ケース (τ₂(M)=∅ / nonabelian Sylow p / abelian Sylow) のための部品を順次構築する。
最終的に `frobenius_factorization_of_regular` (S12_E の scaffold) をここで充足・移植する。
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.Isaacs.Ch06
open scoped Pointwise
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The two-part conclusion of **Theorem 12.12** for a maximal `M` with `σ`-complement `E`:
(a) `E` has an abelian normal subgroup `A₀` swallowing every `C_E(x)` (`x ∈ M_σ#`), and
(b) `E` has a same-exponent subgroup `E₀` with `M_σ E₀` Frobenius of kernel `M_σ`. -/
def FrobFactConclusion (M E : Subgroup G) : Prop :=
  (∃ A₀ : Subgroup G, A₀ ≤ E ∧ IsMulCommutative ↥A₀ ∧
    E ≤ Subgroup.normalizer ((A₀ : Subgroup G) : Set G) ∧
    ∀ x ∈ S10.Msigma M, x ≠ 1 → E ⊓ Subgroup.centralizer ({x} : Set G) ≤ A₀) ∧
  (∃ E₀ : Subgroup G, E₀ ≤ E ∧ Monoid.exponent ↥E₀ = Monoid.exponent ↥E ∧
    Ch06.IsFrobeniusGroup ↥(S10.Msigma M ⊔ E₀)
      ((S10.Msigma M).subgroupOf (S10.Msigma M ⊔ E₀))
      (E₀.subgroupOf (S10.Msigma M ⊔ E₀)))

/-! ## Proposition 3.9: coprime fixed-point-free `p`-action ⟹ cyclic -/

/-- **Proposition 3.9** (Gorenstein 5.3.14): a finite `p`-group `R` (`p` odd) acting
coprimely and fixed-point-freely on a nontrivial finite group `H` is cyclic.

If `R` were not cyclic it would contain an elementary abelian subgroup `B` of order `p²`
(`exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic`); `B` is abelian and not cyclic,
so Isaacs 6.21 (`nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'`) gives
`⟨ C_H(b) | b ∈ B^# ⟩ = H`. But the action is fixed-point-free, so each `C_H(b) = 1`,
forcing `H = 1`, a contradiction. The `12.12` application is the conjugation action of
`Q/Q₀` on a Sylow subgroup `S`, where `Q₀ = C_Q(S)` is the kernel. -/
theorem isCyclic_of_coprime_fpf_pgroup_action
    {R H : Type*} [Group R] [Group H] [Finite R] [Finite H] {p : ℕ} [Fact p.Prime]
    [Nontrivial H] (hR : IsPGroup p R) (hp_odd : Odd p)
    (hcop : Nat.Coprime (Nat.card R) (Nat.card H)) (φ : R →* MulAut H)
    (hfpf : ∀ a : R, a ≠ 1 → actionFixedBy φ a = ⊥) :
    IsCyclic R := by
  by_contra hnc
  obtain ⟨B, hB_elem, hB_card⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic hR hp_odd hnc
  haveI : IsMulCommutative ↥B := ⟨⟨hB_elem.comm⟩⟩
  have hBnc : ¬ IsCyclic ↥B :=
    OddOrder.GroupTheory.IsElementaryAbelian.not_isCyclic_of_card_prime_sq Fact.out hB_elem hB_card
  have hcop' : Nat.Coprime (Nat.card ↥B) (Nat.card H) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card B) hcop
  have htop : nontrivialActionFixedByClosure (φ.comp B.subtype) = ⊤ :=
    OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'
      (φ.comp B.subtype) hcop' hBnc
  have hbot : nontrivialActionFixedByClosure (φ.comp B.subtype) ≤ ⊥ := by
    rw [nontrivialActionFixedByClosure_le_iff]
    intro b hb
    have hb' : B.subtype b ≠ 1 :=
      fun h => hb (B.subtype_injective (h.trans (map_one B.subtype).symm))
    exact (hfpf (B.subtype b) hb').le
  rw [htop, top_le_iff] at hbot
  obtain ⟨x, hx⟩ := exists_ne (1 : H)
  exact hx (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top x))

/-! ## Exponent bookkeeping for the complement `E₀` -/

/-- If `E₀ ≤ E` (finite) and, for every prime `r`, some element of `E₀` attains the `r`-part of
`exp(E)` (i.e. `v_r(exp E) ≤ v_r(ord g₀)` for some `g₀ ∈ E₀`), then `exp(E₀) = exp(E)`.

`exp(E₀) ∣ exp(E)` holds for any subgroup; the converse is checked prime-by-prime via
`Nat.factorization`, using that the `r`-part of `exp(E)` is realized by an element
(`Nat.Prime.exists_orderOf_eq_pow_factorization_exponent`) which the hypothesis lifts to `E₀`. -/
theorem exponent_eq_of_forall_factorization_le [Finite G] {E E₀ : Subgroup G}
    (hle : E₀ ≤ E)
    (hattain : ∀ r : ℕ, r.Prime →
      ∃ g₀ : ↥E₀, (Monoid.exponent ↥E).factorization r ≤ (orderOf g₀).factorization r) :
    Monoid.exponent ↥E₀ = Monoid.exponent ↥E := by
  have hExpE_ne : Monoid.exponent ↥E ≠ 0 := fun hz =>
    (Nat.card_pos (α := ↥E)).ne' (Nat.eq_zero_of_zero_dvd (hz ▸ Group.exponent_dvd_nat_card))
  have hExpE₀_ne : Monoid.exponent ↥E₀ ≠ 0 := fun hz =>
    (Nat.card_pos (α := ↥E₀)).ne' (Nat.eq_zero_of_zero_dvd (hz ▸ Group.exponent_dvd_nat_card))
  refine dvd_antisymm
    (Monoid.exponent_dvd_of_monoidHom (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))
    ?_
  rw [← Nat.factorization_le_iff_dvd hExpE_ne hExpE₀_ne, Finsupp.le_def]
  intro r
  by_cases hr : r.Prime
  · obtain ⟨g₀, hg₀⟩ := hattain r hr
    refine hg₀.trans ?_
    exact (Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd (orderOf_pos g₀).ne'
      hExpE₀_ne).mpr (Monoid.order_dvd_exponent g₀))) r
  · rw [Nat.factorization_eq_zero_of_not_prime _ hr]
    exact Nat.zero_le _

/-! ## Frobenius packaging: a regular complement `E₀` gives a Frobenius group `M_σ E₀` -/

/-- **Frobenius packaging** for Theorem 12.12(b): if `E₀ ≤ E` is a nontrivial subgroup acting
regularly on `M_σ` (`M_σ ⊓ C_G(a) = 1` for every `a ∈ E₀#`), then `M_σ E₀` is a Frobenius group
with Frobenius kernel `M_σ` and complement `E₀`. `M_σ ⊴ M ⊇ M_σ E₀` gives normality and the
complement relation (`M_σ ⊓ E₀ = 1` from the `SubgroupESetup`), `M_σ ≠ 1` by Theorem 10.2(e),
and the regularity is precisely the Frobenius condition `a n a⁻¹ ≠ n`. -/
theorem isFrobeniusGroup_of_regular [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {E₀ : Subgroup G} (hE₀E : E₀ ≤ E) (hE₀ne : E₀ ≠ ⊥)
    (hreg₀ : ∀ a ∈ E₀, a ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({a} : Set G) = ⊥) :
    Ch06.IsFrobeniusGroup ↥(S10.Msigma M ⊔ E₀)
      ((S10.Msigma M).subgroupOf (S10.Msigma M ⊔ E₀))
      (E₀.subgroupOf (S10.Msigma M ⊔ E₀)) := by
  have hMσne : S10.Msigma M ≠ ⊥ := S10.Msigma_ne_bot hG h.mem_maximal
  -- `M_σ E₀ ≤ M ≤ N_G(M_σ)`, so `M_σ` is normal in the ambient `M_σ E₀`.
  haveI hMσM_normal : ((S10.Msigma M).subgroupOf M).Normal := by
    rw [S10.Msigma_subgroupOf]; infer_instance
  have hM_le_N : M ≤ Subgroup.normalizer (S10.Msigma M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (S10.Msigma_le M)).mp hMσM_normal
  have hsup_le_M : S10.Msigma M ⊔ E₀ ≤ M := sup_le (S10.Msigma_le M) (hE₀E.trans h.E_le)
  have hsup_le_N : S10.Msigma M ⊔ E₀ ≤ Subgroup.normalizer (S10.Msigma M : Set G) :=
    hsup_le_M.trans hM_le_N
  have hinfbot : S10.Msigma M ⊓ E₀ = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left (S10.Msigma M) hE₀E).trans h.E_compl_inf.le)
  refine
    { isNormal := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hsup_le_N
      isComplement := ?_
      ne_bot_kernel := ?_
      ne_bot_complement := ?_
      conj_frobenius := ?_ }
  · -- `M_σ` and `E₀` are complements inside `↥(M_σ E₀)`.
    haveI : ((S10.Msigma M).subgroupOf (S10.Msigma M ⊔ E₀)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hsup_le_N
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff]
      have hinf : (S10.Msigma M).subgroupOf (S10.Msigma M ⊔ E₀) ⊓
          E₀.subgroupOf (S10.Msigma M ⊔ E₀)
          = (S10.Msigma M ⊓ E₀).subgroupOf (S10.Msigma M ⊔ E₀) := rfl
      rw [hinf, hinfbot, Subgroup.bot_subgroupOf]
    · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
        Subgroup.subgroupOf_self, Subgroup.coe_top]
  · rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hMσne (hd.eq_bot_of_le le_sup_left)
  · rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hE₀ne (hd.eq_bot_of_le le_sup_right)
  · -- the regularity `M_σ ⊓ C_G(a) = 1` is the Frobenius condition.
    intro a ha hane n hn hne hfix
    have ha_mem : (a : G) ∈ E₀ := Subgroup.mem_subgroupOf.mp ha
    have hn_mem : (n : G) ∈ S10.Msigma M := Subgroup.mem_subgroupOf.mp hn
    have ha_ne : (a : G) ≠ 1 := fun hc => hane (by exact_mod_cast hc)
    have hfixG : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      have := Subtype.ext_iff.mp hfix
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    have hncent : (n : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff] at hm; subst hm
      exact mul_inv_eq_iff_eq_mul.mp hfixG
    have hmem : (n : G) ∈ S10.Msigma M ⊓ Subgroup.centralizer ({(a : G)} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hn_mem, hncent⟩
    rw [hreg₀ (a : G) ha_mem ha_ne, Subgroup.mem_bot] at hmem
    exact hne (by exact_mod_cast hmem)

/-! ## Case `τ₂(M) = ∅`: the whole complement `E` is regular -/

/-- **Theorem 12.12, case `E = E₁E₃`** (i.e. every element of `E#` is a `(τ₁∪τ₃)`-element, so the
regularity hypothesis applies to all of `E`): take `A₀ = 1` and `E₀ = E`. Part (a) is immediate
(`C_E(x) = 1` for `x ∈ M_σ#`: any `1 ≠ e ∈ E ⊓ C_G(x)` would put `x ∈ M_σ ⊓ C_G(e) = 1`), and
part (b) is the Frobenius packaging with `E₀ = E`. -/
theorem frobFact_of_regular_all [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (hEne : E ≠ ⊥)
    (hregAll : ∀ e ∈ E, e ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    FrobFactConclusion M E := by
  refine ⟨⟨⊥, bot_le, ?_, ?_, ?_⟩,
    ⟨E, le_rfl, rfl, isFrobeniusGroup_of_regular hG h le_rfl hEne hregAll⟩⟩
  · exact IsMulCommutative.of_comm (fun a b => Subsingleton.elim _ _)
  · -- `E ≤ N_G(1) = G`.
    intro a _
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl; group
    · intro hz
      have : z = a⁻¹ * 1 * a := by rw [← (hz : a * z * a⁻¹ = 1)]; group
      simpa using this
  · -- `C_E(x) = 1`: a nontrivial `e ∈ E ⊓ C_G(x)` forces `x ∈ M_σ ⊓ C_G(e) = 1`.
    intro x hx hxne e he
    rw [Subgroup.mem_bot]
    by_contra hene
    have heE := (Subgroup.mem_inf.mp he).1
    have heC := (Subgroup.mem_inf.mp he).2
    have hxCe : x ∈ Subgroup.centralizer ({e} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff] at hm; subst hm
      exact (Subgroup.mem_centralizer_iff.mp heC x (Set.mem_singleton x)).symm
    have hmem : x ∈ S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hx, hxCe⟩
    rw [hregAll e heE hene, Subgroup.mem_bot] at hmem
    exact hxne hmem

end OddOrder.BG.Ch3.S12
