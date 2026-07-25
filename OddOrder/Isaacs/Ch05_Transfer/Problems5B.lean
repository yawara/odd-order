/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs
import OddOrder.Isaacs.Ch05_Transfer.Dietzmann

/-!
# Isaacs Chapter 5 — Problems 5B (transfer evaluation / Dietzmann)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 5B (書籍 p. 157)。

* **5B.1** `P ∈ Syl_p(G)`, `g ∈ P` は位数 `p`, `g ∈ G'` かつ `g ∉ P'` ⇒
  `g^t ∈ P` なる `t ∉ P` が存在する。
  ⚠ **書籍の印刷は `g^t ∈ P'` だが、巻末 errata (項目 3, p. 157) が
  「`P` の dash を削れ」= `g^t ∈ P` に訂正している**。PDF ページ画像 (書籍 p.157 =
  PDF p.170) と errata の両方で確認済。
* **5B.2** Thm 5.10 (Dietzmann) の状況で `|X| = m` なら `|⟨X⟩| ≤ n^m`。
* **5B.3** `x ∈ G` がある有限正規部分群に属する ⟺ `x` の位数が有限かつ共役類が有限。

Dietzmann の定理 (Thm 5.10) は `Dietzmann.lean` に landing 済
(`dietzmann` / `dietzmann_setFinite`)。
-/

namespace OddOrder.Isaacs.Ch05

section /- 5B: Problems (p. 157) -/

variable {G : Type*} [Group G]

/-! ### Problem 5B.3 -/

/-- 共役で閉じた集合が生成する部分群は正規。

`Subgroup.closure_induction` で各生成手順が共役に耐えることを見るだけ。 -/
theorem normal_closure_of_conj_closed {X : Set G}
    (hconj : ∀ x ∈ X, ∀ g : G, g * x * g⁻¹ ∈ X) : (Subgroup.closure X).Normal := by
  refine ⟨fun y hy g => ?_⟩
  induction hy using Subgroup.closure_induction with
  | mem z hz => exact Subgroup.subset_closure (hconj z hz g)
  | one => simp
  | mul a b _ _ ha hb =>
    have hab : g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
    rw [hab]
    exact mul_mem ha hb
  | inv a _ ha =>
    have hinv : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [hinv]
    exact inv_mem ha

/-- **Isaacs Problem 5B.3**: `x` がある有限正規部分群に属する ⟺ `x` の位数が有限で,
かつ `x` の共役類が有限。`G` は有限とは限らない。

**証明**: (⟸) `X := x` の共役類は有限・共役閉で, 各元の位数は `orderOf x` を割るので
Dietzmann (Thm 5.10) より `⟨X⟩` は有限。共役閉なので `⟨X⟩ ⊴ G` (`normal_closure_of_conj_closed`),
かつ `x ∈ X ⊆ ⟨X⟩`。
(⟹) `x ∈ N` で `N` 有限なら `x ^ |N| = 1` で位数有限, 共役類は `N` 正規性から `N` に含まれ有限。 -/
theorem exists_finite_normal_iff (x : G) :
    (∃ N : Subgroup G, N.Normal ∧ Finite ↥N ∧ x ∈ N) ↔
      IsOfFinOrder x ∧ (conjugatesOf x).Finite := by
  constructor
  · rintro ⟨N, hNnormal, hNfin, hxN⟩
    haveI := hNfin
    refine ⟨?_, ?_⟩
    · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨Nat.card N, Nat.card_pos,
        congrArg Subtype.val (pow_card_eq_one' (G := ↥N) (x := ⟨x, hxN⟩))⟩
    · have hNset : (N : Set G).Finite := Set.toFinite _
      refine hNset.subset ?_
      intro y hy
      obtain ⟨c, hc⟩ := isConj_iff.mp hy
      rw [← hc]
      exact hNnormal.conj_mem x hxN c
  · rintro ⟨hord, hfin⟩
    obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.mp hord
    have hconj : ∀ y ∈ conjugatesOf x, ∀ g : G, g * y * g⁻¹ ∈ conjugatesOf x := by
      intro y hy g
      obtain ⟨c, hc⟩ := isConj_iff.mp hy
      exact isConj_iff.mpr ⟨g * c, by rw [← hc]; group⟩
    have hexp : ∀ y ∈ conjugatesOf x, y ^ n = 1 := by
      intro y hy
      obtain ⟨c, hc⟩ := isConj_iff.mp hy
      have hcp : ∀ m : ℕ, (c * x * c⁻¹) ^ m = c * x ^ m * c⁻¹ := by
        intro m
        induction m with
        | zero => simp
        | succ k ih => rw [pow_succ, ih, pow_succ]; group
      rw [← hc, hcp, hxn]
      group
    exact ⟨Subgroup.closure (conjugatesOf x), normal_closure_of_conj_closed hconj,
      dietzmann hfin hconj hn hexp, Subgroup.subset_closure (IsConj.refl x)⟩

/-! ### Problem 5B.1 -/

/-- **Isaacs Problem 5B.1** (書籍 p. 157; 巻末 errata で訂正済): `P ∈ Syl_p(G)` で `g ∈ P` の
位数が `p`, `g ∈ G'` かつ `g ∉ ⁅P, P⁆` なら, `t ∉ P` かつ `t⁻¹ g t ∈ P` なる `t ∈ G` がある。

⚠ 書籍の印刷は結論が `g^t ∈ P'` だが, **巻末 errata 項目 3 (p. 157) が `g^t ∈ P` に訂正**
している (PDF ページ画像と errata の両方で確認済)。

**証明** (書籍 hint): `v : G →* P/P'` を transfer とすると `G' ≤ ker v` ゆえ `v(g) = 1`。
transfer-evaluation (mathlib `transfer_eq_prod_quotient_orbitRel_zpowers_quot`) より
`v(g) = ∏_q ϕ⟨w_q⁻¹ g^{n_q} w_q⟩`。`o(g) = p` なので `n_q ∈ {1, p}` で,
`n_q = p` の項は `g^p = 1` ゆえ自明。仮に「`w⁻¹ g w ∈ P ⟹ w ∈ P`」が常に成り立つとすると
`n_q = 1` の項はすべて `P/P'` の中で `gP'` に等しく `v(g) = (gP')^N`。
`∑ n_q = |G : P|` と `p ∤ |G : P|` から `N ≢ 0 (mod p)` だが, `g ∉ ⁅P,P⁆` より `gP'` の位数は
`p` なので `(gP')^N ≠ 1`, `v(g) = 1` に矛盾。 -/
theorem exists_notMem_conj_mem_of_mem_commutator [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {g : G} (hgP : g ∈ (P : Subgroup G)) (hgord : orderOf g = p)
    (hgG : g ∈ commutator G) (hgP' : g ∉ ⁅(P : Subgroup G), (P : Subgroup G)⁆) :
    ∃ t : G, t ∉ (P : Subgroup G) ∧ t⁻¹ * g * t ∈ (P : Subgroup G) := by
  classical
  by_contra hcon
  have hfix : ∀ t : G, t⁻¹ * g * t ∈ (P : Subgroup G) → t ∈ (P : Subgroup G) := by
    intro t ht
    by_contra htP
    exact hcon ⟨t, htP, ht⟩
  set Q : Subgroup G := (P : Subgroup G) with hQ
  set ϕ : ↥Q →* Abelianization ↥Q := Abelianization.of with hϕ
  haveI : Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ Q)) :=
    Fintype.ofFinite _
  -- `g ∈ G' ≤ ker (transfer ϕ)`
  have hker : MonoidHom.transfer ϕ g = 1 := by
    have hle : commutator G ≤ (MonoidHom.transfer ϕ).ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    exact MonoidHom.mem_ker.mp (hle hgG)
  -- 各軌道の周期は `1` か `p`
  have hper : ∀ q : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ Q),
      Function.IsPeriodicPt (fun x : G ⧸ Q => g • x) p q.out := by
    intro q
    have hit : (fun x : G ⧸ Q => g • x)^[p] q.out = (g ^ p) • q.out := by
      rw [smul_iterate]
    have : (g : G) ^ p = 1 := by rw [← hgord, pow_orderOf_eq_one]
    simp only [Function.IsPeriodicPt, Function.IsFixedPt, hit, this, one_smul]
  have hnp : ∀ q : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ Q),
      Function.minimalPeriod (fun x : G ⧸ Q => g • x) q.out = 1 ∨
        Function.minimalPeriod (fun x : G ⧸ Q => g • x) q.out = p :=
    fun q => (Nat.Prime.eq_one_or_self_of_dvd Fact.out _ (hper q).minimalPeriod_dvd)
  -- `∑ n_q = |G : P|`
  have hsum : ∑ q : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ Q),
      Function.minimalPeriod (fun x : G ⧸ Q => g • x) q.out = Q.index := by
    have hcard := Nat.card_congr (Subgroup.quotientEquivSigmaZMod Q g)
    rw [Nat.card_sigma] at hcard
    simp only [Nat.card_zmod] at hcard
    exact hcard.symm
  -- transfer-evaluation の各因子
  set f : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ Q) → Abelianization ↥Q :=
    fun q => ϕ ⟨q.out.out⁻¹ *
      g ^ Function.minimalPeriod (fun x : G ⧸ Q => g • x) q.out * q.out.out,
      QuotientGroup.out_conj_pow_minimalPeriod_mem Q g q.out⟩ with hf
  have hker' : ∏ q, f q = 1 :=
    (MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot ϕ g).symm.trans hker
  set S := Finset.univ.filter
    (fun q : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ Q) =>
      Function.minimalPeriod (fun x : G ⧸ Q => g • x) q.out = 1) with hS
  have hgpow : g ^ p = 1 := by rw [← hgord, pow_orderOf_eq_one]
  -- `n_q = p` の因子は自明
  have hone : ∀ q ∈ Finset.univ, q ∉ S → f q = 1 := by
    intro q _ hq
    have hnq : Function.minimalPeriod (fun x : G ⧸ Q => g • x) q.out = p := by
      rcases hnp q with h | h
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ q, h⟩) hq
      · exact h
    have hval : (⟨q.out.out⁻¹ *
        g ^ Function.minimalPeriod (fun x : G ⧸ Q => g • x) q.out * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem Q g q.out⟩ : ↥Q) = 1 := by
      refine Subtype.ext ?_
      change q.out.out⁻¹ * g ^ Function.minimalPeriod (fun x : G ⧸ Q => g • x) q.out *
        q.out.out = 1
      rw [hnq, hgpow]
      group
    rw [hf]
    simp only [hval, map_one]
  -- `n_q = 1` の因子はすべて `ϕ ⟨g⟩`
  have hgS : ∀ q ∈ S, f q = ϕ ⟨g, hgP⟩ := by
    intro q hq
    have hnq : Function.minimalPeriod (fun x : G ⧸ Q => g • x) q.out = 1 :=
      (Finset.mem_filter.mp hq).2
    have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem Q g q.out
    rw [hnq, pow_one] at hmem
    have hw : q.out.out ∈ Q := hfix _ hmem
    have hval : (⟨q.out.out⁻¹ *
        g ^ Function.minimalPeriod (fun x : G ⧸ Q => g • x) q.out * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem Q g q.out⟩ : ↥Q)
        = (⟨q.out.out, hw⟩ : ↥Q)⁻¹ * ⟨g, hgP⟩ * ⟨q.out.out, hw⟩ := by
      refine Subtype.ext ?_
      change q.out.out⁻¹ * g ^ Function.minimalPeriod (fun x : G ⧸ Q => g • x) q.out *
        q.out.out = _
      rw [hnq, pow_one]
      rfl
    rw [hf]
    simp only [hval, map_mul, map_inv]
    rw [mul_comm (ϕ ⟨q.out.out, hw⟩)⁻¹ (ϕ ⟨g, hgP⟩), mul_assoc, inv_mul_cancel, mul_one]
  -- 積を `S` 上に落とす
  have hprod : (ϕ ⟨g, hgP⟩) ^ S.card = 1 := by
    rw [← Finset.prod_const, ← Finset.prod_congr rfl hgS,
      Finset.prod_subset (Finset.subset_univ S) hone]
    exact hker'
  -- `ϕ ⟨g⟩` の位数は `p`
  have hne : ϕ ⟨g, hgP⟩ ≠ 1 := by
    intro h
    refine hgP' ?_
    have hmem : (⟨g, hgP⟩ : ↥Q) ∈ _root_.commutator ↥Q := (QuotientGroup.eq_one_iff _).mp h
    have := Subgroup.map_subtype_commutator Q
    rw [← this]
    exact ⟨⟨g, hgP⟩, hmem, rfl⟩
  have hordϕ : orderOf (ϕ ⟨g, hgP⟩) = p := by
    refine orderOf_eq_prime ?_ hne
    rw [← map_pow]
    have : (⟨g, hgP⟩ : ↥Q) ^ p = 1 := Subtype.ext (by simpa using hgpow)
    rw [this, map_one]
  -- `p ∣ |S|`
  have hpS : p ∣ S.card := by
    have := orderOf_dvd_of_pow_eq_one hprod
    rwa [hordϕ] at this
  -- しかし `|S| + p · |Sᶜ| = |G : P|` で `p ∤ |G : P|`
  refine P.not_dvd_index ?_
  rw [← hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun q : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ Q) =>
      Function.minimalPeriod (fun x : G ⧸ Q => g • x) q.out = 1)]
  refine Nat.dvd_add ?_ ?_
  · rw [Finset.sum_congr rfl (fun q hq => (Finset.mem_filter.mp hq).2), Finset.sum_const,
      smul_eq_mul, mul_one]
    exact hpS
  · refine Finset.dvd_sum fun q hq => ?_
    have hnot : ¬ Function.minimalPeriod (fun x : G ⧸ Q => g • x) q.out = 1 :=
      (Finset.mem_filter.mp hq).2
    rcases hnp q with h | h
    · exact absurd h hnot
    · exact h ▸ dvd_rfl

end

end OddOrder.Isaacs.Ch05
