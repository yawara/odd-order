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
    have := hNfin
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
  have : Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ Q)) :=
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

/-! ### Problem 5B.2: 添字列のソート (隣接交換 + 辞書式降下)

書籍 hint の collection process を**隣接交換によるソート**として実装する。
`x_i x_j = x_j · (x_j⁻¹ x_i x_j)` で逆転 (`j < i`) を解消すると, 添字列の
`m` 進数値 `measure` が狭義減少するので停止する。 -/

namespace Sort5B2

variable {m : ℕ}

/-- 添字列の `m` 進数値 (先頭が最上位桁)。隣接交換の停止性の測度。 -/
def measure (m : ℕ) : List (Fin m) → ℕ
  | [] => 0
  | a :: t => (a : ℕ) * m ^ t.length + measure m t

theorem measure_lt (m : ℕ) : ∀ ι : List (Fin m), measure m ι < m ^ ι.length
  | [] => by simp [measure]
  | a :: t => by
    have ht := measure_lt m t
    have ha : (a : ℕ) + 1 ≤ m := a.isLt
    have hcalc : ((a : ℕ) + 1) * m ^ t.length ≤ m * m ^ t.length :=
      Nat.mul_le_mul_right _ ha
    simp only [measure, List.length_cons, pow_succ']
    nlinarith [ht, hcalc]

theorem measure_cons_lt {a b : Fin m} {t t' : List (Fin m)}
    (hab : (b : ℕ) < (a : ℕ)) (hlen : t'.length = t.length) :
    measure m (b :: t') < measure m (a :: t) := by
  have h1 : measure m t' < m ^ t'.length := measure_lt m t'
  rw [hlen] at h1
  have h2 : ((b : ℕ) + 1) * m ^ t.length ≤ (a : ℕ) * m ^ t.length :=
    Nat.mul_le_mul_right _ hab
  simp only [measure, hlen]
  nlinarith [h1, h2, Nat.zero_le (measure m t)]

theorem measure_append_lt (pre : List (Fin m)) {r r' : List (Fin m)}
    (hlen : r'.length = r.length) (h : measure m r' < measure m r) :
    measure m (pre ++ r') < measure m (pre ++ r) := by
  induction pre with
  | nil => simpa using h
  | cons a t ih =>
    have hle : (t ++ r').length = (t ++ r).length := by
      simp [hlen]
    simp only [List.cons_append, measure, hle]
    omega

/-- ソートされていない添字列には隣接する逆転がある。 -/
theorem exists_inversion {ι : List (Fin m)} (h : ¬ ι.IsChain (· ≤ ·)) :
    ∃ (pre post : List (Fin m)) (i j : Fin m),
      ι = pre ++ i :: j :: post ∧ (j : ℕ) < (i : ℕ) := by
  induction ι with
  | nil => exact absurd List.isChain_nil h
  | cons a t ih =>
    cases t with
    | nil => exact absurd (List.isChain_singleton a) h
    | cons b t' =>
      by_cases hab : a ≤ b
      · have ht : ¬ (b :: t').IsChain (· ≤ ·) := fun hc =>
          h (List.isChain_cons.mpr ⟨by simpa using hab, hc⟩)
        obtain ⟨pre, post, i, j, heq, hij⟩ := ih ht
        exact ⟨a :: pre, post, i, j, by rw [heq]; rfl, hij⟩
      · exact ⟨[], t', a, b, rfl, Fin.lt_def.mp (not_le.mp hab)⟩

/-- ⭐ **Problem 5B.2 の核**: 共役閉な枚挙 `xs : Fin m → G` に対し, 任意の添字列は
同じ積を与える**単調増加な**添字列に書き換えられる。

`measure` についての強帰納。逆転 `x_i x_j` (`j < i`) を `x_j x_k`
(`xs k = (xs j)⁻¹ * xs i * xs j`) に書き換えると `measure` が狭義減少する。 -/
theorem exists_chain'_map_prod_eq {G : Type*} [Group G] (xs : Fin m → G)
    (hconj : ∀ i j : Fin m, ∃ k : Fin m, (xs j)⁻¹ * xs i * xs j = xs k) :
    ∀ ι : List (Fin m), ∃ κ : List (Fin m), κ.IsChain (· ≤ ·) ∧
      (κ.map xs).prod = (ι.map xs).prod ∧ κ.length = ι.length := by
  intro ι
  induction hM : measure m ι using Nat.strong_induction_on generalizing ι with
  | _ M ih =>
    by_cases hs : ι.IsChain (· ≤ ·)
    · exact ⟨ι, hs, rfl, rfl⟩
    · obtain ⟨pre, post, i, j, rfl, hij⟩ := exists_inversion hs
      obtain ⟨k, hk⟩ := hconj i j
      have hprod : ((pre ++ j :: k :: post).map xs).prod =
          ((pre ++ i :: j :: post).map xs).prod := by
        simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
        congr 1
        rw [← hk]
        group
      have hlen : (pre ++ j :: k :: post).length = (pre ++ i :: j :: post).length := by
        simp
      have hdec : measure m (pre ++ j :: k :: post) < measure m (pre ++ i :: j :: post) :=
        measure_append_lt pre (by simp) (measure_cons_lt hij (by simp))
      obtain ⟨κ, hκ1, hκ2, hκ3⟩ := ih _ (hM ▸ hdec) (pre ++ j :: k :: post) rfl
      exact ⟨κ, hκ1, hκ2.trans hprod, hκ3.trans hlen⟩

/-- 単調増加なリストで, 先頭 `a` が最小かつ `a` の重複度が `k` 以上なら,
先頭 `k` 個はすべて `a`。 -/
theorem take_eq_replicate_of_isChain :
    ∀ (l : List (Fin m)) (a : Fin m) (k : ℕ), l.IsChain (· ≤ ·) → (∀ y ∈ l, a ≤ y) →
      k ≤ l.count a → l.take k = List.replicate k a := by
  intro l
  induction l with
  | nil => intro a k _ _ hk; simp at hk; simp [hk]
  | cons b t ih =>
    intro a k hchain hmin hk
    cases k with
    | zero => simp
    | succ k' =>
      have hba : a ≤ b := hmin b (by simp)
      by_cases hab : b = a
      · subst hab
        have hchain' : t.IsChain (· ≤ ·) := (List.isChain_cons.mp hchain).2
        have hmin' : ∀ y ∈ t, b ≤ y := fun y hy => hmin y (List.mem_cons_of_mem _ hy)
        have hk' : k' ≤ t.count b := by
          rw [List.count_cons_self] at hk
          omega
        rw [List.take_succ_cons, ih b k' hchain' hmin' hk', List.replicate_succ]
      · exfalso
        have hzero : t.count a = 0 := by
          refine List.count_eq_zero_of_not_mem fun hmem => ?_
          have hbt : b ≤ a := by
            have hchain' := List.isChain_cons.mp hchain
            exact List.rel_of_pairwise_cons (List.isChain_iff_pairwise.mp hchain) hmem
          exact hab (le_antisymm hbt hba)
        rw [List.count_cons_of_ne (Ne.symm (fun h => hab h.symm)), hzero] at hk
        omega

/-- ⭐ 単調増加な添字列は, 積を保ったまま各添字の重複度を `n` 未満にできる。 -/
theorem exists_counts_lt {G : Type*} [Group G] (xs : Fin m → G) {n : ℕ} (hn : 0 < n)
    (hexp : ∀ i : Fin m, xs i ^ n = 1) :
    ∀ (N : ℕ) (κ : List (Fin m)), κ.length ≤ N → κ.IsChain (· ≤ ·) →
      ∃ κ' : List (Fin m), κ'.IsChain (· ≤ ·) ∧ (∀ i, κ'.count i < n) ∧
        (∀ i, κ'.count i ≤ κ.count i) ∧ (κ'.map xs).prod = (κ.map xs).prod := by
  intro N
  induction N with
  | zero =>
    intro κ hlen _
    have : κ = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨[], List.isChain_nil, fun i => by simpa using hn, fun i => by simp, rfl⟩
  | succ N ih =>
    intro κ hlen hchain
    cases κ with
    | nil => exact ⟨[], List.isChain_nil, fun i => by simpa using hn, fun i => by simp, rfl⟩
    | cons a t =>
      by_cases hcnt : n ≤ (a :: t).count a
      · -- 先頭 `n` 個はすべて `a`; 落としても積は変わらない
        have hmin : ∀ y ∈ a :: t, a ≤ y := by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact le_rfl
          · exact List.rel_of_pairwise_cons (List.isChain_iff_pairwise.mp hchain) hy
        have htake := take_eq_replicate_of_isChain (a :: t) a n hchain hmin hcnt
        have hsplit : (a :: t) = List.replicate n a ++ (a :: t).drop n := by
          conv_lhs => rw [← List.take_append_drop n (a :: t)]
          rw [htake]
        have hdroplen : ((a :: t).drop n).length ≤ N := by
          have hd : ((a :: t).drop n).length = (a :: t).length - n := List.length_drop
          simp only [List.length_cons] at hd hlen ⊢
          omega
        have hdropchain : ((a :: t).drop n).IsChain (· ≤ ·) := hchain.drop n
        obtain ⟨κ', hκ1, hκ2, hκ4, hκ3⟩ := ih _ hdroplen hdropchain
        refine ⟨κ', hκ1, hκ2, fun i => (hκ4 i).trans
          ((List.drop_sublist n (a :: t)).count_le i), ?_⟩
        rw [hκ3]
        conv_rhs => rw [hsplit]
        simp only [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate,
          hexp, one_mul]
      · -- 先頭を残して残りを再帰
        have hchain' : t.IsChain (· ≤ ·) := (List.isChain_cons.mp hchain).2
        obtain ⟨κ', hκ1, hκ2, hκ4, hκ3⟩ :=
          ih t (by simp only [List.length_cons] at hlen; omega) hchain'
        have hcnt' : (a :: t).count a < n := by omega
        refine ⟨a :: κ', ?_, ?_, ?_, ?_⟩
        · refine List.isChain_cons.mpr ⟨?_, hκ1⟩
          intro y hy
          have hyκ : y ∈ κ' := List.mem_of_mem_head? hy
          have hyt : y ∈ t := by
            have h1 : 0 < κ'.count y := List.count_pos_iff.mpr hyκ
            have h2 : 0 < t.count y := lt_of_lt_of_le h1 (hκ4 y)
            exact List.count_pos_iff.mp h2
          exact List.rel_of_pairwise_cons (List.isChain_iff_pairwise.mp hchain) hyt
        · intro i
          rcases eq_or_ne i a with rfl | hia
          · rw [List.count_cons_self]
            rw [List.count_cons_self] at hcnt'
            have := hκ4 i
            omega
          · rw [List.count_cons_of_ne (Ne.symm hia)]
            exact hκ2 i
        · intro i
          rcases eq_or_ne i a with rfl | hia
          · rw [List.count_cons_self, List.count_cons_self]
            exact Nat.succ_le_succ (hκ4 i)
          · rw [List.count_cons_of_ne (Ne.symm hia), List.count_cons_of_ne (Ne.symm hia)]
            exact hκ4 i
        · simp only [List.map_cons, List.prod_cons, hκ3]

/-- 単調増加なリストは重複度ベクトルで決まる。 -/
theorem eq_of_count_eq {κ κ' : List (Fin m)} (h : κ.IsChain (· ≤ ·)) (h' : κ'.IsChain (· ≤ ·))
    (hc : ∀ i, κ.count i = κ'.count i) : κ = κ' :=
  List.Perm.eq_of_sortedLE (List.sortedLE_iff_isChain.mpr h) (List.sortedLE_iff_isChain.mpr h')
    (List.perm_iff_count.mpr hc)

/-- `xs` の像の元からなるリストは添字列で書ける。 -/
theorem exists_index_list {G : Type*} [Group G] (xs : Fin m → G) :
    ∀ {l : List G}, (∀ y ∈ l, y ∈ Set.range xs) → ∃ ι : List (Fin m), (ι.map xs).prod = l.prod := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons a t ih =>
    intro hl
    obtain ⟨i, hi⟩ := hl a (by simp)
    obtain ⟨ι, hι⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    exact ⟨i :: ι, by simp [hi, hι]⟩

end Sort5B2

/-- ⭐ **Isaacs Problem 5B.2** (添字形): `xs : Fin m → G` の像が共役で閉じ, 各 `xs i ^ n = 1`
なら `|⟨range xs⟩| ≤ n ^ m`。

**証明**: `⟨range xs⟩` の元は `xs` の元の積 (`x⁻¹ = x^{n-1}` なので逆元は不要;
既存 `Dietzmann.exists_list_subset_prod_eq`)。添字列に直し, 隣接交換で単調増加に整列し
(`Sort5B2.exists_chain'_map_prod_eq`), 各重複度を `n` 未満に落とす
(`Sort5B2.exists_counts_lt`)。単調増加列は重複度ベクトルで決まる (`Sort5B2.eq_of_count_eq`)
ので, そのような添字列は `Fin m → Fin n` に単射的に埋まり, 個数は `n^m` 以下。 -/
theorem card_closure_range_le {G : Type*} [Group G] {m : ℕ} (xs : Fin m → G) {n : ℕ}
    (hn : 0 < n) (hexp : ∀ i, xs i ^ n = 1)
    (hconj : ∀ i j : Fin m, ∃ k : Fin m, (xs j)⁻¹ * xs i * xs j = xs k) :
    Nat.card ↥(Subgroup.closure (Set.range xs)) ≤ n ^ m := by
  classical
  have hinj : Function.Injective
      (fun κ : {κ : List (Fin m) // κ.IsChain (· ≤ ·) ∧ ∀ i, κ.count i < n} =>
        (fun i => (⟨(κ : List (Fin m)).count i, κ.2.2 i⟩ : Fin n))) := by
    intro κ κ' h
    refine Subtype.ext (Sort5B2.eq_of_count_eq κ.2.1 κ'.2.1 fun i => ?_)
    exact congrArg Fin.val (congrFun h i)
  have : Finite {κ : List (Fin m) // κ.IsChain (· ≤ ·) ∧ ∀ i, κ.count i < n} :=
    Finite.of_injective _ hinj
  have hcardT : Nat.card {κ : List (Fin m) // κ.IsChain (· ≤ ·) ∧ ∀ i, κ.count i < n} ≤ n ^ m := by
    calc Nat.card {κ : List (Fin m) // κ.IsChain (· ≤ ·) ∧ ∀ i, κ.count i < n}
        ≤ Nat.card (Fin m → Fin n) := Nat.card_le_card_of_injective _ hinj
      _ = n ^ m := by simp
  have hmem : ∀ κ : {κ : List (Fin m) // κ.IsChain (· ≤ ·) ∧ ∀ i, κ.count i < n},
      (((κ : List (Fin m)).map xs).prod) ∈ Subgroup.closure (Set.range xs) := by
    intro κ
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
    exact Subgroup.subset_closure ⟨i, rfl⟩
  refine le_trans (Nat.card_le_card_of_surjective
    (fun κ => (⟨_, hmem κ⟩ : ↥(Subgroup.closure (Set.range xs)))) ?_) hcardT
  rintro ⟨g, hg⟩
  have hexp' : ∀ x ∈ Set.range xs, x ^ n = 1 := by
    rintro x ⟨i, rfl⟩
    exact hexp i
  have hg' : g ∈ Submonoid.closure (Set.range xs ∪ (Set.range xs)⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid]
    exact hg
  obtain ⟨l, hlmem, hlprod⟩ := Submonoid.exists_list_of_mem_closure hg'
  simp only [Set.mem_union, Set.mem_inv] at hlmem
  obtain ⟨l₁, hl₁X, hl₁prod⟩ := Dietzmann.exists_list_subset_prod_eq hn hexp' hlmem
  obtain ⟨ι, hι⟩ := Sort5B2.exists_index_list xs hl₁X
  obtain ⟨κ, hκchain, hκprod, -⟩ := Sort5B2.exists_chain'_map_prod_eq xs hconj ι
  obtain ⟨κ', hκ'chain, hκ'cnt, -, hκ'prod⟩ :=
    Sort5B2.exists_counts_lt xs hn hexp κ.length κ le_rfl hκchain
  refine ⟨⟨κ', hκ'chain, hκ'cnt⟩, Subtype.ext ?_⟩
  change (κ'.map xs).prod = g
  rw [hκ'prod, hκprod, hι, hl₁prod, hlprod]


/-- ⭐ **Isaacs Problem 5B.2** (書籍の形): Dietzmann (Thm 5.10) の状況で `|X| = m` なら
`|⟨X⟩| ≤ n ^ m`。

`X` の枚挙 `xs : Fin m → G` を取り `card_closure_range_le` を適用するだけ。 -/
theorem card_closure_le_pow_card {G : Type*} [Group G] {X : Set G} (hfin : X.Finite)
    (hconj : ∀ x ∈ X, ∀ g : G, g * x * g⁻¹ ∈ X) {n : ℕ} (hn : 0 < n)
    (hexp : ∀ x ∈ X, x ^ n = 1) :
    Nat.card ↥(Subgroup.closure X) ≤ n ^ hfin.toFinset.card := by
  classical
  set e : Fin hfin.toFinset.card ≃ ↥hfin.toFinset := hfin.toFinset.equivFin.symm with he
  set xs : Fin hfin.toFinset.card → G := fun i => ((e i : G)) with hxs
  have hrange : Set.range xs = X := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact hfin.mem_toFinset.mp (e i).2
    · intro hy
      exact ⟨e.symm ⟨y, hfin.mem_toFinset.mpr hy⟩, by simp [hxs]⟩
  have hexp' : ∀ i, xs i ^ n = 1 := fun i => hexp _ (by rw [← hrange]; exact ⟨i, rfl⟩)
  have hconj' : ∀ i j, ∃ k, (xs j)⁻¹ * xs i * xs j = xs k := by
    intro i j
    have hmem : (xs j)⁻¹ * xs i * xs j ∈ X := by
      have := hconj (xs i) (by rw [← hrange]; exact ⟨i, rfl⟩) (xs j)⁻¹
      simpa using this
    rw [← hrange] at hmem
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, hk.symm⟩
  have := card_closure_range_le xs hn hexp' hconj'
  rwa [hrange] at this

end

end OddOrder.Isaacs.Ch05
