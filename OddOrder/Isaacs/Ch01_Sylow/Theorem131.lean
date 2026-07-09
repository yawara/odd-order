/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Basic

/-!
# Theorem131

Prefix-split from `OddOrder.Isaacs.Ch01_Sylow.Main` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Isaacs.Ch01
open scoped IsMulCommutative

section /- 1E: Small-order groups, normal subgroup of index 2 (pp. 31-34) -/
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ### Isaacs Thm 1.31: `|G| = p²q` ⇒ Sylow `p` または `q` が正規.

証明方針 (Isaacs §1E):
* `n_q ∣ p²`, `n_q ≡ 1 (mod q)`. 故 `n_q ∈ {1, p, p²}`.
* `n_q = 1`: Sylow `q` 正規.
* `n_q = p`: `q ∣ p − 1`.
* `n_q = p²`: `q ∣ p² − 1 = (p−1)(p+1)`; `q ∣ p−1` または `q ∣ p+1`.
* `q < p` の場合, `q ∣ p − 1` でも `q ∣ p + 1` でも矛盾なく成立し,
  自動的に `n_p = 1` まで進むには別途 `n_p ∣ q`, `n_p ≡ 1 (mod p)` から
  `n_p = 1` を得る (この場合, `q < p` なので `n_p = q` は不可).
* `p < q` の場合, `q ≤ p − 1 < p < q` または `q ≤ p + 1` で `q = p + 1`,
  すなわち `(p, q) = (2, 3)`, `|G| = 12`. このとき `n_3 = 4` から
  `Sylow 2` の正規性を, "元の位数 3 が 8 個, 残り 4 個が Sylow 2" の
  数え上げで示す. -/

/-- Helper: For `|G| = p² · q` with `p, q` distinct primes,
the cardinality of any Sylow `q`-subgroup is `q`. -/
private lemma card_sylow_q_of_card_eq_sq_mul_prime
    [Finite G] {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ 2 * q) (Q : Sylow q G) :
    Nat.card (Q : Subgroup G) = q := by
  have hpne : (p ^ 2 : ℕ) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hqne : (q : ℕ) ≠ 0 := hq.out.ne_zero
  rw [Sylow.card_eq_multiplicity Q, hcard,
      Nat.factorization_mul hpne hqne, Finsupp.add_apply,
      Nat.Prime.factorization_pow hp.out, hq.out.factorization,
      Finsupp.single_apply, Finsupp.single_apply,
      if_neg hpq, if_pos rfl, zero_add, pow_one]

/-- Helper: For `|G| = p² · q` with `p, q` distinct primes,
the cardinality of any Sylow `p`-subgroup is `p²`. -/
private lemma card_sylow_p_of_card_eq_sq_mul_prime
    [Finite G] {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ 2 * q) (P : Sylow p G) :
    Nat.card (P : Subgroup G) = p ^ 2 := by
  have hpne : (p ^ 2 : ℕ) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hqne : (q : ℕ) ≠ 0 := hq.out.ne_zero
  rw [Sylow.card_eq_multiplicity P, hcard,
      Nat.factorization_mul hpne hqne, Finsupp.add_apply,
      Nat.Prime.factorization_pow hp.out, hq.out.factorization,
      Finsupp.single_apply, Finsupp.single_apply,
      if_pos rfl, if_neg (Ne.symm hpq), add_zero]

/-- Helper: For `|G| = p² · q` with `p, q` distinct primes,
the index of any Sylow `q`-subgroup is `p²`. -/
private lemma index_sylow_q_of_card_eq_sq_mul_prime
    [Finite G] {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ 2 * q) (Q : Sylow q G) :
    (Q : Subgroup G).index = p ^ 2 := by
  have hQ := card_sylow_q_of_card_eq_sq_mul_prime hpq hcard Q
  have h := (Q : Subgroup G).card_mul_index
  rw [hQ, hcard] at h
  have hq_pos : 0 < q := hq.out.pos
  exact Nat.eq_of_mul_eq_mul_left hq_pos (by linarith [h])

/-- Helper: For `|G| = p² · q` with `p, q` distinct primes,
the index of any Sylow `p`-subgroup is `q`. -/
private lemma index_sylow_p_of_card_eq_sq_mul_prime
    [Finite G] {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ 2 * q) (P : Sylow p G) :
    (P : Subgroup G).index = q := by
  have hP := card_sylow_p_of_card_eq_sq_mul_prime hpq hcard P
  have h := (P : Subgroup G).card_mul_index
  rw [hP, hcard] at h
  have hpsq_pos : 0 < p ^ 2 := pow_pos hp.out.pos 2
  exact Nat.eq_of_mul_eq_mul_left hpsq_pos h

/-- **Isaacs Thm 1.31** (case `q < p`).  `|G| = p² · q` (p, q 異なる素数) で
`q < p` のとき, Sylow `p`-部分群は正規.

証明: `n_p ∣ q`, `n_p ≡ 1 (mod p)`.  `n_p ∈ {1, q}`.  `n_p = q` なら
`p ∣ q − 1` で `p ≤ q − 1 < q < p`, 矛盾.  ゆえに `n_p = 1`. -/
theorem sylow_normal_of_card_eq_sq_mul_prime_lt
    [Finite G] {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hqp : q < p) (hcard : Nat.card G = p ^ 2 * q) :
    ∃ P : Sylow p G, (P : Subgroup G).Normal := by
  haveI : Finite (Sylow p G) := by
    have hG_pos : 0 < Nat.card G := Nat.card_pos
    haveI : Fintype G := Fintype.ofFinite G
    infer_instance
  have hpq : p ≠ q := (ne_of_lt hqp).symm
  -- n_p | q
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  have hidx : (P : Subgroup G).index = q :=
    index_sylow_p_of_card_eq_sq_mul_prime hpq hcard P
  have hdvd : Nat.card (Sylow p G) ∣ q := by
    rw [← hidx]; exact Sylow.card_dvd_index P
  have hmod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  -- n_p ∈ {1, q}
  rcases (Nat.dvd_prime hq.out).mp hdvd with h1 | hq_eq
  · -- n_p = 1
    refine ⟨P, ?_⟩
    haveI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Sylow.normal_of_subsingleton P
  · -- n_p = q.  Then p ∣ q − 1.  But q < p and q ≥ 1, so q − 1 < p, contradiction.
    exfalso
    rw [hq_eq] at hmod
    -- hmod : q ≡ 1 [MOD p], q ≥ 1 so this means p ∣ q - 1
    have hq_ge : 1 ≤ q := hq.out.one_lt.le
    have hdvd_sub : p ∣ q - 1 := (Nat.modEq_iff_dvd' hq_ge).mp hmod.symm
    -- q - 1 < p since q < p
    have hqm1_lt : q - 1 < p := by omega
    -- q - 1 = 0 (forced by p ∣ q-1 and 0 ≤ q-1 < p, and p ≥ 2)
    have hp_pos : 0 < p := hp.out.pos
    have hqm1_eq : q - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_sub hqm1_lt
    -- So q ≤ 1, but q is prime so q ≥ 2.
    have : q ≤ 1 := by omega
    exact absurd this (not_le.mpr hq.out.one_lt)

/-- Helper: For `|G| = 12` with `n_3 = 4` (i.e., 4 distinct Sylow 3-subgroups),
any Sylow 2-subgroup is normal.

証明 (数え上げ): Sylow 3 部分群は 4 個, 各位数 3, 互いの共通部分は trivial.
ゆえに位数 3 の元は 8 個.  非単位元で位数 3 でない元は 12 − 8 − 1 = 3 個.
Sylow 2-部分群 `S` は位数 4 で 3 個の非単位元を持ち, 全て位数 3 ではない (位数 ∣ 4).
ゆえに `S \ {1} = {g | g ≠ 1 ∧ orderOf g ≠ 3}` (3 元集合).  任意の Sylow 2 で同様.
よって全ての Sylow 2 は同じ非単位元集合を持ち, 同一の部分群.  Subsingleton. -/
private lemma sylow_two_normal_of_card_twelve_of_four_sylow_three
    [Finite G] (hcard : Nat.card G = 12)
    (hn3 : Nat.card (Sylow 3 G) = 4) :
    ∃ P : Sylow 2 G, (P : Subgroup G).Normal := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype G := Fintype.ofFinite G
  classical
  have hpq : (2 : ℕ) ≠ 3 := by norm_num
  have h12 : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  have hcard2 : Nat.card G = 2 ^ 2 * 3 := hcard.trans h12
  -- |Sylow 3-subgroup| = 3.
  have hcard_S3 : ∀ P : Sylow 3 G, Nat.card (P : Subgroup G) = 3 :=
    fun P => card_sylow_q_of_card_eq_sq_mul_prime hpq hcard2 P
  -- |Sylow 2-subgroup| = 4.
  have hcard_S2 : ∀ P : Sylow 2 G, Nat.card (P : Subgroup G) = 4 := by
    intro P
    exact card_sylow_p_of_card_eq_sq_mul_prime hpq hcard2 P
  -- Fintype version of Sylow 3 card.
  have hfin_S3 : ∀ P : Sylow 3 G, Fintype.card (P : Subgroup G) = 3 := by
    intro P; rw [← Nat.card_eq_fintype_card]; exact hcard_S3 P
  have hfin_S2 : ∀ P : Sylow 2 G, Fintype.card (P : Subgroup G) = 4 := by
    intro P; rw [← Nat.card_eq_fintype_card]; exact hcard_S2 P
  have hG_fin : Fintype.card G = 12 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  -- For Sylow 3-subgroups: distinct P ≠ Q have trivial intersection.
  have hinter_trivial : ∀ P Q : Sylow 3 G, P ≠ Q →
      ((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) = ⊥ := by
    intro P Q hne
    have hcardP := hcard_S3 P
    have hcardQ := hcard_S3 Q
    have h_dvd_P : Nat.card ((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) ∣
        Nat.card (P : Subgroup G) := Subgroup.card_dvd_of_le inf_le_left
    rw [hcardP] at h_dvd_P
    rcases (Nat.dvd_prime Nat.prime_three).mp h_dvd_P with hone | hthree
    · exact (Subgroup.card_eq_one (H := (P : Subgroup G) ⊓ (Q : Subgroup G))).mp hone
    · exfalso
      apply hne
      have h_le_eq : ((P : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) = (P : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hthree, hcardP])
      have hP_le_Q : (P : Subgroup G) ≤ (Q : Subgroup G) := h_le_eq ▸ inf_le_right
      have hPQ_subgroup : (P : Subgroup G) = (Q : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge hP_le_Q (by rw [hcardP, hcardQ])
      exact Sylow.ext hPQ_subgroup
  -- Define the Finset of order-3 elements.
  let U : Finset G := Finset.univ.filter (fun g => orderOf g = 3)
  -- Compute |U| = 8.
  -- U = ⋃ P, (P-as-Finset \ {1}).  Pairwise disjoint.  Each has card 2.
  have hU_card : U.card = 8 := by
    -- Per-Sylow Finset: define f P := (Subgroup.carrier P)-as-Finset \ {1}.
    let f : Sylow 3 G → Finset G :=
      fun P => (P : Subgroup G).carrier.toFinset \ {1}
    -- |f P| = 2.
    have hf_card : ∀ P : Sylow 3 G, (f P).card = 2 := by
      intro P
      have hP_card : (P : Subgroup G).carrier.toFinset.card = 3 := by
        rw [Set.toFinset_card]
        change Fintype.card (P : Subgroup G) = 3
        exact hfin_S3 P
      have h_sub : ({(1 : G)} : Finset G) ⊆ (P : Subgroup G).carrier.toFinset := by
        intro x hx
        simp only [Finset.mem_singleton] at hx
        subst hx
        simp [Set.mem_toFinset]
      rw [Finset.card_sdiff_of_subset h_sub, hP_card, Finset.card_singleton]
    -- f is pairwise disjoint on univ.
    have hf_pwd : ((Finset.univ : Finset (Sylow 3 G)) : Set (Sylow 3 G)).PairwiseDisjoint f := by
      intro P _ Q _ hne
      simp only [f, Function.onFun, Finset.disjoint_iff_ne]
      rintro x hx y hy rfl
      simp only [Finset.mem_sdiff, Set.mem_toFinset,
        Finset.mem_singleton] at hx hy
      have h_in : x ∈ (P : Subgroup G) ⊓ (Q : Subgroup G) := ⟨hx.1, hy.1⟩
      rw [hinter_trivial P Q hne] at h_in
      exact hx.2 (Subgroup.mem_bot.mp h_in)
    -- U = ⋃_{P} f P as a biUnion.
    have hU_eq : U = (Finset.univ : Finset (Sylow 3 G)).biUnion f := by
      ext g
      simp only [U, f, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Finset.mem_sdiff, Set.mem_toFinset,
        Finset.mem_singleton]
      constructor
      · intro hg
        have hg_ne_one : g ≠ 1 := by
          intro h; rw [h, orderOf_one] at hg; omega
        have h_pgroup : IsPGroup 3 (Subgroup.zpowers g) := by
          rw [IsPGroup.iff_card]
          exact ⟨1, by rw [Nat.card_zpowers, hg, pow_one]⟩
        obtain ⟨P, hP⟩ := h_pgroup.exists_le_sylow
        exact ⟨P, hP (Subgroup.mem_zpowers g), hg_ne_one⟩
      · rintro ⟨P, hgP, hg_ne⟩
        have hcardP := hcard_S3 P
        have h_ord_dvd : orderOf (⟨g, hgP⟩ : (P : Subgroup G)) ∣ Nat.card (P : Subgroup G) :=
          orderOf_dvd_natCard _
        rw [hcardP] at h_ord_dvd
        have h_ord_g : orderOf g ∣ 3 := by
          rw [Subgroup.orderOf_mk] at h_ord_dvd
          exact h_ord_dvd
        rcases (Nat.dvd_prime Nat.prime_three).mp h_ord_g with hone | hthree
        · exact absurd (orderOf_eq_one_iff.mp hone) hg_ne
        · exact hthree
    rw [hU_eq, Finset.card_biUnion hf_pwd]
    simp_rw [hf_card]
    rw [Finset.sum_const, smul_eq_mul]
    have hSylow3_card : (Finset.univ : Finset (Sylow 3 G)).card = 4 := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact hn3
    rw [hSylow3_card]
  -- Now define V := non-identity, order ≠ 3 elements as a Finset.
  let V : Finset G := ((Finset.univ : Finset G) \ U) \ ({1} : Finset G)
  -- |V| = 12 - 8 - 1 = 3.
  have hV_card : V.card = 3 := by
    have h1_notU : (1 : G) ∉ U := by
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, orderOf_one]
      omega
    have h_sub : U ⊆ (Finset.univ : Finset G) := Finset.subset_univ _
    have h_sub2 : ({(1 : G)} : Finset G) ⊆ (Finset.univ : Finset G) \ U := by
      simp [Finset.singleton_subset_iff, h1_notU]
    change (((Finset.univ : Finset G) \ U) \ ({1} : Finset G)).card = 3
    rw [Finset.card_sdiff_of_subset h_sub2, Finset.card_sdiff_of_subset h_sub,
      Finset.card_univ, hG_fin, hU_card, Finset.card_singleton]
  -- Every non-identity element of a Sylow 2-subgroup is in V.
  -- (its order divides 4, so ≠ 3.)
  have h_S2_sub_V : ∀ P : Sylow 2 G,
      ((P : Subgroup G).carrier.toFinset \ {1} : Finset G) ⊆ V := by
    intro P x hx
    simp only [Finset.mem_sdiff, Set.mem_toFinset,
      Finset.mem_singleton] at hx
    obtain ⟨hxP, hx_ne⟩ := hx
    have h_ord_dvd : orderOf (⟨x, hxP⟩ : (P : Subgroup G)) ∣ Nat.card (P : Subgroup G) :=
      orderOf_dvd_natCard _
    rw [hcard_S2 P] at h_ord_dvd
    have h_ord_x : orderOf x ∣ 4 := by
      rw [Subgroup.orderOf_mk] at h_ord_dvd
      exact h_ord_dvd
    have h_ord_ne_3 : orderOf x ≠ 3 := by
      intro heq
      rw [heq] at h_ord_x
      omega
    -- V = Finset.univ \ U \ {1}.  Show x ∈ V.
    change x ∈ ((Finset.univ : Finset G) \ U) \ ({1} : Finset G)
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h_ord_ne_3
    · simp [hx_ne]
  -- |S2 \ {1}| = 3.
  have h_S2_card : ∀ P : Sylow 2 G,
      ((P : Subgroup G).carrier.toFinset \ {1} : Finset G).card = 3 := by
    intro P
    have hP_card : (P : Subgroup G).carrier.toFinset.card = 4 := by
      rw [Set.toFinset_card]
      change Fintype.card (P : Subgroup G) = 4
      exact hfin_S2 P
    have h_sub : ({(1 : G)} : Finset G) ⊆ (P : Subgroup G).carrier.toFinset := by
      intro x hx
      simp only [Finset.mem_singleton] at hx; subst hx
      simp [Set.mem_toFinset]
    rw [Finset.card_sdiff_of_subset h_sub, hP_card, Finset.card_singleton]
  -- So every Sylow 2 has non-id Finset = V (cardinality coincides with ⊆).
  have h_S2_eq_V : ∀ P : Sylow 2 G,
      ((P : Subgroup G).carrier.toFinset \ {1} : Finset G) = V := by
    intro P
    exact Finset.eq_of_subset_of_card_le (h_S2_sub_V P)
      (by rw [hV_card, h_S2_card P])
  -- Two Sylow 2-subgroups P Q: non-id parts equal, plus both contain 1, so as Finsets they equal.
  -- Hence as subgroups, equal.
  have h_S2_eq : ∀ P Q : Sylow 2 G, (P : Subgroup G) = (Q : Subgroup G) := by
    intro P Q
    have hP := h_S2_eq_V P
    have hQ := h_S2_eq_V Q
    have h_carriers : ((P : Subgroup G).carrier.toFinset : Finset G) =
        (Q : Subgroup G).carrier.toFinset := by
      have hP_carr : ((P : Subgroup G).carrier.toFinset \ {1} : Finset G) ∪ {(1 : G)} =
          (P : Subgroup G).carrier.toFinset := by
        rw [Finset.sdiff_union_self_eq_union]
        rw [Finset.union_eq_left.mpr]
        intro x hx
        simp only [Finset.mem_singleton] at hx
        subst hx
        simp [Set.mem_toFinset]
      have hQ_carr : ((Q : Subgroup G).carrier.toFinset \ {1} : Finset G) ∪ {(1 : G)} =
          (Q : Subgroup G).carrier.toFinset := by
        rw [Finset.sdiff_union_self_eq_union]
        rw [Finset.union_eq_left.mpr]
        intro x hx
        simp only [Finset.mem_singleton] at hx
        subst hx
        simp [Set.mem_toFinset]
      rw [← hP_carr, ← hQ_carr, hP, hQ]
    -- From Finset equality to Set equality to Subgroup equality.
    apply SetLike.coe_injective
    ext x
    have hP_iff : x ∈ ((P : Subgroup G).carrier.toFinset : Finset G) ↔
        x ∈ (P : Subgroup G) := by
      simp [Set.mem_toFinset]
    have hQ_iff : x ∈ ((Q : Subgroup G).carrier.toFinset : Finset G) ↔
        x ∈ (Q : Subgroup G) := by
      simp [Set.mem_toFinset]
    constructor
    · intro hxP
      have : x ∈ ((P : Subgroup G).carrier.toFinset : Finset G) := hP_iff.mpr hxP
      rw [h_carriers] at this
      exact hQ_iff.mp this
    · intro hxQ
      have : x ∈ ((Q : Subgroup G).carrier.toFinset : Finset G) := hQ_iff.mpr hxQ
      rw [← h_carriers] at this
      exact hP_iff.mp this
  -- Hence all Sylow 2-subgroups equal as Sylows.
  haveI : Subsingleton (Sylow 2 G) := by
    refine ⟨fun P Q => Sylow.ext ?_⟩
    exact h_S2_eq P Q
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := G)
  exact ⟨P, Sylow.normal_of_subsingleton P⟩

/-- **Isaacs Thm 1.31** (case `p < q`).  `|G| = p² · q` (p, q 異なる素数) で
`p < q` のとき, Sylow `p` または Sylow `q` が正規.

証明: `n_q ∣ p²`, `n_q ≡ 1 (mod q)`.  `n_q ∈ {1, p, p²}`.
* `n_q = 1`: Sylow `q` 正規.
* `n_q = p`: `q ∣ p − 1` で `p < q` と矛盾.
* `n_q = p²`: `q ∣ p² − 1`.  `q ∣ p − 1` 矛盾, `q ∣ p + 1` で `q = p + 1`, 連続素数,
  `(p, q) = (2, 3)`, `|G| = 12`.  ここで `n_3 = 4` から Sylow 2 が正規. -/
theorem sylow_normal_of_card_eq_sq_mul_prime_gt
    [Finite G] {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq_lt : p < q) (hcard : Nat.card G = p ^ 2 * q) :
    (∃ P : Sylow p G, (P : Subgroup G).Normal) ∨
    (∃ Q : Sylow q G, (Q : Subgroup G).Normal) := by
  haveI : Fintype G := Fintype.ofFinite G
  classical
  haveI : Finite (Sylow q G) := inferInstance
  haveI : Finite (Sylow p G) := inferInstance
  have hpq : p ≠ q := ne_of_lt hpq_lt
  -- n_q ∣ p² and n_q ≡ 1 (mod q)
  obtain ⟨Q⟩ := Sylow.nonempty (p := q) (G := G)
  have hidx : (Q : Subgroup G).index = p ^ 2 :=
    index_sylow_q_of_card_eq_sq_mul_prime hpq hcard Q
  have hdvd_psq : Nat.card (Sylow q G) ∣ p ^ 2 := by
    rw [← hidx]; exact Sylow.card_dvd_index Q
  have hmod : Nat.card (Sylow q G) ≡ 1 [MOD q] := card_sylow_modEq_one q G
  -- n_q is a power of p, ≤ 2.
  obtain ⟨k, hk, hk_eq⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd_psq
  interval_cases k
  · -- n_q = 1
    right
    rw [pow_zero] at hk_eq
    refine ⟨Q, ?_⟩
    haveI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hk_eq).1
    exact Sylow.normal_of_subsingleton Q
  · -- n_q = p.  Then p ≡ 1 (mod q), so q ∣ p - 1, but p < q ⇒ p - 1 < q ⇒ contradiction.
    exfalso
    rw [pow_one] at hk_eq
    rw [hk_eq] at hmod
    have hp_ge : 1 ≤ p := hp.out.one_lt.le
    have : q ∣ p - 1 := (Nat.modEq_iff_dvd' hp_ge).mp hmod.symm
    have hpm1_lt : p - 1 < q := by omega
    have hpm1_eq : p - 1 = 0 := Nat.eq_zero_of_dvd_of_lt this hpm1_lt
    have : p ≤ 1 := by omega
    exact absurd this (not_le.mpr hp.out.one_lt)
  · -- n_q = p².  Then p² ≡ 1 (mod q), so q ∣ p² - 1 = (p-1)(p+1).
    -- Hence q ∣ p-1 or q ∣ p+1. First is impossible (p < q), so q ∣ p+1.
    rw [hk_eq] at hmod
    have hpsq_ge : 1 ≤ p ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.out.ne_zero)
    have hq_dvd : q ∣ p ^ 2 - 1 := (Nat.modEq_iff_dvd' hpsq_ge).mp hmod.symm
    -- p² - 1 = (p - 1)(p + 1)
    have hp_ge : 2 ≤ p := hp.out.two_le
    have h_factor : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      have hp_ge1 : 1 ≤ p := by omega
      have : (p - 1) * (p + 1) + 1 = p ^ 2 := by
        zify [hp_ge1]
        ring
      omega
    rw [h_factor] at hq_dvd
    rcases (Nat.Prime.dvd_mul hq.out).mp hq_dvd with hq_dvd_sub | hq_dvd_add
    · -- q ∣ p - 1, but q > p ⇒ q > p - 1 ⇒ p - 1 = 0, so p ≤ 1, contradicting p prime.
      exfalso
      have hpm1_lt : p - 1 < q := by omega
      have hpm1_eq : p - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hq_dvd_sub hpm1_lt
      have : p ≤ 1 := by omega
      exact absurd this (not_le.mpr hp.out.one_lt)
    · -- q ∣ p + 1, so q ≤ p + 1.  Combined with p < q: q ∈ {p+1}, so q = p+1.
      -- Both prime, so (p, q) = (2, 3).
      have hq_le : q ≤ p + 1 := Nat.le_of_dvd (by omega) hq_dvd_add
      have hq_eq : q = p + 1 := by omega
      -- Now p and p+1 are consecutive primes, so p = 2.
      have hp_eq : p = 2 := by
        by_contra hp_ne_2
        -- p ≥ 2 prime and p ≠ 2 ⇒ p ≥ 3, p odd.
        have hp_ge3 : 3 ≤ p := by
          have := hp.out.two_le; omega
        have hp_odd : Odd p := hp.out.odd_of_ne_two hp_ne_2
        obtain ⟨m, hm⟩ := hp_odd
        -- p + 1 = 2 * (m + 1), so 2 ∣ p + 1 = q.
        have h2_dvd_q : 2 ∣ q := by
          rw [hq_eq, hm]; exact ⟨m + 1, by ring⟩
        -- 2 ∣ q (prime) means q = 2 or q = 2... but q > p ≥ 3 > 2, contradiction.
        have hq_eq_2 : q = 2 :=
          ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq.out).mp h2_dvd_q).symm
        omega
      have hq_eq_3 : q = 3 := by omega
      -- So |G| = 4 * 3 = 12 and n_3 = 4.
      have hcard12 : Nat.card G = 12 := by
        rw [hcard, hp_eq, hq_eq_3]; norm_num
      have hn3_eq : Nat.card (Sylow 3 G) = 4 := by
        have h1 : Nat.card (Sylow q G) = p ^ 2 := hk_eq
        rw [hp_eq, hq_eq_3] at h1
        -- h1 : Nat.card (Sylow 3 G) = 2 ^ 2
        rw [h1]; norm_num
      -- Apply helper.
      left
      -- We need ∃ P : Sylow p G normal, but `p = 2`.  Convert.
      subst hp_eq
      subst hq_eq_3
      -- Now p = 2, q = 3.  We have hn3_eq : Nat.card (Sylow 3 G) = 4.
      exact sylow_two_normal_of_card_twelve_of_four_sylow_three hcard12 hn3_eq

/-- **Isaacs Thm 1.31** (一般形).  `|G| = p² · q` (p, q 異なる素数) ⇒ Sylow `p` または
Sylow `q` が正規.  特殊な場合分け (`q < p` または `p < q`) を統合した形.

`q < p` の場合: `sylow_normal_of_card_eq_sq_mul_prime_lt` で Sylow `p` 正規.
`p < q` の場合: `sylow_normal_of_card_eq_sq_mul_prime_gt` で適切な側が正規. -/
theorem sylow_normal_of_card_eq_sq_mul_prime
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ 2 * q) :
    (∃ P : Sylow p G, (P : Subgroup G).Normal) ∨
    (∃ Q : Sylow q G, (Q : Subgroup G).Normal) := by
  rcases lt_or_gt_of_ne hpq with hpq_lt | hqp_lt
  · -- p < q
    exact sylow_normal_of_card_eq_sq_mul_prime_gt hpq_lt hcard
  · -- q < p
    left
    exact sylow_normal_of_card_eq_sq_mul_prime_lt hqp_lt hcard

/-! ### Thm 1.32 — `|G| = p³q` helpers and main theorem. -/

/-- Distinct Sylow `q` subgroups of prime order `q` intersect trivially. -/
lemma sylow_q_disjoint_of_prime_card
    [Finite G] {q : ℕ} [Fact q.Prime]
    {Q₁ Q₂ : Sylow q G} (hne : Q₁ ≠ Q₂)
    (hQ₁ : Nat.card (Q₁ : Subgroup G) = q) :
    (Q₁ : Subgroup G) ⊓ (Q₂ : Subgroup G) = ⊥ := by
  have hcoe : (Q₁ : Subgroup G) ⊓ (Q₂ : Subgroup G) ≤ (Q₁ : Subgroup G) := inf_le_left
  have hdvd : Nat.card ((Q₁ : Subgroup G) ⊓ (Q₂ : Subgroup G) : Subgroup G) ∣
      Nat.card (Q₁ : Subgroup G) := Subgroup.card_dvd_of_le hcoe
  rw [hQ₁] at hdvd
  rcases (Nat.dvd_prime (Fact.out (p := q.Prime))).mp hdvd with h1 | hq
  · exact (Subgroup.card_eq_one (H := (Q₁ : Subgroup G) ⊓ (Q₂ : Subgroup G))).mp h1
  · exfalso
    apply hne
    have hinf_eq : (Q₁ : Subgroup G) ⊓ (Q₂ : Subgroup G) = (Q₁ : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge hcoe
      omega
    have hQ₁_le_Q₂ : (Q₁ : Subgroup G) ≤ (Q₂ : Subgroup G) := by
      rw [← hinf_eq]; exact inf_le_right
    have h := Q₁.is_maximal' Q₂.isPGroup' hQ₁_le_Q₂
    exact Sylow.ext h.symm

/-- For `|G| = p^3 · q` (p, q distinct primes), any Sylow `p` subgroup has order `p^3`. -/
theorem card_sylow_p_of_card_eq_cube_mul_prime
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ 3 * q) (P : Sylow p G) :
    Nat.card P = p ^ 3 := by
  have hmul := P.card_eq_multiplicity (G := G)
  have hpne : p ^ 3 ≠ 0 := pow_ne_zero _ (Fact.out (p := p.Prime)).ne_zero
  have hqne : q ≠ 0 := (Fact.out (p := q.Prime)).ne_zero
  rw [hcard, Nat.factorization_mul hpne hqne,
      Nat.Prime.factorization_pow (Fact.out (p := p.Prime))] at hmul
  simp only [Finsupp.coe_add, Pi.add_apply,
             (Fact.out (p := q.Prime)).factorization, Finsupp.single_apply,
             if_neg (Ne.symm hpq)] at hmul
  simpa using hmul

/-- For `|G| = p^3 · q` (p, q distinct primes), any Sylow `q` subgroup has order `q`. -/
theorem card_sylow_q_of_card_eq_cube_mul_prime
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ 3 * q) (Q : Sylow q G) :
    Nat.card Q = q := by
  have hmul := Q.card_eq_multiplicity (G := G)
  have hpne : p ^ 3 ≠ 0 := pow_ne_zero _ (Fact.out (p := p.Prime)).ne_zero
  have hqne : q ≠ 0 := (Fact.out (p := q.Prime)).ne_zero
  rw [hcard, Nat.factorization_mul hpne hqne,
      Nat.Prime.factorization_pow (Fact.out (p := p.Prime))] at hmul
  simp only [Finsupp.coe_add, Pi.add_apply,
             Finsupp.single_apply, if_neg hpq] at hmul
  simpa [(Fact.out (p := q.Prime)).factorization_self] using hmul

/-- For `|G| = p^3 · q` (p, q distinct primes), any Sylow `p` subgroup has index `q`. -/
theorem index_sylow_p_of_card_eq_cube_mul_prime
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ 3 * q) (P : Sylow p G) :
    (P : Subgroup G).index = q := by
  have hPcard := card_sylow_p_of_card_eq_cube_mul_prime hpq hcard P
  have h1 : Nat.card (P : Subgroup G) * (P : Subgroup G).index = Nat.card G :=
    Subgroup.card_mul_index _
  rw [hcard, hPcard] at h1
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out (p := p.Prime)).pos 3) h1

/-- For `|G| = p^3 · q` (p, q distinct primes), any Sylow `q` subgroup has index `p^3`. -/
theorem index_sylow_q_of_card_eq_cube_mul_prime
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ 3 * q) (Q : Sylow q G) :
    (Q : Subgroup G).index = p ^ 3 := by
  have hQcard := card_sylow_q_of_card_eq_cube_mul_prime hpq hcard Q
  have h1 : Nat.card (Q : Subgroup G) * (Q : Subgroup G).index = Nat.card G :=
    Subgroup.card_mul_index _
  rw [hcard, hQcard, mul_comm (p ^ 3) q] at h1
  exact Nat.eq_of_mul_eq_mul_left (Fact.out (p := q.Prime)).pos h1

/-- For `|G| = p^3 · q` (p, q 異素数) with `n_q = p^3`, the Sylow `p`-subgroup is normal.

Counting argument: each Sylow `q` has prime order `q` (distinct ones disjoint outside {1}),
so order-`q` elements form a set of size `n_q * (q-1) = p^3 (q-1)`.  The complement
(`p^3 - 1` non-identity elements + identity = `p^3` elements) contains every Sylow `p`-subgroup
(since elements of a Sylow `p` have `p`-power order, not order `q`).  Each Sylow `p` has exactly
`p^3` elements, matching the complement's size, so any two Sylow `p` subgroups coincide as sets,
hence are equal.  Therefore `n_p = 1`. -/
private lemma sylow_p_normal_of_card_eq_cube_mul_prime_of_nq_eq_pcube
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ 3 * q)
    (hnq : Nat.card (Sylow q G) = p ^ 3) :
    ∃ P : Sylow p G, (P : Subgroup G).Normal := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (Sylow q G) := Fintype.ofFinite _
  haveI : Fintype (Sylow p G) := Fintype.ofFinite _
  classical
  have hpprime := Fact.out (p := p.Prime)
  have hqprime := Fact.out (p := q.Prime)
  have hp_pos : 0 < p := hpprime.pos
  have hq_pos : 0 < q := hqprime.pos
  have hp3_pos : 0 < p ^ 3 := pow_pos hp_pos 3
  have hcard_Sq : ∀ Q : Sylow q G, Nat.card (Q : Subgroup G) = q :=
    fun Q => card_sylow_q_of_card_eq_cube_mul_prime hpq hcard Q
  have hcard_Sp : ∀ P : Sylow p G, Nat.card (P : Subgroup G) = p ^ 3 :=
    fun P => card_sylow_p_of_card_eq_cube_mul_prime hpq hcard P
  have hfin_Sq : ∀ Q : Sylow q G, Fintype.card (Q : Subgroup G) = q := by
    intro Q; rw [← Nat.card_eq_fintype_card]; exact hcard_Sq Q
  have hfin_Sp : ∀ P : Sylow p G, Fintype.card (P : Subgroup G) = p ^ 3 := by
    intro P; rw [← Nat.card_eq_fintype_card]; exact hcard_Sp P
  have hG_fin : Fintype.card G = p ^ 3 * q := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  -- U := order-q elements (a Finset).
  let U : Finset G := Finset.univ.filter (fun g => orderOf g = q)
  -- |U| = p^3 * (q - 1).
  have hU_card : U.card = p ^ 3 * (q - 1) := by
    let f : Sylow q G → Finset G :=
      fun Q => (Q : Subgroup G).carrier.toFinset \ {1}
    have hf_card : ∀ Q : Sylow q G, (f Q).card = q - 1 := by
      intro Q
      have hQ_card : (Q : Subgroup G).carrier.toFinset.card = q := by
        rw [Set.toFinset_card]
        change Fintype.card (Q : Subgroup G) = q
        exact hfin_Sq Q
      have h_sub : ({(1 : G)} : Finset G) ⊆ (Q : Subgroup G).carrier.toFinset := by
        intro x hx
        simp only [Finset.mem_singleton] at hx; subst hx
        simp [Set.mem_toFinset]
      rw [Finset.card_sdiff_of_subset h_sub, hQ_card, Finset.card_singleton]
    have hf_pwd : ((Finset.univ : Finset (Sylow q G)) : Set (Sylow q G)).PairwiseDisjoint f := by
      intro Q1 _ Q2 _ hne
      simp only [f, Function.onFun, Finset.disjoint_iff_ne]
      rintro x hx y hy rfl
      simp only [Finset.mem_sdiff, Set.mem_toFinset, Finset.mem_singleton] at hx hy
      have h_in : x ∈ (Q1 : Subgroup G) ⊓ (Q2 : Subgroup G) := ⟨hx.1, hy.1⟩
      rw [sylow_q_disjoint_of_prime_card hne (hcard_Sq Q1)] at h_in
      exact hx.2 (Subgroup.mem_bot.mp h_in)
    have hU_eq : U = (Finset.univ : Finset (Sylow q G)).biUnion f := by
      ext g
      simp only [U, f, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Finset.mem_sdiff, Set.mem_toFinset, Finset.mem_singleton]
      constructor
      · intro hg
        have hg_ne_one : g ≠ 1 := by
          intro h; rw [h, orderOf_one] at hg
          have := hqprime.two_le
          omega
        have h_qgroup : IsPGroup q (Subgroup.zpowers g) := by
          rw [IsPGroup.iff_card]
          exact ⟨1, by rw [Nat.card_zpowers, hg, pow_one]⟩
        obtain ⟨Q, hQ⟩ := h_qgroup.exists_le_sylow
        exact ⟨Q, hQ (Subgroup.mem_zpowers g), hg_ne_one⟩
      · rintro ⟨Q, hgQ, hg_ne⟩
        have hcardQ := hcard_Sq Q
        have h_ord_dvd : orderOf (⟨g, hgQ⟩ : (Q : Subgroup G)) ∣ Nat.card (Q : Subgroup G) :=
          orderOf_dvd_natCard _
        rw [hcardQ] at h_ord_dvd
        have h_ord_g : orderOf g ∣ q := by
          rw [Subgroup.orderOf_mk] at h_ord_dvd
          exact h_ord_dvd
        rcases (Nat.dvd_prime hqprime).mp h_ord_g with hone | hq_eq
        · exact absurd (orderOf_eq_one_iff.mp hone) hg_ne
        · exact hq_eq
    rw [hU_eq, Finset.card_biUnion hf_pwd]
    simp_rw [hf_card]
    rw [Finset.sum_const, smul_eq_mul]
    have hSylowq_card : (Finset.univ : Finset (Sylow q G)).card = p ^ 3 := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact hnq
    rw [hSylowq_card]
  -- V := (G \ U) \ {1}.  |V| = p^3 - 1.
  let V : Finset G := ((Finset.univ : Finset G) \ U) \ ({1} : Finset G)
  have hV_card : V.card = p ^ 3 - 1 := by
    have h1_notU : (1 : G) ∉ U := by
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, orderOf_one]
      have := hqprime.two_le
      omega
    have h_sub : U ⊆ (Finset.univ : Finset G) := Finset.subset_univ _
    have h_sub2 : ({(1 : G)} : Finset G) ⊆ (Finset.univ : Finset G) \ U := by
      simp [Finset.singleton_subset_iff, h1_notU]
    change (((Finset.univ : Finset G) \ U) \ ({1} : Finset G)).card = p ^ 3 - 1
    rw [Finset.card_sdiff_of_subset h_sub2, Finset.card_sdiff_of_subset h_sub,
      Finset.card_univ, hG_fin, hU_card, Finset.card_singleton]
    -- Goal: p^3 * q - p^3 * (q - 1) - 1 = p^3 - 1
    have harith : p ^ 3 * q = p ^ 3 * (q - 1) + p ^ 3 := by
      have hq_ge : 1 ≤ q := hq_pos
      have heq : q - 1 + 1 = q := Nat.sub_add_cancel hq_ge
      conv_lhs => rw [← heq]
      ring
    omega
  -- Every non-identity element of a Sylow p subgroup is in V.
  have h_Sp_sub_V : ∀ P : Sylow p G,
      ((P : Subgroup G).carrier.toFinset \ {1} : Finset G) ⊆ V := by
    intro P x hx
    simp only [Finset.mem_sdiff, Set.mem_toFinset, Finset.mem_singleton] at hx
    obtain ⟨hxP, hx_ne⟩ := hx
    have h_ord_dvd : orderOf (⟨x, hxP⟩ : (P : Subgroup G)) ∣ Nat.card (P : Subgroup G) :=
      orderOf_dvd_natCard _
    rw [hcard_Sp P] at h_ord_dvd
    have h_ord_x : orderOf x ∣ p ^ 3 := by
      rw [Subgroup.orderOf_mk] at h_ord_dvd
      exact h_ord_dvd
    have h_ord_ne_q : orderOf x ≠ q := by
      intro heq
      rw [heq] at h_ord_x
      have hq_dvd_p : q ∣ p := hqprime.dvd_of_dvd_pow h_ord_x
      have hq_eq_p : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hpprime).mp hq_dvd_p
      exact hpq hq_eq_p.symm
    change x ∈ ((Finset.univ : Finset G) \ U) \ ({1} : Finset G)
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h_ord_ne_q
    · simp [hx_ne]
  -- |Sylow p \ {1}| = p^3 - 1.
  have h_Sp_card : ∀ P : Sylow p G,
      ((P : Subgroup G).carrier.toFinset \ {1} : Finset G).card = p ^ 3 - 1 := by
    intro P
    have hP_card : (P : Subgroup G).carrier.toFinset.card = p ^ 3 := by
      rw [Set.toFinset_card]
      change Fintype.card (P : Subgroup G) = p ^ 3
      exact hfin_Sp P
    have h_sub : ({(1 : G)} : Finset G) ⊆ (P : Subgroup G).carrier.toFinset := by
      intro x hx
      simp only [Finset.mem_singleton] at hx; subst hx
      simp [Set.mem_toFinset]
    rw [Finset.card_sdiff_of_subset h_sub, hP_card, Finset.card_singleton]
  -- Sylow p \ {1} = V.
  have h_Sp_eq_V : ∀ P : Sylow p G,
      ((P : Subgroup G).carrier.toFinset \ {1} : Finset G) = V := by
    intro P
    exact Finset.eq_of_subset_of_card_le (h_Sp_sub_V P)
      (by rw [hV_card, h_Sp_card P])
  -- All Sylow p subgroups are equal.
  have h_Sp_eq : ∀ P Q : Sylow p G, (P : Subgroup G) = (Q : Subgroup G) := by
    intro P Q
    have hP := h_Sp_eq_V P
    have hQ' := h_Sp_eq_V Q
    have h_carriers : ((P : Subgroup G).carrier.toFinset : Finset G) =
        (Q : Subgroup G).carrier.toFinset := by
      have hP_carr : ((P : Subgroup G).carrier.toFinset \ {1} : Finset G) ∪ {(1 : G)} =
          (P : Subgroup G).carrier.toFinset := by
        rw [Finset.sdiff_union_self_eq_union]
        rw [Finset.union_eq_left.mpr]
        intro x hx
        simp only [Finset.mem_singleton] at hx; subst hx
        simp [Set.mem_toFinset]
      have hQ_carr : ((Q : Subgroup G).carrier.toFinset \ {1} : Finset G) ∪ {(1 : G)} =
          (Q : Subgroup G).carrier.toFinset := by
        rw [Finset.sdiff_union_self_eq_union]
        rw [Finset.union_eq_left.mpr]
        intro x hx
        simp only [Finset.mem_singleton] at hx; subst hx
        simp [Set.mem_toFinset]
      rw [← hP_carr, ← hQ_carr, hP, hQ']
    apply SetLike.coe_injective
    ext x
    have hP_iff : x ∈ ((P : Subgroup G).carrier.toFinset : Finset G) ↔
        x ∈ (P : Subgroup G) := by simp [Set.mem_toFinset]
    have hQ_iff : x ∈ ((Q : Subgroup G).carrier.toFinset : Finset G) ↔
        x ∈ (Q : Subgroup G) := by simp [Set.mem_toFinset]
    constructor
    · intro hxP
      have : x ∈ ((P : Subgroup G).carrier.toFinset : Finset G) := hP_iff.mpr hxP
      rw [h_carriers] at this
      exact hQ_iff.mp this
    · intro hxQ
      have : x ∈ ((Q : Subgroup G).carrier.toFinset : Finset G) := hQ_iff.mpr hxQ
      rw [← h_carriers] at this
      exact hP_iff.mp this
  haveI : Subsingleton (Sylow p G) := ⟨fun P Q => Sylow.ext (h_Sp_eq P Q)⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  exact ⟨P, Sylow.normal_of_subsingleton P⟩

/-- **Isaacs Thm 1.32**.  `|G| = p^3 · q` (p, q 異素数) ⇒ Sylow `p` または Sylow `q` 部分群が
正規, または `|G| = 24` (Thm 1.33 で扱う例外).

Isaacs p.31 の証明: `n_p` の場合分け (∈ {1, q}). `n_p = 1` なら直ちに Sylow `p` 正規.
`n_p = q` なら `p < q`, 次に `n_q ∈ {1, p, p², p³}` で場合分け.
* `n_q = 1`: Sylow `q` 正規.
* `n_q = p`: Sylow III で `q ∣ p-1`, しかし `p < q` で矛盾.
* `n_q = p²`: Sylow III で `q ∣ p²-1 = (p-1)(p+1)`. `p < q` で `q ∤ p-1` ⇒ `q ∣ p+1`,
  `q ≤ p+1` と `p < q` で `q = p+1`, 連続素数で `(p,q) = (2,3)` ⇒ `|G| = 24`.
* `n_q = p³`: 各 Sylow `q` が prime 位数 `q` で互いに自明交差, 元素勘定で Sylow `p` 一意 ⇒ 正規. -/
theorem sylow_normal_of_card_eq_cube_mul_prime
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ 3 * q) :
    (∃ P : Sylow p G, (P : Subgroup G).Normal) ∨
    (∃ Q : Sylow q G, (Q : Subgroup G).Normal) ∨
    Nat.card G = 24 := by
  classical
  haveI : Finite (Sylow p G) := inferInstance
  haveI : Finite (Sylow q G) := inferInstance
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  obtain ⟨Q⟩ := Sylow.nonempty (p := q) (G := G)
  have hPindex : (P : Subgroup G).index = q :=
    index_sylow_p_of_card_eq_cube_mul_prime hpq hcard P
  have hQindex : (Q : Subgroup G).index = p ^ 3 :=
    index_sylow_q_of_card_eq_cube_mul_prime hpq hcard Q
  have hnp_dvd : Nat.card (Sylow p G) ∣ q := hPindex ▸ P.card_dvd_index
  have hnp_mod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  have hnq_dvd : Nat.card (Sylow q G) ∣ p ^ 3 := hQindex ▸ Q.card_dvd_index
  have hnq_mod : Nat.card (Sylow q G) ≡ 1 [MOD q] := card_sylow_modEq_one q G
  rcases (Nat.dvd_prime (Fact.out (p := q.Prime))).mp hnp_dvd with hnp1 | hnpq
  · haveI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hnp1).1
    exact Or.inl ⟨P, Sylow.normal_of_subsingleton P⟩
  · have hp_dvd_q_sub_1 : p ∣ q - 1 := by
      rw [hnpq] at hnp_mod
      have hq1 : 1 ≤ q := (Fact.out (p := q.Prime)).pos
      exact (Nat.modEq_iff_dvd' hq1).mp hnp_mod.symm
    have hp_lt_q : p < q := by
      have hp_le : p ≤ q - 1 := Nat.le_of_dvd (by
        have hq1 : 1 < q := (Fact.out (p := q.Prime)).one_lt
        omega) hp_dvd_q_sub_1
      omega
    rcases (Nat.dvd_prime_pow (Fact.out (p := p.Prime)) (m := 3)).mp hnq_dvd
      with ⟨k, hk_le, hk_eq⟩
    interval_cases k
    · -- k = 0: n_q = 1, Sylow q normal.
      have hk_eq_one : Nat.card (Sylow q G) = 1 := by
        simpa using hk_eq
      haveI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hk_eq_one).1
      exact Or.inr (Or.inl ⟨Q, Sylow.normal_of_subsingleton Q⟩)
    · -- k = 1: n_q = p. By Sylow III: p ≡ 1 (mod q), so q ∣ p - 1. But p < q ⇒ contradiction.
      exfalso
      have hk_eq_p : Nat.card (Sylow q G) = p := by
        simpa using hk_eq
      rw [hk_eq_p] at hnq_mod
      have hp_ge : 1 ≤ p := (Fact.out (p := p.Prime)).pos
      have hq_dvd : q ∣ p - 1 := (Nat.modEq_iff_dvd' hp_ge).mp hnq_mod.symm
      have hq_le_p : q ≤ p - 1 := Nat.le_of_dvd (by
        have := (Fact.out (p := p.Prime)).two_le
        omega) hq_dvd
      omega
    · -- k = 2: n_q = p². q ∣ p² - 1 = (p+1)(p-1). q prime, p < q ⇒ q ∣ p+1, q = p+1, (p,q)=(2,3).
      rw [hk_eq] at hnq_mod
      have hpprime := Fact.out (p := p.Prime)
      have hqprime := Fact.out (p := q.Prime)
      have hp_ge_two : 2 ≤ p := hpprime.two_le
      have hp2_ge : 1 ≤ p ^ 2 := by
        have : 0 < p ^ 2 := pow_pos hpprime.pos 2
        omega
      have hq_dvd_p2_sub_1 : q ∣ p ^ 2 - 1 := (Nat.modEq_iff_dvd' hp2_ge).mp hnq_mod.symm
      have hp2_eq : p ^ 2 - 1 = (p + 1) * (p - 1) := by
        have h := Nat.sq_sub_sq p 1
        simpa [one_pow] using h
      rw [hp2_eq] at hq_dvd_p2_sub_1
      rcases (Nat.Prime.dvd_mul hqprime).mp hq_dvd_p2_sub_1 with hq_dvd_succ | hq_dvd_pred
      · have hq_le_succ : q ≤ p + 1 := Nat.le_of_dvd (Nat.succ_pos p) hq_dvd_succ
        have hq_eq : q = p + 1 := by omega
        have hp_eq : p = 2 := by
          rcases hpprime.eq_two_or_odd with h2 | hodd
          · exact h2
          · exfalso
            have hsucc_prime : (p + 1).Prime := hq_eq ▸ hqprime
            rcases hsucc_prime.eq_two_or_odd with hs2 | hs_odd
            · omega
            · omega
        have hq_eq_3 : q = 3 := by rw [hq_eq, hp_eq]
        refine Or.inr (Or.inr ?_)
        rw [hcard, hp_eq, hq_eq_3]
        norm_num
      · exfalso
        have hp_sub_pos : 0 < p - 1 := by omega
        have hq_le : q ≤ p - 1 := Nat.le_of_dvd hp_sub_pos hq_dvd_pred
        omega
    · -- k = 3: n_q = p³.  By the counting helper, Sylow p is normal.
      exact Or.inl (sylow_p_normal_of_card_eq_cube_mul_prime_of_nq_eq_pcube hpq hcard hk_eq)

/-! ### Thm 1.33 — `|G| = 24` で Sylow 2 も Sylow 3 も非正規ならば `G ≅ S₄`. -/

/-- `(24 : ℕ).factorization 3 = 1`. -/
private lemma factorization_twenty_four_three : (24 : ℕ).factorization 3 = 1 := by
  have hmul_eq : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  rw [show (24 : ℕ) = 2 ^ 3 * 3 from hmul_eq,
      Nat.factorization_mul (pow_ne_zero _ Nat.prime_two.ne_zero) Nat.prime_three.ne_zero,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.Prime.factorization Nat.prime_three]
  simp

/-- `(24 : ℕ).factorization 2 = 3`. -/
private lemma factorization_twenty_four_two : (24 : ℕ).factorization 2 = 3 := by
  have hmul_eq : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  rw [show (24 : ℕ) = 2 ^ 3 * 3 from hmul_eq,
      Nat.factorization_mul (pow_ne_zero _ Nat.prime_two.ne_zero) Nat.prime_three.ne_zero,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.Prime.factorization Nat.prime_three]
  simp

/-- `(12 : ℕ).factorization 2 = 2`. -/
private lemma factorization_twelve_two : (12 : ℕ).factorization 2 = 2 := by
  have hmul_eq : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  rw [show (12 : ℕ) = 2 ^ 2 * 3 from hmul_eq,
      Nat.factorization_mul (pow_ne_zero _ Nat.prime_two.ne_zero) Nat.prime_three.ne_zero,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.Prime.factorization Nat.prime_three]
  simp

/-- `(12 : ℕ).factorization 3 = 1`. -/
private lemma factorization_twelve_three : (12 : ℕ).factorization 3 = 1 := by
  have hmul_eq : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  rw [show (12 : ℕ) = 2 ^ 2 * 3 from hmul_eq,
      Nat.factorization_mul (pow_ne_zero _ Nat.prime_two.ne_zero) Nat.prime_three.ne_zero,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.Prime.factorization Nat.prime_three]
  simp

/-- `(6 : ℕ).factorization 3 = 1`. -/
private lemma factorization_six_three : (6 : ℕ).factorization 3 = 1 := by
  have hmul_eq : (6 : ℕ) = 2 * 3 := by norm_num
  rw [show (6 : ℕ) = 2 * 3 from hmul_eq,
      Nat.factorization_mul Nat.prime_two.ne_zero Nat.prime_three.ne_zero,
      Nat.Prime.factorization Nat.prime_two,
      Nat.Prime.factorization Nat.prime_three]
  simp

/-- 位数 24 の群の Sylow 3 部分群は位数 3. -/
private lemma card_sylow_three_of_card_twenty_four
    [Finite G] (hG : Nat.card G = 24) (P : Sylow 3 G) :
    Nat.card (P : Subgroup G) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmul := P.card_eq_multiplicity (G := G)
  rw [hG, factorization_twenty_four_three] at hmul
  simpa using hmul

/-- 位数 24 の群の Sylow 2 部分群は位数 8. -/
private lemma card_sylow_two_of_card_twenty_four
    [Finite G] (hG : Nat.card G = 24) (P : Sylow 2 G) :
    Nat.card (P : Subgroup G) = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul := P.card_eq_multiplicity (G := G)
  rw [hG, factorization_twenty_four_two] at hmul
  simpa using hmul

/-- 位数 12 の群の Sylow 2 部分群は位数 4. -/
private lemma card_sylow_two_of_card_twelve
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 12) (Q : Sylow 2 H) :
    Nat.card (Q : Subgroup H) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul := Q.card_eq_multiplicity (G := H)
  rw [hH, factorization_twelve_two] at hmul
  simpa using hmul

/-- 位数 12 の群の Sylow 3 部分群は位数 3. -/
private lemma card_sylow_three_of_card_twelve
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 12) (Q : Sylow 3 H) :
    Nat.card (Q : Subgroup H) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmul := Q.card_eq_multiplicity (G := H)
  rw [hH, factorization_twelve_three] at hmul
  simpa using hmul

/-- 位数 6 の群の Sylow 3 部分群は位数 3. -/
private lemma card_sylow_three_of_card_six
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 6) (Q : Sylow 3 H) :
    Nat.card (Q : Subgroup H) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmul := Q.card_eq_multiplicity (G := H)
  rw [hH, factorization_six_three] at hmul
  simpa using hmul

/-- 位数 6 の群の Sylow 3 部分群は一意. -/
private lemma subsingleton_sylow_three_of_card_six
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 6) :
    Subsingleton (Sylow 3 H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ := Sylow.nonempty (p := 3) (G := H)
  have hQ_card : Nat.card (Q : Subgroup H) = 3 := card_sylow_three_of_card_six hH Q
  have hQ_index : (Q : Subgroup H).index = 2 := by
    have h1 : Nat.card (Q : Subgroup H) * (Q : Subgroup H).index = Nat.card H :=
      Subgroup.card_mul_index _
    rw [hH, hQ_card] at h1; omega
  have hdvd : Nat.card (Sylow 3 H) ∣ 2 := hQ_index ▸ Q.card_dvd_index
  have hmod : Nat.card (Sylow 3 H) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 H
  have hle : Nat.card (Sylow 3 H) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hN3_eq_1 : Nat.card (Sylow 3 H) = 1 := by
    interval_cases (Nat.card (Sylow 3 H))
    all_goals first | rfl | (exfalso; revert hmod; decide)
  exact Finite.card_le_one_iff_subsingleton.mp (by omega)

/-- `|G| = 24` で Sylow 3 が非正規 (`n_3 > 1`) ならば `n_3 = 4`.

`n_3 ∣ 8` (`Sylow.card_dvd_index`, |G:P| = 24/3 = 8), `n_3 ≡ 1 mod 3` (Sylow III),
ゆえ `n_3 ∈ {1, 4}`. `n_3 > 1` より `n_3 = 4`. -/
private lemma card_sylow_three_of_card_eq_twenty_four
    [Finite G] (hcard : Nat.card G = 24) (hn3 : 1 < Nat.card (Sylow 3 G)) :
    Nat.card (Sylow 3 G) = 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := G)
  have hPcard : Nat.card (P : Subgroup G) = 3 :=
    card_sylow_three_of_card_twenty_four hcard P
  have hPindex : (P : Subgroup G).index = 8 := by
    have h1 : Nat.card (P : Subgroup G) * (P : Subgroup G).index = Nat.card G :=
      Subgroup.card_mul_index _
    rw [hcard, hPcard] at h1
    omega
  have hdvd : Nat.card (Sylow 3 G) ∣ 8 := hPindex ▸ P.card_dvd_index
  have hmod : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have hle : Nat.card (Sylow 3 G) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases (Nat.card (Sylow 3 G))
  all_goals first | omega | (exfalso; revert hmod; decide)

/-- `|G| = 24` で Sylow 3 が非正規 (`n_3 > 1`) ならば任意の Sylow 3 部分群の正規化群の位数は 6. -/
private lemma card_normalizer_sylow_three_of_card_eq_twenty_four
    [Finite G] (hcard : Nat.card G = 24) (hn3 : 1 < Nat.card (Sylow 3 G))
    (P : Sylow 3 G) :
    Nat.card (Subgroup.normalizer (P : Set G)) = 6 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn3_eq : Nat.card (Sylow 3 G) = 4 :=
    card_sylow_three_of_card_eq_twenty_four hcard hn3
  have hidx : (Subgroup.normalizer (P : Set G)).index = 4 := by
    rw [← P.card_eq_index_normalizer]; exact hn3_eq
  have h1 : Nat.card (Subgroup.normalizer (P : Set G)) *
      (Subgroup.normalizer (P : Set G)).index = Nat.card G :=
    Subgroup.card_mul_index _
  rw [hcard, hidx] at h1
  omega

/-- `|G| = 24`, Sylow 2 と Sylow 3 が共に非正規ならば `G ≅ S₄`.

**Isaacs Thm 1.33** (p.32).

証明骨子 (Isaacs):
* Phase 1: `n_3 ∈ {1, 4}`, 仮定 `n_3 > 1` から `n_3 = 4`. ゆえに `P ∈ Syl_3` に対し
  `N := N_G(P)` は `|N| = 6`.
* Phase 2: `G` が `G ⧸ N` (4 元) に左乗法作用 ⇒ `G →* Sym(G ⧸ N)`,
  核 `K = N.normalCore`.
* Phase 3 (難所): `K = ⊥` を示す.  `K ≤ N` で `|K| ∈ {1, 2, 3, 6}`.
  - `|K| = 6 ⇒ K = N ⇒ N ⊴ G ⇒ P` (`N` 内の唯一の Sylow 3) `⊴ G ⇒ n_3 = 1`, 矛盾.
  - `|K| = 3`: `K` は `N` の位数 3 部分群, 唯一なので `K = P ⊴ G ⇒ n_3 = 1`, 矛盾.
  - `|K| = 2`: `|G/K| = 12`.  Thm 1.31 で `G/K` の `n_2 = 1` または `n_3 = 1`:
    - `n_2(G/K) = 1`: 対応で `|S| = 8` の正規 Sylow 2 in `G ⇒ n_2 = 1`, 矛盾.
    - `n_3(G/K) = 1`: 対応で `|S| = 6` の正規部分群, 唯一の Sylow 3 (特性) ⇒ `n_3 = 1`, 矛盾.
* Phase 4: `K = ⊥` ⇒ `G →* Sym(G ⧸ N)` 単射. 両側 24 元で全単射 ⇒ `MulEquiv`. -/
theorem mulEquiv_perm_fin_four_of_card_twenty_four
    [Finite G] (hcard : Nat.card G = 24)
    (hn2 : 1 < Nat.card (Sylow 2 G))
    (hn3 : 1 < Nat.card (Sylow 3 G)) :
    Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype G := Fintype.ofFinite G
  -- Phase 1: n_3 = 4, |N| = 6.
  obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := G)
  have hPcard : Nat.card (P : Subgroup G) = 3 :=
    card_sylow_three_of_card_twenty_four hcard P
  set N : Subgroup G := Subgroup.normalizer (P : Set G) with hN_def
  have hN_card : Nat.card N = 6 :=
    card_normalizer_sylow_three_of_card_eq_twenty_four hcard hn3 P
  have hN_index : N.index = 4 := by
    have h1 : Nat.card N * N.index = Nat.card G := Subgroup.card_mul_index _
    rw [hcard, hN_card] at h1; omega
  have hP_le_N : (P : Subgroup G) ≤ N := Subgroup.le_normalizer
  haveI hN_sub3 : Subsingleton (Sylow 3 N) :=
    subsingleton_sylow_three_of_card_six hN_card
  let PN : Sylow 3 N := P.subtype hP_le_N
  have hPN_card : Nat.card (PN : Subgroup N) = 3 := by
    have hPN_equiv : (PN : Subgroup N) ≃* (P : Subgroup G) := by
      change ((P : Subgroup G).subgroupOf N) ≃* (P : Subgroup G)
      exact Subgroup.subgroupOfEquivOfLe hP_le_N
    rw [Nat.card_congr hPN_equiv.toEquiv]
    exact hPcard
  have hPN_map_eq_P : (PN : Subgroup N).map N.subtype = (P : Subgroup G) := by
    change ((P : Subgroup G).subgroupOf N).map N.subtype = (P : Subgroup G)
    exact Subgroup.map_subgroupOf_eq_of_le hP_le_N
  haveI hPN_normal : (PN : Subgroup N).Normal := PN.normal_of_subsingleton
  haveI hPN_char : (PN : Subgroup N).Characteristic :=
    Sylow.characteristic_of_normal PN hPN_normal
  -- Phase 2: define f : G →* Equiv.Perm (G ⧸ N), K = N.normalCore = f.ker.
  let f : G →* Equiv.Perm (G ⧸ N) := MulAction.toPermHom G (G ⧸ N)
  have hKer_eq : N.normalCore = f.ker := N.normalCore_eq_ker
  set K : Subgroup G := N.normalCore with hK_def
  have hK_le_N : K ≤ N := N.normalCore_le
  haveI hK_normal : K.Normal := N.normalCore_normal
  -- Phase 3: K = ⊥.
  have hK_dvd : Nat.card K ∣ 6 := by
    rw [← hN_card]; exact Subgroup.card_dvd_of_le hK_le_N
  have hK_pos : 0 < Nat.card K := Nat.card_pos
  have hK_le_six : Nat.card K ≤ 6 := Nat.le_of_dvd (by norm_num) hK_dvd
  have hK_card_in : Nat.card K = 1 ∨ Nat.card K = 2 ∨ Nat.card K = 3 ∨ Nat.card K = 6 := by
    rcases hK_dvd with ⟨k, hk⟩
    interval_cases (Nat.card K)
    all_goals omega
  have hK_eq_bot : K = ⊥ := by
    rcases hK_card_in with hKK | hKK | hKK | hKK
    · exact (Subgroup.card_eq_one (H := K)).mp hKK
    · -- |K| = 2: derive contradiction.
      exfalso
      have hquot_card : Nat.card (G ⧸ K) = 12 := by
        have h1 : Nat.card G = Nat.card (G ⧸ K) * Nat.card K :=
          K.card_eq_card_quotient_mul_card_subgroup
        rw [hcard, hKK] at h1; omega
      have h12_eq : Nat.card (G ⧸ K) = 2 ^ 2 * 3 := by rw [hquot_card]; norm_num
      have hpq : (2 : ℕ) ≠ 3 := by norm_num
      rcases sylow_normal_of_card_eq_sq_mul_prime (G := G ⧸ K) hpq h12_eq with
        ⟨S2_quot, hS2_quot_normal⟩ | ⟨S3_quot, hS3_quot_normal⟩
      · set S2 : Subgroup G := Subgroup.comap (QuotientGroup.mk' K) (S2_quot : Subgroup (G ⧸ K))
          with hS2_def
        haveI hS2_normal : S2.Normal := hS2_quot_normal.comap _
        have hS2_quot_card : Nat.card (S2_quot : Subgroup (G ⧸ K)) = 4 :=
          card_sylow_two_of_card_twelve hquot_card S2_quot
        have hS2_card : Nat.card S2 = 8 := by
          have hindex_eq : S2.index = (S2_quot : Subgroup (G ⧸ K)).index :=
            (S2_quot : Subgroup (G ⧸ K)).index_comap_of_surjective
              (QuotientGroup.mk'_surjective K)
          have hS2_quot_index : (S2_quot : Subgroup (G ⧸ K)).index = 3 := by
            have h1 : Nat.card (S2_quot : Subgroup (G ⧸ K)) *
                (S2_quot : Subgroup (G ⧸ K)).index = Nat.card (G ⧸ K) :=
              Subgroup.card_mul_index _
            rw [hquot_card, hS2_quot_card] at h1; omega
          have hS2_index : S2.index = 3 := hindex_eq.trans hS2_quot_index
          have h1 : Nat.card S2 * S2.index = Nat.card G := Subgroup.card_mul_index _
          rw [hcard, hS2_index] at h1; omega
        have hS2_pgroup : IsPGroup 2 S2 := by
          rw [IsPGroup.iff_card]
          exact ⟨3, by rw [hS2_card]; norm_num⟩
        obtain ⟨S2_syl, hS2_le_syl⟩ := hS2_pgroup.exists_le_sylow
        have hS2_card_syl : Nat.card (S2_syl : Subgroup G) = 8 :=
          card_sylow_two_of_card_twenty_four hcard S2_syl
        have hS2_eq : S2 = (S2_syl : Subgroup G) :=
          Subgroup.eq_of_le_of_card_ge hS2_le_syl (by rw [hS2_card, hS2_card_syl])
        haveI hS2_syl_normal : (S2_syl : Subgroup G).Normal := hS2_eq ▸ hS2_normal
        haveI : Unique (Sylow 2 G) := Sylow.unique_of_normal S2_syl hS2_syl_normal
        have hn2_eq : Nat.card (Sylow 2 G) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨S2_syl⟩⟩
        omega
      · set S3 : Subgroup G := Subgroup.comap (QuotientGroup.mk' K) (S3_quot : Subgroup (G ⧸ K))
          with hS3_def
        haveI hS3_normal : S3.Normal := hS3_quot_normal.comap _
        have hS3_quot_card : Nat.card (S3_quot : Subgroup (G ⧸ K)) = 3 :=
          card_sylow_three_of_card_twelve hquot_card S3_quot
        have hS3_card : Nat.card S3 = 6 := by
          have hindex_eq : S3.index = (S3_quot : Subgroup (G ⧸ K)).index :=
            (S3_quot : Subgroup (G ⧸ K)).index_comap_of_surjective
              (QuotientGroup.mk'_surjective K)
          have hS3_quot_index : (S3_quot : Subgroup (G ⧸ K)).index = 4 := by
            have h1 : Nat.card (S3_quot : Subgroup (G ⧸ K)) *
                (S3_quot : Subgroup (G ⧸ K)).index = Nat.card (G ⧸ K) :=
              Subgroup.card_mul_index _
            rw [hquot_card, hS3_quot_card] at h1; omega
          have hS3_index : S3.index = 4 := hindex_eq.trans hS3_quot_index
          have h1 : Nat.card S3 * S3.index = Nat.card G := Subgroup.card_mul_index _
          rw [hcard, hS3_index] at h1; omega
        haveI : Subsingleton (Sylow 3 S3) := subsingleton_sylow_three_of_card_six hS3_card
        obtain ⟨P3⟩ := Sylow.nonempty (p := 3) (G := S3)
        have hP3_card : Nat.card (P3 : Subgroup S3) = 3 :=
          card_sylow_three_of_card_six hS3_card P3
        haveI hP3_normal : (P3 : Subgroup S3).Normal := P3.normal_of_subsingleton
        haveI hP3_char : (P3 : Subgroup S3).Characteristic :=
          Sylow.characteristic_of_normal P3 hP3_normal
        haveI hP3_normal_in_G : ((P3 : Subgroup S3).map S3.subtype).Normal :=
          inferInstance
        have hP3_map_card : Nat.card ((P3 : Subgroup S3).map S3.subtype) = 3 := by
          rw [Subgroup.card_map_of_injective Subtype.coe_injective]
          exact hP3_card
        have hP3_map_pgroup : IsPGroup 3 ((P3 : Subgroup S3).map S3.subtype) := by
          rw [IsPGroup.iff_card]
          exact ⟨1, by rw [hP3_map_card, pow_one]⟩
        obtain ⟨P3_syl, hP3_le_syl⟩ := hP3_map_pgroup.exists_le_sylow
        have hP3_card_syl : Nat.card (P3_syl : Subgroup G) = 3 :=
          card_sylow_three_of_card_twenty_four hcard P3_syl
        have hP3_map_eq_syl : (P3 : Subgroup S3).map S3.subtype = (P3_syl : Subgroup G) :=
          Subgroup.eq_of_le_of_card_ge hP3_le_syl (by rw [hP3_map_card, hP3_card_syl])
        haveI hP3_syl_normal : (P3_syl : Subgroup G).Normal := hP3_map_eq_syl ▸ hP3_normal_in_G
        haveI : Unique (Sylow 3 G) := Sylow.unique_of_normal P3_syl hP3_syl_normal
        have hn3_eq : Nat.card (Sylow 3 G) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨P3_syl⟩⟩
        omega
    · -- |K| = 3.
      exfalso
      have hKsub_card : Nat.card (K.subgroupOf N) = 3 := by
        have hK_equiv : K.subgroupOf N ≃* K := Subgroup.subgroupOfEquivOfLe hK_le_N
        rw [Nat.card_congr hK_equiv.toEquiv]
        exact hKK
      have hKsub_pgroup : IsPGroup 3 (K.subgroupOf N) := by
        rw [IsPGroup.iff_card]
        exact ⟨1, by rw [hKsub_card, pow_one]⟩
      obtain ⟨QN, hKsub_le_QN⟩ := hKsub_pgroup.exists_le_sylow
      have hQN_eq_PN : QN = PN := Subsingleton.elim _ _
      have hQN_card : Nat.card (QN : Subgroup N) = 3 := hQN_eq_PN ▸ hPN_card
      have hKsub_eq_QN : K.subgroupOf N = (QN : Subgroup N) :=
        Subgroup.eq_of_le_of_card_ge hKsub_le_QN (by rw [hKsub_card, hQN_card])
      have hK_eq_P : K = (P : Subgroup G) := by
        rw [show K = (K.subgroupOf N).map N.subtype from
              (Subgroup.map_subgroupOf_eq_of_le hK_le_N).symm,
            hKsub_eq_QN, hQN_eq_PN, hPN_map_eq_P]
      have hP_normal : (P : Subgroup G).Normal := hK_eq_P ▸ hK_normal
      haveI : Unique (Sylow 3 G) := Sylow.unique_of_normal P hP_normal
      have hn3_eq : Nat.card (Sylow 3 G) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨P⟩⟩
      omega
    · -- |K| = 6.
      exfalso
      have hK_eq_N : K = N := Subgroup.eq_of_le_of_card_ge hK_le_N (by rw [hKK, hN_card])
      haveI hN_normal : N.Normal := hK_eq_N ▸ hK_normal
      haveI hPN_map_normal : ((PN : Subgroup N).map N.subtype).Normal := inferInstance
      have hP_normal : (P : Subgroup G).Normal := hPN_map_eq_P ▸ hPN_map_normal
      haveI : Unique (Sylow 3 G) := Sylow.unique_of_normal P hP_normal
      have hn3_eq : Nat.card (Sylow 3 G) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨P⟩⟩
      omega
  -- Phase 4: f is injective ⇒ surjective ⇒ MulEquiv.
  have hf_ker : f.ker = ⊥ := by rw [← hKer_eq]; exact hK_eq_bot
  have hf_inj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hf_ker
  have hquotN_card : Nat.card (G ⧸ N) = 4 := by rw [← N.index_eq_card]; exact hN_index
  haveI : Finite (G ⧸ N) := Nat.finite_of_card_ne_zero (by rw [hquotN_card]; norm_num)
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hfintype_card : Fintype.card (G ⧸ N) = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact hquotN_card
  let e : G ⧸ N ≃ Fin 4 := Fintype.equivFinOfCardEq hfintype_card
  let φ : Equiv.Perm (G ⧸ N) ≃* Equiv.Perm (Fin 4) := e.permCongrHom
  let f' : G →* Equiv.Perm (Fin 4) := φ.toMonoidHom.comp f
  have hf'_inj : Function.Injective f' := φ.injective.comp hf_inj
  have hperm_card : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm, Nat.card_fin]; decide
  haveI : Finite (Equiv.Perm (Fin 4)) := inferInstance
  haveI : Fintype (Equiv.Perm (Fin 4)) := Fintype.ofFinite _
  have hfin_perm_card : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [← Nat.card_eq_fintype_card]; exact hperm_card
  have hfin_G_card : Fintype.card G = 24 := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have hcard_eq : Fintype.card G = Fintype.card (Equiv.Perm (Fin 4)) := by
    rw [hfin_G_card, hfin_perm_card]
  have hf'_bij : Function.Bijective f' :=
    (Fintype.bijective_iff_injective_and_card f').mpr ⟨hf'_inj, hcard_eq⟩
  exact ⟨MulEquiv.ofBijective f' hf'_bij⟩

end
end OddOrder.Isaacs.Ch01
