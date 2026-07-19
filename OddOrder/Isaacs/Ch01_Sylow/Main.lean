/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Theorem131

/-!
# TAIL

Prefix-split from `OddOrder.Isaacs.Ch01_Sylow.Main` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Isaacs.Ch01
open scoped IsMulCommutative

section /- 1E: Small-order groups, normal subgroup of index 2 (pp. 31-34) -/
open scoped Pointwise

variable {G : Type*} [Group G]


/-! ### Thm 1.36 — `|G| = p^a q` 単純性破壊.  helpers + main. -/

/-- D = ⊥ 部分 case of Thm 1.36: |G| = p^a q, n_p = q (≥ 2), 全 Sylow `p` 対が自明交差
ならば Sylow `q` が正規.

Counting: 非単位元 p-元素 = `q(p^a-1)` 個 (Sylow `p` の互いに自明交差), 残り `q-1` 個は
非 p-冪.  Sylow `q` (素位数 `q`) は `q-1` 個の非単位元を寄与, 互いに自明交差.
`n_q (q-1) ≤ q-1` で `n_q ≥ 1` ⇒ `n_q = 1`, Sylow `q` 正規. -/
private lemma sylow_q_normal_of_card_eq_pa_q_of_sylow_p_disjoint
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {a : ℕ} (_ha : 1 ≤ a)
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ a * q)
    (hnpq : Nat.card (Sylow p G) = q)
    (hcard_Sp : ∀ R : Sylow p G, Nat.card (R : Subgroup G) = p ^ a)
    (hcard_Sq : ∀ R : Sylow q G, Nat.card (R : Subgroup G) = q)
    (hSp_disj : ∀ S T : Sylow p G, S ≠ T →
      (S : Subgroup G) ⊓ (T : Subgroup G) = ⊥) :
    ∃ Q : Sylow q G, (Q : Subgroup G).Normal := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (Sylow p G) := Fintype.ofFinite _
  haveI : Fintype (Sylow q G) := Fintype.ofFinite _
  have hpprime := Fact.out (p := p.Prime)
  have hqprime := Fact.out (p := q.Prime)
  have hp_pos := hpprime.pos
  have hq_pos := hqprime.pos
  have hq_ge_two := hqprime.two_le
  have hpa_pos : 0 < p ^ a := pow_pos hp_pos a
  have hG_fin : Fintype.card G = p ^ a * q := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have hSyl_count : Fintype.card (Sylow p G) = q := by
    rw [← Nat.card_eq_fintype_card]; exact hnpq
  -- Up := union of Sylow p's \ {1}.
  let Up : Finset G := (Finset.univ : Finset (Sylow p G)).biUnion
      (fun R => (R : Subgroup G).carrier.toFinset \ {1})
  have hcard_Up : Up.card = q * (p ^ a - 1) := by
    have hf_card : ∀ R : Sylow p G,
        ((R : Subgroup G).carrier.toFinset \ {1}).card = p ^ a - 1 := by
      intro R
      have hcard_R : (R : Subgroup G).carrier.toFinset.card = p ^ a := by
        rw [Set.toFinset_card]
        change Fintype.card (R : Subgroup G) = p ^ a
        rw [← Nat.card_eq_fintype_card]; exact hcard_Sp R
      have h_sub : ({(1 : G)} : Finset G) ⊆ (R : Subgroup G).carrier.toFinset := by
        intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
        simp [Set.mem_toFinset]
      rw [Finset.card_sdiff_of_subset h_sub, hcard_R, Finset.card_singleton]
    have hf_pwd : ((Finset.univ : Finset (Sylow p G)) : Set (Sylow p G)).PairwiseDisjoint
        (fun R => (R : Subgroup G).carrier.toFinset \ {1}) := by
      intro S1 _ S2 _ hne
      simp only [Function.onFun, Finset.disjoint_iff_ne]
      rintro x hx y hy rfl
      simp only [Finset.mem_sdiff, Set.mem_toFinset, Finset.mem_singleton] at hx hy
      have h_in : x ∈ (S1 : Subgroup G) ⊓ (S2 : Subgroup G) := ⟨hx.1, hy.1⟩
      rw [hSp_disj S1 S2 hne] at h_in
      exact hx.2 (Subgroup.mem_bot.mp h_in)
    rw [Finset.card_biUnion hf_pwd]
    simp_rw [hf_card]
    rw [Finset.sum_const, smul_eq_mul]
    have hsylcount : (Finset.univ : Finset (Sylow p G)).card = q := by
      rw [Finset.card_univ, hSyl_count]
    rw [hsylcount]
  -- Vq := G \ Up \ {1}.
  have h1_notUp : (1 : G) ∉ Up := by
    intro h
    obtain ⟨R, _, hR⟩ := Finset.mem_biUnion.mp h
    exact (Finset.mem_sdiff.mp hR).2 (Finset.mem_singleton.mpr rfl)
  let Vq : Finset G := ((Finset.univ : Finset G) \ Up) \ ({1} : Finset G)
  have hcard_Vq : Vq.card = q - 1 := by
    have h_sub : Up ⊆ (Finset.univ : Finset G) := Finset.subset_univ _
    have h_sub2 : ({(1 : G)} : Finset G) ⊆ (Finset.univ : Finset G) \ Up := by
      simp [Finset.singleton_subset_iff, h1_notUp]
    change (((Finset.univ : Finset G) \ Up) \ ({1} : Finset G)).card = q - 1
    rw [Finset.card_sdiff_of_subset h_sub2, Finset.card_sdiff_of_subset h_sub,
        Finset.card_univ, hG_fin, hcard_Up, Finset.card_singleton]
    have harith : p ^ a * q = q * (p ^ a - 1) + q := by
      have hp_ge : 1 ≤ p ^ a := hpa_pos
      have heq : p ^ a - 1 + 1 = p ^ a := Nat.sub_add_cancel hp_ge
      conv_lhs => rw [← heq]
      ring
    omega
  -- Sq_nonid := ∪ Sylow q's \ {1}. ⊆ Vq.
  let Sq_nonid : Finset G := (Finset.univ : Finset (Sylow q G)).biUnion
      (fun R => (R : Subgroup G).carrier.toFinset \ {1})
  have hSq_disj : ∀ Q1 Q2 : Sylow q G, Q1 ≠ Q2 →
      (Q1 : Subgroup G) ⊓ (Q2 : Subgroup G) = ⊥ :=
    fun Q1 Q2 hne => sylow_q_disjoint_of_prime_card hne (hcard_Sq Q1)
  have hcard_Sq_nonid : Sq_nonid.card = Fintype.card (Sylow q G) * (q - 1) := by
    have hf_card : ∀ R : Sylow q G,
        ((R : Subgroup G).carrier.toFinset \ {1}).card = q - 1 := by
      intro R
      have hcard_R : (R : Subgroup G).carrier.toFinset.card = q := by
        rw [Set.toFinset_card]
        change Fintype.card (R : Subgroup G) = q
        rw [← Nat.card_eq_fintype_card]; exact hcard_Sq R
      have h_sub : ({(1 : G)} : Finset G) ⊆ (R : Subgroup G).carrier.toFinset := by
        intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
        simp [Set.mem_toFinset]
      rw [Finset.card_sdiff_of_subset h_sub, hcard_R, Finset.card_singleton]
    have hf_pwd : ((Finset.univ : Finset (Sylow q G)) : Set (Sylow q G)).PairwiseDisjoint
        (fun R => (R : Subgroup G).carrier.toFinset \ {1}) := by
      intro Q1 _ Q2 _ hne
      simp only [Function.onFun, Finset.disjoint_iff_ne]
      rintro x hx y hy rfl
      simp only [Finset.mem_sdiff, Set.mem_toFinset, Finset.mem_singleton] at hx hy
      have h_in : x ∈ (Q1 : Subgroup G) ⊓ (Q2 : Subgroup G) := ⟨hx.1, hy.1⟩
      rw [hSq_disj Q1 Q2 hne] at h_in
      exact hx.2 (Subgroup.mem_bot.mp h_in)
    rw [Finset.card_biUnion hf_pwd]
    simp_rw [hf_card]
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
  have hSq_sub_Vq : Sq_nonid ⊆ Vq := by
    intro x hx
    simp only [Sq_nonid, Finset.mem_biUnion, Finset.mem_univ, true_and,
               Finset.mem_sdiff, Set.mem_toFinset, Finset.mem_singleton] at hx
    obtain ⟨Q, hxQ, hx_ne⟩ := hx
    have hxord : orderOf x = q := by
      have h_ord_dvd : orderOf (⟨x, hxQ⟩ : (Q : Subgroup G)) ∣ Nat.card (Q : Subgroup G) :=
        orderOf_dvd_natCard _
      rw [hcard_Sq Q] at h_ord_dvd
      have h_ord_x : orderOf x ∣ q := by
        rw [Subgroup.orderOf_mk] at h_ord_dvd; exact h_ord_dvd
      rcases (Nat.dvd_prime hqprime).mp h_ord_x with h1 | hq
      · exact absurd (orderOf_eq_one_iff.mp h1) hx_ne
      · exact hq
    have hx_notUp : x ∉ Up := by
      intro h
      simp only [Up, Finset.mem_biUnion, Finset.mem_univ, true_and,
                 Finset.mem_sdiff, Set.mem_toFinset, Finset.mem_singleton] at h
      obtain ⟨R, hxR, _⟩ := h
      have h_ord_dvd : orderOf (⟨x, hxR⟩ : (R : Subgroup G)) ∣ Nat.card (R : Subgroup G) :=
        orderOf_dvd_natCard _
      rw [hcard_Sp R] at h_ord_dvd
      have h_ord_xp : orderOf x ∣ p ^ a := by
        rw [Subgroup.orderOf_mk] at h_ord_dvd; exact h_ord_dvd
      rw [hxord] at h_ord_xp
      have hq_dvd_p : q ∣ p := hqprime.dvd_of_dvd_pow h_ord_xp
      have hq_eq_p : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hpprime).mp hq_dvd_p
      exact hpq hq_eq_p.symm
    change x ∈ ((Finset.univ : Finset G) \ Up) \ ({1} : Finset G)
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx_notUp⟩, ?_⟩
    simp [hx_ne]
  -- n_q * (q-1) ≤ q-1 ⇒ n_q ≤ 1.
  have hSq_le : Fintype.card (Sylow q G) * (q - 1) ≤ q - 1 := by
    rw [← hcard_Sq_nonid, ← hcard_Vq]
    exact Finset.card_le_card hSq_sub_Vq
  have hSq_eq_one : Fintype.card (Sylow q G) = 1 := by
    have hq_minus_one_pos : 0 < q - 1 := by omega
    have hSq_pos : 1 ≤ Fintype.card (Sylow q G) := Fintype.card_pos
    by_contra h
    have h2le : 2 ≤ Fintype.card (Sylow q G) := by omega
    have : 2 * (q - 1) ≤ Fintype.card (Sylow q G) * (q - 1) :=
      Nat.mul_le_mul_right _ h2le
    omega
  haveI : Subsingleton (Sylow q G) :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  obtain ⟨Q⟩ := Sylow.nonempty (p := q) (G := G)
  exact ⟨Q, Sylow.normal_of_subsingleton Q⟩

/-- `D ≠ ⊥` 部分 case of Thm 1.36: `|G| = p^a q` (p, q 異素数, a ≥ 1),
`n_p = q`, `(S, T)` を `|S ⊓ T|` 最大の Sylow `p` ペア (`S ≠ T`) として固定し,
`D := S ⊓ T ≠ ⊥` のとき `opCore p G ≠ ⊥`.

Isaacs proof (p.34): `N := N_G(D)` とおく.  S は p-群 ⇒ 冪零 (Thm 1.22),
`D < S` から S 内 normalizer condition で `(S ⊓ N) > D`. 同様 `(T ⊓ N) > D`.
これより `N` は p-群でない (もし `N ≤ R ∈ Sylow p` だと `R ⊓ S ⊇ N ⊓ S > D` で
`hmax` から `R = S`, 同様 `R = T`, しかし `S ≠ T` で矛盾).  よって `q ∣ |N|`,
Cauchy で位数 `q` の `y ∈ N` あり `Q := zpowers y`, `|Q| = q`.
`Disjoint S Q` (gcd(p^a, q) = 1), `|S| · |Q| = |G|` で `S, Q` は complement.
任意の Sylow `p` `R` は Sylow C で `R = g • S`; `g = s · z` (`s ∈ S, z ∈ Q`) と書け
`R = (sz) • S = z • S` (S 自己正規化).  `z ∈ Q ⊆ N` で `D = z • D ⊆ z • S = R`.
∀ Sylow R で `D ≤ R` ゆえ `D ≤ opCore p G`, `D ≠ ⊥` より `opCore p G ≠ ⊥`. -/
private lemma opCore_ne_bot_of_card_eq_pa_q_of_max_inter_ne_bot
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {a : ℕ} (ha : 1 ≤ a)
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ a * q)
    (_hnpq : Nat.card (Sylow p G) = q)
    (hcard_Sp : ∀ R : Sylow p G, Nat.card (R : Subgroup G) = p ^ a)
    {S T : Sylow p G} (hST : S ≠ T)
    (hmax : ∀ R₁ R₂ : Sylow p G, R₁ ≠ R₂ →
      Nat.card (((R₁ : Subgroup G) ⊓ (R₂ : Subgroup G) : Subgroup G)) ≤
      Nat.card (((S : Subgroup G) ⊓ (T : Subgroup G) : Subgroup G)))
    (hD_ne : ((S : Subgroup G) ⊓ (T : Subgroup G) : Subgroup G) ≠ ⊥) :
    opCore p G ≠ ⊥ := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (Sylow p G) := Fintype.ofFinite _
  have hpprime := Fact.out (p := p.Prime)
  have hqprime := Fact.out (p := q.Prime)
  have hp_pos := hpprime.pos
  have hq_pos := hqprime.pos
  have hpa_pos : 0 < p ^ a := pow_pos hp_pos a
  -- Notation.
  set Ssub : Subgroup G := (S : Subgroup G) with hSsubDef
  set Tsub : Subgroup G := (T : Subgroup G) with hTsubDef
  set D : Subgroup G := Ssub ⊓ Tsub with hDdef
  -- Sub-cards.
  have hScard : Nat.card Ssub = p ^ a := hcard_Sp S
  have hTcard : Nat.card Tsub = p ^ a := hcard_Sp T
  have hD_le_S : D ≤ Ssub := inf_le_left
  have hD_le_T : D ≤ Tsub := inf_le_right
  -- D ≠ S (else S ≤ T and same card ⇒ S = T, contra).
  have hD_ne_S : D ≠ Ssub := by
    intro h
    apply hST; apply Sylow.ext
    -- h : D = Ssub, and D = Ssub ⊓ Tsub.  So Ssub = Ssub ⊓ Tsub, giving Ssub ≤ Tsub.
    have hS_le_T : Ssub ≤ Tsub := by
      conv_lhs => rw [← h, hDdef]
      exact inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hS_le_T (by rw [hScard, hTcard])
  have hD_ne_T : D ≠ Tsub := by
    intro h
    apply hST; apply Sylow.ext
    have hT_le_S : Tsub ≤ Ssub := by
      conv_lhs => rw [← h, hDdef]
      exact inf_le_left
    refine (Subgroup.eq_of_le_of_card_ge hT_le_S
      (by rw [hScard, hTcard])).symm
  have hD_lt_S : D < Ssub := lt_of_le_of_ne hD_le_S hD_ne_S
  have hD_lt_T : D < Tsub := lt_of_le_of_ne hD_le_T hD_ne_T
  -- S, T are nilpotent (p-groups).
  haveI hS_nilp : Group.IsNilpotent Ssub := IsPGroup.isNilpotent S.2
  haveI hT_nilp : Group.IsNilpotent Tsub := IsPGroup.isNilpotent T.2
  haveI : Finite Ssub := inferInstance
  haveI : Finite Tsub := inferInstance
  -- D.subgroupOf S < ⊤ in S.
  have hDS_lt_top : D.subgroupOf Ssub < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hD_ne_S
    refine le_antisymm hD_le_S ?_
    intro x hx
    have : (⟨x, hx⟩ : Ssub) ∈ D.subgroupOf Ssub := by rw [h]; trivial
    exact (Subgroup.mem_subgroupOf).mp this
  have hDT_lt_top : D.subgroupOf Tsub < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hD_ne_T
    refine le_antisymm hD_le_T ?_
    intro x hx
    have : (⟨x, hx⟩ : Tsub) ∈ D.subgroupOf Tsub := by rw [h]; trivial
    exact (Subgroup.mem_subgroupOf).mp this
  -- Normalizer condition in S, T.
  have hlt_S := lt_normalizer_of_isNilpotent_of_lt_top (G := Ssub) hDS_lt_top
  have hlt_T := lt_normalizer_of_isNilpotent_of_lt_top (G := Tsub) hDT_lt_top
  -- Set N := N_G(D) at G level.
  set Nd : Subgroup G := Subgroup.normalizer (D : Set G) with hNdDef
  -- Translate via subgroupOf_normalizer_eq: N_S(D.subOf S) = N.subOf S.
  rw [show Subgroup.normalizer (D.subgroupOf Ssub) = Nd.subgroupOf Ssub from
      (Subgroup.subgroupOf_normalizer_eq hD_le_S).symm] at hlt_S
  rw [show Subgroup.normalizer (D.subgroupOf Tsub) = Nd.subgroupOf Tsub from
      (Subgroup.subgroupOf_normalizer_eq hD_le_T).symm] at hlt_T
  -- D ≤ Nd : a subgroup normalizes itself.
  have hD_le_Nd : D ≤ Nd := by
    intro d hd
    rw [hNdDef]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact D.mul_mem (D.mul_mem hd hh) (D.inv_mem hd)
    · intro hh
      have : h = d⁻¹ * (d * h * d⁻¹) * d := by group
      rw [this]; exact D.mul_mem (D.mul_mem (D.inv_mem hd) hh) hd
  -- Extract an element x ∈ S, x ∈ Nd, x ∉ D.
  obtain ⟨⟨x, hxS⟩, hxNd_sub, hxD_sub⟩ :
      ∃ y : Ssub, y ∈ Nd.subgroupOf Ssub ∧ y ∉ D.subgroupOf Ssub := by
    obtain ⟨y, hyN, hyD⟩ := SetLike.exists_of_lt hlt_S
    exact ⟨y, hyN, hyD⟩
  have hxNd : x ∈ Nd := (Subgroup.mem_subgroupOf).mp hxNd_sub
  have hxD : x ∉ D := fun hxD =>
    hxD_sub (by rw [Subgroup.mem_subgroupOf]; exact hxD)
  -- Helper: D ≤ subgroup, D ≠ subgroup, finite ⇒ |D| < |subgroup|.
  have card_lt_of_lt :
      ∀ {H : Subgroup G}, D < H → Nat.card D < Nat.card H := by
    intro H hlt
    have hle : Nat.card D ≤ Nat.card H := Nat.le_of_dvd Nat.card_pos
      (Subgroup.card_dvd_of_le hlt.le)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      apply ne_of_lt hlt
      exact Subgroup.eq_of_le_of_card_ge hlt.le h.ge
  -- Step 4: N_G(D) is not a p-group.
  have hN_not_pgroup : ¬ IsPGroup p Nd := by
    intro hN_p
    obtain ⟨R, hNR⟩ := hN_p.exists_le_sylow
    have hxR : x ∈ (R : Subgroup G) := hNR hxNd
    have hD_le_R : D ≤ (R : Subgroup G) := hD_le_Nd.trans hNR
    -- D < R ⊓ S, since x ∈ R ⊓ S but x ∉ D.
    have hD_lt_RS : D < (R : Subgroup G) ⊓ Ssub := by
      rw [lt_iff_le_and_ne]
      refine ⟨le_inf hD_le_R hD_le_S, ?_⟩
      intro heq
      apply hxD
      have : x ∈ (R : Subgroup G) ⊓ Ssub := ⟨hxR, hxS⟩
      rw [← heq] at this; exact this
    -- |R ⊓ S| > |D|; hmax says |R ⊓ S| ≤ |D| if R ≠ S; so R = S.
    have hR_eq_S : R = S := by
      by_contra hne
      have hle : Nat.card ((R : Subgroup G) ⊓ Ssub : Subgroup G) ≤ Nat.card D := hmax R S hne
      exact absurd (lt_of_lt_of_le (card_lt_of_lt hD_lt_RS) hle) (lt_irrefl _)
    -- Symmetric for T.
    obtain ⟨⟨xT, hxTS⟩, hxTN_sub, hxTD_sub⟩ :
        ∃ y : Tsub, y ∈ Nd.subgroupOf Tsub ∧ y ∉ D.subgroupOf Tsub := by
      obtain ⟨y, hyN, hyD⟩ := SetLike.exists_of_lt hlt_T
      exact ⟨y, hyN, hyD⟩
    have hxTN : xT ∈ Nd := (Subgroup.mem_subgroupOf).mp hxTN_sub
    have hxTD : xT ∉ D := fun hxTD' =>
      hxTD_sub (by rw [Subgroup.mem_subgroupOf]; exact hxTD')
    have hxTR : xT ∈ (R : Subgroup G) := hNR hxTN
    have hD_lt_RT : D < (R : Subgroup G) ⊓ Tsub := by
      rw [lt_iff_le_and_ne]
      refine ⟨le_inf hD_le_R hD_le_T, ?_⟩
      intro heq
      apply hxTD
      have : xT ∈ (R : Subgroup G) ⊓ Tsub := ⟨hxTR, hxTS⟩
      rw [← heq] at this; exact this
    have hR_eq_T : R = T := by
      by_contra hne
      have hle : Nat.card ((R : Subgroup G) ⊓ Tsub : Subgroup G) ≤ Nat.card D := hmax R T hne
      exact absurd (lt_of_lt_of_le (card_lt_of_lt hD_lt_RT) hle) (lt_irrefl _)
    exact hST (hR_eq_S.symm.trans hR_eq_T)
  -- Step 5: q ∣ |Nd|.  |Nd| ∣ |G| = p^a q.  Nd not a p-group ⇒ q | |Nd|.
  have hNd_dvd_G : Nat.card Nd ∣ Nat.card G :=
    Subgroup.card_dvd_of_le (le_top : Nd ≤ ⊤) |>.trans (by rw [Subgroup.card_top])
  rw [hcard] at hNd_dvd_G
  -- Decompose |Nd| ∣ p^a q.  Either |Nd| | p^a (so Nd is p-group), or q | |Nd|.
  have hq_dvd_Nd : q ∣ Nat.card Nd := by
    -- |Nd| > 1 since x ∈ Nd, x ∉ D, x might be 1? No, x ∉ D but D ∋ 1.
    have hx_ne_one : x ≠ 1 := fun h => hxD (h ▸ D.one_mem)
    have hNd_card_pos : 0 < Nat.card Nd := Nat.card_pos
    -- |Nd| = p^k * m where gcd(m, p) = 1.  Nd is p-group iff m = 1.
    -- |Nd| ∣ p^a q ⇒ m ∣ q (after dividing out p-power).
    by_contra hq_nd
    apply hN_not_pgroup
    -- IsPGroup p Nd ↔ every element has p-power order.  Equivalent to |Nd| being p-power.
    -- Use: |Nd| ∣ p^a · q and ¬ (q ∣ |Nd|) imply |Nd| ∣ p^a, so Nd is p-group.
    have hcop : Nat.Coprime (Nat.card Nd) q :=
      Nat.coprime_comm.mp (hqprime.coprime_iff_not_dvd.mpr hq_nd)
    have h_dvd_pa : Nat.card Nd ∣ p ^ a :=
      Nat.Coprime.dvd_of_dvd_mul_right hcop hNd_dvd_G
    -- IsPGroup p Nd from |Nd| = p^k.
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hpprime).mp h_dvd_pa
    exact IsPGroup.of_card (n := k) hk
  -- Step 6: Cauchy for q ∣ |Nd|: ∃ y : Nd, orderOf y = q.
  have hq_dvd_Nd' : q ∣ Nat.card Nd := hq_dvd_Nd
  obtain ⟨ysub, hy_ord⟩ := cauchy (G := Nd) hq_dvd_Nd'
  set y : G := (ysub : G) with hy_def
  have hy_orderOf : orderOf y = q := by
    rw [hy_def, Subgroup.orderOf_coe, hy_ord]
  have hy_mem_Nd : y ∈ Nd := ysub.2
  -- Q := zpowers y.  |Q| = orderOf y = q.
  set Q : Subgroup G := Subgroup.zpowers y with hQdef
  have hQ_card : Nat.card Q = q := by
    rw [hQdef, Nat.card_zpowers, hy_orderOf]
  -- Disjoint: S ⊓ Q has order dividing both p^a and q, with gcd 1.
  have hS_Q_disjoint : Disjoint Ssub Q := by
    rw [disjoint_iff]
    apply Subgroup.eq_bot_of_card_eq
    have hSQ_dvd_S : Nat.card (Ssub ⊓ Q : Subgroup G) ∣ Nat.card Ssub :=
      Subgroup.card_dvd_of_le inf_le_left
    have hSQ_dvd_Q : Nat.card (Ssub ⊓ Q : Subgroup G) ∣ Nat.card Q :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hScard] at hSQ_dvd_S
    rw [hQ_card] at hSQ_dvd_Q
    have hcop : Nat.Coprime (p ^ a) q := by
      rw [Nat.coprime_pow_left_iff (by omega : 0 < a)]
      exact (Nat.coprime_primes hpprime hqprime).mpr hpq
    exact Nat.eq_one_of_dvd_coprimes hcop hSQ_dvd_S hSQ_dvd_Q
  -- |S| * |Q| = p^a * q = |G|. So S, Q complement.
  have hSQ_card : Nat.card Ssub * Nat.card Q = Nat.card G := by
    rw [hScard, hQ_card, hcard]
  have hSQ_complement : Subgroup.IsComplement' Ssub Q :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hSQ_card hS_Q_disjoint
  -- For every Sylow p R, ∃ z ∈ Q, R = z • S.
  -- Step: ∀ R : Sylow p G, D ≤ ↑R.
  have hD_le_all : ∀ R : Sylow p G, D ≤ (R : Subgroup G) := by
    intro R
    -- Sylow C: ∃ g, R = g • S.
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S R
    -- g = z * s with z ∈ Q, s ∈ S via complement (Q first by IsComplement'.symm).
    have hQS_complement : Subgroup.IsComplement' Q Ssub := hSQ_complement.symm
    have hbij := hQS_complement
    rw [Subgroup.IsComplement'] at hbij
    obtain ⟨pair, hzs⟩ := hbij.2 g
    set z : G := pair.1.1 with hz_def
    set s : G := pair.2.1 with hs_def
    have hz : z ∈ Q := pair.1.2
    have hs : s ∈ Ssub := pair.2.2
    -- hzs : z * s = g.  R = g • S = (z * s) • S = z • (s • S) = z • S (s ∈ S normalizes S).
    have hR_sub : (R : Subgroup G) = MulAut.conj z • Ssub := by
      have h1 : (R : Subgroup G) = MulAut.conj g • Ssub := by
        rw [← hg]; exact Sylow.coe_subgroup_smul
      have hzs' : z * s = g := hzs
      rw [h1, ← hzs', map_mul, mul_smul, Subgroup.conj_smul_eq_self_of_mem hs]
    -- z ∈ Q ≤ Nd ?  Need: Q ≤ Nd.  zpowers y ≤ Nd iff y ∈ Nd, yes.
    have hQ_le_Nd : Q ≤ Nd := by
      rw [hQdef, Subgroup.zpowers_le]
      exact hy_mem_Nd
    have hz_in_Nd : z ∈ Nd := hQ_le_Nd hz
    -- D = (MulAut.conj z) • D, since z normalizes D.
    have hConjD : MulAut.conj z • D = D := by
      apply le_antisymm
      · intro d hd
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hd
        simp only [MulAut.smul_def, MulAut.conj_apply, ← map_inv, inv_inv] at hd
        -- hd : z⁻¹ * d * z ∈ D.  z ∈ Nd = N_G(D) ⇒ z * (z⁻¹ d z) * z⁻¹ = d ∈ D.
        rw [show (Nd : Subgroup G) = Subgroup.normalizer (D : Set G) from rfl,
            Subgroup.mem_normalizer_iff''] at hz_in_Nd
        exact (hz_in_Nd d).mpr hd
      · intro d hd
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
        simp only [MulAut.smul_def, MulAut.conj_apply, ← map_inv, inv_inv]
        rw [show (Nd : Subgroup G) = Subgroup.normalizer (D : Set G) from rfl,
            Subgroup.mem_normalizer_iff''] at hz_in_Nd
        exact (hz_in_Nd d).mp hd
    -- D ≤ R = z • S follows from D ≤ S (after conjugation by z, which fixes D).
    have hD_eq : D = MulAut.conj z • D := hConjD.symm
    calc D = MulAut.conj z • D := hD_eq
      _ ≤ MulAut.conj z • Ssub := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hD_le_S
      _ = (R : Subgroup G) := hR_sub.symm
  -- D ≤ opCore p G.
  have hD_le_op : D ≤ opCore p G := by
    rw [opCore, le_iInf_iff]
    exact hD_le_all
  -- D ≠ ⊥ ⇒ opCore ≠ ⊥.
  intro hbot
  rw [hbot, le_bot_iff] at hD_le_op
  exact hD_ne hD_le_op

/-- **Isaacs Thm 1.36** (strong form).  有限群 `G` で
`|G| = p^a · q` (p, q 異素数, a ≥ 1) ならば `G` は非自明な真正規部分群を持つ.

証明 (Isaacs p.34): `n_p(G)` を Sylow `p` の個数とする.  Sylow C/III より
`n_p ∣ q` かつ `n_p ≡ 1 (mod p)`.  q は素数なので `n_p ∈ {1, q}`.

(i) `n_p = 1`: Sylow `p` は唯一 ⇒ 正規.  `|G|` を `q` が真に割るから真部分群.
よって `G` 単純なら矛盾.

(ii) `n_p = q`: 各 Sylow `p` は位数 `p^a`.  `|S ⊓ T|` 最大の (S, T) を取る.
* (a) D = ⊥: helper `sylow_q_normal_of_card_eq_pa_q_of_sylow_p_disjoint` で
  Sylow `q` 正規.  Sylow `q` の位数は `q < p^a q = |G|`, 真部分群で矛盾.
* (b) D ≠ ⊥: helper `opCore_ne_bot_of_card_eq_pa_q_of_max_inter_ne_bot` で
  `opCore p G ≠ ⊥`.  `opCore p G ≤ S` で `|S| = p^a < |G|` より `opCore ≠ ⊤`.
  どちらの場合も真部分の正規部分群が存在する. -/
theorem exists_normal_ne_bot_ne_top_of_card_eq_pow_mul_prime
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {a : ℕ} (ha : 1 ≤ a) (hcard : Nat.card G = p ^ a * q) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  classical
  rcases eq_or_ne p q with rfl | hpq
  · -- `p = q`: `|G| = p^(a+1)` with `a + 1 ≥ 2`, so `G` is a `p`-group of order `≥ p²`.
    have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
    have hcard' : Nat.card G = p ^ (a + 1) := by rw [hcard, pow_succ]
    haveI : Nontrivial G := by
      rcases subsingleton_or_nontrivial G with hs | hn
      · exact absurd ((Nat.card_eq_one_iff_unique.mpr ⟨hs, ⟨1⟩⟩).symm.trans hcard')
          (Nat.one_lt_pow (by omega) hp1).ne
      · exact hn
    have hGp : IsPGroup p G := IsPGroup.of_card hcard'
    rcases eq_or_ne (Subgroup.center G) ⊤ with hctop | hcne
    · -- `G` is abelian: a subgroup of order `p` is normal, nontrivial and proper.
      obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) p
        (n := 1) (by rw [hcard']; exact pow_dvd_pow p (by omega))
      haveI : H.Normal := Subgroup.normalizer_eq_top_iff.mp
        (top_le_iff.mp (hctop ▸ Subgroup.center_le_normalizer (H : Set G)))
      refine ⟨H, inferInstance, ?_, ?_⟩
      · intro hbot
        rw [hbot, Subgroup.card_bot, pow_one] at hH
        omega
      · intro htop
        rw [htop, Nat.card_congr (Subgroup.topEquiv (G := G)).toEquiv, hcard'] at hH
        have := Nat.pow_right_injective hp1 hH
        omega
    · -- the centre is a proper nontrivial normal subgroup.
      exact ⟨Subgroup.center G, inferInstance,
        (Subgroup.nontrivial_iff_ne_bot _).mp hGp.center_nontrivial, hcne⟩
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (Sylow p G) := Fintype.ofFinite _
  haveI : Fintype (Sylow q G) := Fintype.ofFinite _
  have hpprime := Fact.out (p := p.Prime)
  have hqprime := Fact.out (p := q.Prime)
  have hp_pos := hpprime.pos
  have hq_pos := hqprime.pos
  have hpa_pos : 0 < p ^ a := pow_pos hp_pos a
  have hpa_one_lt : 1 < p ^ a := by
    calc 1 = p ^ 0 := by simp
      _ < p ^ a := by
        apply pow_lt_pow_right₀ hpprime.one_lt
        omega
  have hpaq_pos : 0 < p ^ a * q := Nat.mul_pos hpa_pos hq_pos
  have hpaq_gt_q : q < p ^ a * q := by
    have h1 : 1 * q < p ^ a * q := by
      exact (Nat.mul_lt_mul_right hq_pos).mpr hpa_one_lt
    rwa [one_mul] at h1
  have hpaq_gt_pa : p ^ a < p ^ a * q := by
    have h1 : p ^ a * 1 < p ^ a * q := by
      exact (Nat.mul_lt_mul_left hpa_pos).mpr hqprime.one_lt
    rwa [mul_one] at h1
  -- |G| > 1.  G is Nontrivial.
  have hG_card_gt_one : 1 < Nat.card G := by rw [hcard]; omega
  have hpq_coprime : Nat.Coprime (p ^ a) q := by
    rw [Nat.coprime_pow_left_iff (by omega : 0 < a)]
    exact (Nat.coprime_primes hpprime hqprime).mpr hpq
  -- Each Sylow p has order p^a.
  have hcard_Sp : ∀ R : Sylow p G, Nat.card (R : Subgroup G) = p ^ a := by
    intro R
    have hmul := R.card_eq_multiplicity (G := G)
    have hpne : p ^ a ≠ 0 := hpa_pos.ne'
    have hqne : q ≠ 0 := hqprime.ne_zero
    rw [hcard, Nat.factorization_mul hpne hqne,
        Nat.Prime.factorization_pow hpprime] at hmul
    simp only [Finsupp.coe_add, Pi.add_apply, hqprime.factorization,
               Finsupp.single_apply, if_neg (Ne.symm hpq)] at hmul
    simpa using hmul
  -- Each Sylow q has order q.
  have hcard_Sq : ∀ R : Sylow q G, Nat.card (R : Subgroup G) = q := by
    intro R
    have hmul := R.card_eq_multiplicity (G := G)
    have hpne : p ^ a ≠ 0 := hpa_pos.ne'
    have hqne : q ≠ 0 := hqprime.ne_zero
    rw [hcard, Nat.factorization_mul hpne hqne,
        Nat.Prime.factorization_pow hpprime] at hmul
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
               if_neg hpq] at hmul
    simpa [hqprime.factorization_self] using hmul
  -- np ∈ {1, q}.  np = 1 case: Sylow p normal, proper since |S| = p^a < |G|.
  -- np ≥ 2 case: np = q, then split D = ⊥ or D ≠ ⊥.
  -- Sylow C/III on np: np | q and np ≡ 1 mod p.
  have hnp_dvd : Nat.card (Sylow p G) ∣ q := by
    -- np * normalizer.index = |G| ?  Use `Sylow.card_dvd`.
    -- Actually np = [G : N_G(S)] ∣ [G : 1] = |G| = p^a q.
    -- And gcd(np, p) = 1 by Sylow's third theorem.
    -- So np ∣ q.
    obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
    have hidx_dvd : (Subgroup.normalizer (P : Set G)).index ∣ Nat.card G :=
      Subgroup.index_dvd_card _
    rw [← P.card_eq_index_normalizer, hcard] at hidx_dvd
    -- np ∣ p^a q, gcd(np, p) = 1 ⇒ np ∣ q.
    have hnp_coprime_p : Nat.Coprime (Nat.card (Sylow p G)) p :=
      Nat.coprime_comm.mp (hpprime.coprime_iff_not_dvd.mpr (not_dvd_card_sylow p G))
    have hnp_coprime : Nat.Coprime (Nat.card (Sylow p G)) (p ^ a) := by
      rw [Nat.coprime_pow_right_iff (by omega : 0 < a)]; exact hnp_coprime_p
    exact Nat.Coprime.dvd_of_dvd_mul_left hnp_coprime hidx_dvd
  have hnp_eq_one_or_q : Nat.card (Sylow p G) = 1 ∨ Nat.card (Sylow p G) = q :=
    (Nat.dvd_prime hqprime).mp hnp_dvd
  rcases hnp_eq_one_or_q with hnp_eq_one | hnp_eq_q
  · -- (i) np = 1: Sylow p is normal and proper.
    haveI : Subsingleton (Sylow p G) :=
      Fintype.card_le_one_iff_subsingleton.mp (by
        rw [← Nat.card_eq_fintype_card]; omega)
    obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
    have hP_normal : (P : Subgroup G).Normal := P.normal_of_subsingleton
    have hP_ne_bot : (P : Subgroup G) ≠ ⊥ := by
      intro hPbot
      have : Nat.card (P : Subgroup G) = 1 := by
        rw [hPbot]; exact Subgroup.card_bot
      rw [hcard_Sp P] at this
      omega
    have hP_ne_top : (P : Subgroup G) ≠ ⊤ := by
      intro hPtop
      have hcardP : Nat.card (P : Subgroup G) = Nat.card G := by
        rw [hPtop, Subgroup.card_top]
      rw [hcard_Sp P, hcard] at hcardP
      have : p ^ a * 1 = p ^ a * q := by rw [mul_one]; exact hcardP
      have : 1 = q := Nat.eq_of_mul_eq_mul_left hpa_pos this
      omega
    exact ⟨P, hP_normal, hP_ne_bot, hP_ne_top⟩
  · -- (ii) np = q.
    -- Sub-case split on D = ⊥ vs D ≠ ⊥.
    by_cases hAllDisj : ∀ S T : Sylow p G, S ≠ T →
        (S : Subgroup G) ⊓ (T : Subgroup G) = ⊥
    · -- D = ⊥ all.  Helper gives Sylow q normal.
      obtain ⟨Q, hQ_normal⟩ := sylow_q_normal_of_card_eq_pa_q_of_sylow_p_disjoint
        ha hpq hcard hnp_eq_q hcard_Sp hcard_Sq hAllDisj
      have hQ_ne_bot : (Q : Subgroup G) ≠ ⊥ := by
        intro hQbot
        have hQ1 : Nat.card (Q : Subgroup G) = 1 := by
          rw [hQbot]; exact Subgroup.card_bot
        rw [hcard_Sq Q] at hQ1
        have : q ≥ 2 := hqprime.two_le
        omega
      have hQ_ne_top : (Q : Subgroup G) ≠ ⊤ := by
        intro hQtop
        have hcardQ : Nat.card (Q : Subgroup G) = Nat.card G := by
          rw [hQtop, Subgroup.card_top]
        rw [hcard_Sq Q, hcard] at hcardQ
        -- hcardQ : q = p^a * q.  p^a ≥ 2 so contradiction.
        have hpa : p ^ a ≥ 2 := by
          calc p ^ a ≥ p ^ 1 := pow_le_pow_right₀ hpprime.one_lt.le ha
            _ = p := pow_one p
            _ ≥ 2 := hpprime.two_le
        have hqpos : 1 ≤ q := hq_pos
        nlinarith [hcardQ, hpa, hqpos]
      exact ⟨Q, hQ_normal, hQ_ne_bot, hQ_ne_top⟩
    · -- D ≠ ⊥ for some (S, T).
      push Not at hAllDisj
      obtain ⟨S, T, hST_ne, hD_ne⟩ := hAllDisj
      -- Take (S', T') maximizing |S' ⊓ T'| over distinct pairs.
      -- We can use Finset.exists_max_image on Finset.univ filtered.
      -- Alternative: take the max over the full univ (S' = T' included), which gives S' = T' since
      -- |S' ⊓ S'| = |S'| = p^a maximizes trivially.  Need to restrict to distinct.
      -- Use distinct-pair set: { (S, T) : S ≠ T } : nonempty.
      let distinctPairs : Finset (Sylow p G × Sylow p G) :=
        Finset.univ.filter (fun ST => ST.1 ≠ ST.2)
      have h_nonempty : distinctPairs.Nonempty :=
        ⟨(S, T), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hST_ne⟩⟩
      obtain ⟨ST_max, hST_max_mem, hST_max⟩ :=
        distinctPairs.exists_max_image
          (fun ST => Nat.card ((ST.1 : Subgroup G) ⊓ (ST.2 : Subgroup G) : Subgroup G))
          h_nonempty
      obtain ⟨S', T'⟩ := ST_max
      have hST'_ne : S' ≠ T' := (Finset.mem_filter.mp hST_max_mem).2
      -- hmax: ∀ distinct pair, ≤ |S' ⊓ T'|.
      have hmax : ∀ R₁ R₂ : Sylow p G, R₁ ≠ R₂ →
          Nat.card (((R₁ : Subgroup G) ⊓ (R₂ : Subgroup G) : Subgroup G)) ≤
          Nat.card (((S' : Subgroup G) ⊓ (T' : Subgroup G) : Subgroup G)) := by
        intro R₁ R₂ hR
        exact hST_max (R₁, R₂) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR⟩)
      -- |S' ⊓ T'| ≥ |S ⊓ T|, and we know |S ⊓ T| > 0 since it's ≠ ⊥, so |S' ⊓ T'| ≥ |S ⊓ T| > 1.
      have hST_card_ge : Nat.card (((S : Subgroup G) ⊓ (T : Subgroup G) : Subgroup G)) ≤
          Nat.card (((S' : Subgroup G) ⊓ (T' : Subgroup G) : Subgroup G)) :=
        hmax S T hST_ne
      have hD'_ne : ((S' : Subgroup G) ⊓ (T' : Subgroup G) : Subgroup G) ≠ ⊥ := by
        intro hbot
        apply hD_ne
        rw [Subgroup.eq_bot_iff_card]
        rw [hbot, Subgroup.card_bot] at hST_card_ge
        rw [show Nat.card (((S : Subgroup G) ⊓ (T : Subgroup G) : Subgroup G)) = 1
          from le_antisymm hST_card_ge (Nat.card_pos)]
      -- Apply helper: opCore p G ≠ ⊥.
      have hopCore_ne : opCore p G ≠ ⊥ :=
        opCore_ne_bot_of_card_eq_pa_q_of_max_inter_ne_bot
          ha hpq hcard hnp_eq_q hcard_Sp hST'_ne hmax hD'_ne
      -- opCore p G ≤ S' for any S' Sylow, so |opCore| ≤ p^a < |G|, hence ≠ ⊤.
      have hopCore_normal : (opCore p G).Normal := opCore.normal p G
      have hopCore_ne_top : opCore p G ≠ ⊤ := by
        intro htop
        have hop_le : opCore p G ≤ (S' : Subgroup G) := opCore_le S'
        rw [htop] at hop_le
        have htop_le_S' : (⊤ : Subgroup G) ≤ (S' : Subgroup G) := hop_le
        have h_top_S' : (S' : Subgroup G) = ⊤ := top_le_iff.mp htop_le_S'
        have hcardS' : Nat.card (S' : Subgroup G) = Nat.card G := by
          rw [h_top_S', Subgroup.card_top]
        rw [hcard_Sp S', hcard] at hcardS'
        have : p ^ a * 1 = p ^ a * q := by rw [mul_one]; exact hcardS'
        have hone_eq_q : 1 = q := Nat.eq_of_mul_eq_mul_left hpa_pos this
        omega
      exact ⟨opCore p G, hopCore_normal, hopCore_ne, hopCore_ne_top⟩

/-- **Isaacs Thm 1.36**.  有限群 `G` で `|G| = p^a · q` (p, q 異素数, a ≥ 1) ならば
`G` は単純でない. -/
theorem not_isSimpleGroup_of_card_eq_pow_mul_prime
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {a : ℕ} (ha : 1 ≤ a) (hcard : Nat.card G = p ^ a * q) :
    ¬ IsSimpleGroup G := by
  intro h_simple
  obtain ⟨N, hN_normal, hN_ne_bot, hN_ne_top⟩ :=
    exists_normal_ne_bot_ne_top_of_card_eq_pow_mul_prime ha hcard
  haveI : IsSimpleGroup G := h_simple
  rcases hN_normal.eq_bot_or_eq_top with hbot | htop
  · exact hN_ne_bot hbot
  · exact hN_ne_top htop

/-- **Isaacs Lemma 1.34**.  `G` が有限集合 `Ω` に作用し, ある元 `x ∈ G` が
`Ω` 上で奇置換 (`Equiv.Perm.sign = -1`) を引き起こすなら, `G` は指数 2 の
正規部分群を持つ.

形式化方針: 符号写像 `Equiv.Perm.sign : Perm Ω →* ℤˣ` と作用準同型
`MulAction.toPermHom G Ω : G →* Perm Ω` の合成の核を取る.  核は常に正規,
range は `1` (= 単位) と `-1` (= `x` の像) を含むので `ℤˣ = ⊤` 全体,
よって `MonoidHom.index_ker` から index = `|ℤˣ| = 2`. -/
theorem normalSubgroup_index_two_of_actsOddly
    {Ω : Type*} [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]
    {x : G} (hx : Equiv.Perm.sign (MulAction.toPermHom G Ω x) = -1) :
    ∃ H : Subgroup G, H.Normal ∧ H.index = 2 := by
  set signHom : G →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom G Ω) with hdef
  refine ⟨signHom.ker, inferInstance, ?_⟩
  have hxsign : signHom x = -1 := hx
  have hrange : signHom.range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rcases Int.units_eq_one_or y with rfl | rfl
    · exact ⟨1, map_one signHom⟩
    · exact ⟨x, hxsign⟩
  rw [Subgroup.index_ker, hrange]
  simp [Nat.card_eq_fintype_card]

/-- **Isaacs Thm 1.35**.  有限群 `G` で `|G| = 2n`, `n` が奇数なら `G` は指数 2 の
正規部分群を持つ.

証明 (Isaacs 1.35): Cauchy の定理で `t ∈ G`, `orderOf t = 2` を取り,
正則作用 (左乗法) で `σ_t : g ↦ t * g` を考える.  `t ≠ 1` だから `σ_t` は固定点無し,
`t² = 1` だから involution.  mathlib `Equiv.Perm.sign_of_pow_two_eq_one` より
`sign σ_t = (-1)^(|G|/2) = (-1)^n = -1` (n 奇).  Lemma 1.34 で完了.

Feit-Thompson 「奇数位数群は可解」の "p = 2 の最易特殊 case" にあたる. -/
theorem normalSubgroup_index_two_of_card_two_mul_odd
    [Fintype G] {n : ℕ}
    (hn : Odd n) (hcard : Fintype.card G = 2 * n) :
    ∃ H : Subgroup G, H.Normal ∧ H.index = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card G := by
    rw [Nat.card_eq_fintype_card, hcard]; exact ⟨n, rfl⟩
  obtain ⟨t, ht⟩ := cauchy (G := G) hdvd
  refine normalSubgroup_index_two_of_actsOddly (Ω := G) (x := t) ?_
  -- σ_t は involution: t² = 1
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hσ2 : (MulAction.toPermHom G G t) ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  -- σ_t は固定点無し: t * g = g ⇒ t = 1, しかし orderOf t = 2 で矛盾
  have ht_ne_one : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact (by norm_num : (1 : ℕ) ≠ 2) ht
  have hfix : Fintype.card (Function.fixedPoints (MulAction.toPermHom G G t)) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨g, hg⟩ => ?_⟩
    simp only [Function.mem_fixedPoints_iff, MulAction.toPermHom_apply,
               MulAction.toPerm_apply, smul_eq_mul] at hg
    -- hg : t * g = g  ⇒  t = 1
    exact ht_ne_one (mul_right_cancel (hg.trans (one_mul g).symm))
  rw [Equiv.Perm.sign_of_pow_two_eq_one hσ2, hfix, Nat.sub_zero, hcard,
      Nat.mul_div_cancel_left n (by norm_num : (0 : ℕ) < 2)]
  exact hn.neg_one_pow

end -- 1E

section /- 1F: Brodkey's theorem on abelian Sylow (pp. 37-38) -/

open Pointwise Subgroup MulAction

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

/-- **Isaacs Thm 1.38** (Generalized Brodkey).  有限群 `G` で `S, T ∈ Syl_p(G)` が
`Nat.card (↑S ⊓ ↑T)` を最小化するならば, `D = S ∩ T` の `S` と `T` 両方で正規な
任意の部分群 `K` は `opCore p G = O_p(G)` に含まれる.

正規性は「`S, T` が `K` を正規化する」(`↑S ≤ N_G(K)`, `↑T ≤ N_G(K)`) という形で
与える.  これにより `O_p(G)` が `D` 内の「`S` でも `T` でも正規な最大部分群」
であることを示せる (`opCore_le` で逆向きは自明).

証明 (Isaacs p.38): 任意の Sylow `P : Sylow p G` に対し `K ≤ ↑P` を示せば
`mem_opCore` で結論.  `N := normalizer K` とおくと `S, T ≤ N`.
`(P ⊓ N).subgroupOf N` は `N` の `p`-部分群なので Sylow D で
`(P ⊓ N).subgroupOf N ≤ Q` となる `Q : Sylow p N` 取り, Sylow C in N で
`n : N` あって `n • S.subtype = Q`.  これを `G` に戻すと
`P ⊓ N ≤ (n : G) • ↑S`.  `T ≤ N`, `n ∈ N` から `(n : G) • T ≤ N`, よって
`P ⊓ (n • T) ⊆ P ⊓ N ⊆ n • ↑S`, 一方 `P ⊓ (n • T) ⊆ n • T` 自明,
合わせて `P ⊓ (n • T) ⊆ n • D`.  `n⁻¹ • ` で `n⁻¹ • P ⊓ T ⊆ D`.
最小性で等号: `n⁻¹ • P ⊓ T = D`, 特に `D ≤ n⁻¹ • P`, つまり `n • D ≤ P`.
`n ∈ N = N_G(K)`, `K ≤ D` から `K = n • K ≤ n • D ≤ P`.

⚠ **`hmin` は書籍どおり「包含**極小**」** (2026-07-19 に一般化)。以前は「全 Sylow 対の
交わりの中で位数**最小**」を要求していたが、Isaacs の statement は「`D = S ∩ T` is minimal
in the set of intersections of two Sylow p-subgroups」であり、**Isaacs 自身が p.61
(Thm 2.18 の注) で両者を区別している**: 「minimal member … means that no member of the set
is properly contained in M. Of course, if M is chosen to have minimal order … then M will
necessarily be minimal in this sense, **but not conversely**」。
よって位数最小版は包含極小版より真に狭く、包含極小だが位数最小でない対を渡せなかった。
証明側では `hmin` は 1 箇所 (Step 8) でしか使われず、そこは
`Subgroup.eq_of_le_of_card_ge` で等号を出していただけなので、包含極小形は**直接適用**になる。
repo 内の唯一の caller (Thm 1.37) は位数最小の対を作るので、そこで弱形へ落として渡す。
なお Ch.2 の Zenkov (2.18) は元から**正しく包含極小**を使っている。 -/
theorem opCore_eq_inf_of_minimal_sylow_inter
    [Finite G]
    (S T : Sylow p G)
    (hmin : ∀ S' T' : Sylow p G,
        (S' : Subgroup G) ⊓ (T' : Subgroup G) ≤ (S : Subgroup G) ⊓ (T : Subgroup G) →
        (S' : Subgroup G) ⊓ (T' : Subgroup G) = (S : Subgroup G) ⊓ (T : Subgroup G))
    {K : Subgroup G} (hKD : K ≤ (S : Subgroup G) ⊓ (T : Subgroup G))
    (hSN : (S : Subgroup G) ≤ normalizer K) (hTN : (T : Subgroup G) ≤ normalizer K) :
    K ≤ opCore p G := by
  classical
  set N : Subgroup G := normalizer K with hNdef
  set D : Subgroup G := (S : Subgroup G) ⊓ (T : Subgroup G) with hDdef
  have hD_le_N : D ≤ N := inf_le_left.trans hSN
  intro k hk
  refine (mem_opCore (G := G)).mpr (fun P => ?_)
  -- Step 1: ((↑P ⊓ N).subgroupOf N) is a p-subgroup of N.
  -- Via the iso (↑P ⊓ N).subgroupOf N ≃* (↑P ⊓ N), and (↑P ⊓ N) is a p-group (sub of ↑P).
  have hPN_pgroup : IsPGroup p (((P : Subgroup G) ⊓ N).subgroupOf N) := by
    have hPN_pgroup_G : IsPGroup p ((P : Subgroup G) ⊓ N : Subgroup G) := P.2.to_inf_left
    exact hPN_pgroup_G.of_injective
      (Subgroup.subgroupOfEquivOfLe (G := G) (H := (P : Subgroup G) ⊓ N) (K := N)
        inf_le_right).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (G := G) (H := (P : Subgroup G) ⊓ N) (K := N)
        inf_le_right).injective
  -- Step 2: Sylow D in N.
  obtain ⟨Q, hPNQ⟩ := hPN_pgroup.exists_le_sylow
  -- Step 3: Sylow C in N: n • S.subtype hSN = Q.
  haveI : Finite (Sylow p N) := inferInstance
  obtain ⟨n, hnSQ⟩ := MulAction.exists_smul_eq N (S.subtype hSN) Q
  -- Step 4: pull back: P ⊓ N ≤ MulAut.conj (n : G) • ↑S.
  have hPN_in_nS : (P : Subgroup G) ⊓ N ≤ MulAut.conj (n : G) • (S : Subgroup G) := by
    intro g hg
    obtain ⟨hgP, hgN⟩ := hg
    have hg_inSub : (⟨g, hgN⟩ : N) ∈ ((P : Subgroup G) ⊓ N).subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]; exact ⟨hgP, hgN⟩
    have hg_inQ : (⟨g, hgN⟩ : N) ∈ Q := hPNQ hg_inSub
    rw [← hnSQ] at hg_inQ
    -- hg_inQ : ⟨g, hgN⟩ ∈ (n • S.subtype hSN : Sylow p N).
    -- Membership in a Sylow ≡ membership in its underlying Subgroup; unfold then.
    have hg_inQ' : (⟨g, hgN⟩ : N) ∈
        (((n : N) • S.subtype hSN : Sylow p N) : Subgroup N) := hg_inQ
    rw [show (((n : N) • S.subtype hSN : Sylow p N) : Subgroup N) =
        MulAut.conj (n : N) • (S.subtype hSN : Subgroup N) from
        Sylow.coe_subgroup_smul] at hg_inQ'
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hg_inQ'
    -- hg_inQ : (MulAut.conj (n : N))⁻¹ • ⟨g, hgN⟩ ∈ S.subtype hSN
    -- This means ((n : N)⁻¹ * ⟨g, hgN⟩ * (n : N)) ∈ S.subtype hSN.
    -- Project to G: (n : G)⁻¹ * g * (n : G) ∈ S.
    have hgS : ((n : G)⁻¹ * g * (n : G)) ∈ (S : Subgroup G) := by
      have hN_val : (((MulAut.conj (n : N))⁻¹ • ⟨g, hgN⟩ : N) : G) =
          (n : G)⁻¹ * g * (n : G) := by
        simp [MulAut.smul_def]
      -- hg_inQ as membership in subtype: (... : N) ∈ S.subtype hSN.
      -- Use Sylow.coe_subtype: S.subtype hSN.toSubgroup = (↑S).subgroupOf N
      have hin_subOf : ((MulAut.conj (n : N))⁻¹ • ⟨g, hgN⟩ : N) ∈
          (S : Subgroup G).subgroupOf N := by
        rw [← Sylow.coe_subtype]
        exact hg_inQ'
      rw [Subgroup.mem_subgroupOf] at hin_subOf
      rwa [hN_val] at hin_subOf
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
    exact hgS
  -- Step 5: T ≤ N and (n : G) ∈ N, so MulAut.conj (n : G) • ↑T ≤ N.
  have hnT_le_N : MulAut.conj (n : G) • (T : Subgroup G) ≤ N := by
    have hn_in_N : (n : G) ∈ N := n.2
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    simp only [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv] at hx
    have hConjN : (n : G)⁻¹ * x * (n : G) ∈ N := hTN hx
    have hx_eq : x = (n : G) * ((n : G)⁻¹ * x * (n : G)) * (n : G)⁻¹ := by group
    rw [hx_eq]
    exact N.mul_mem (N.mul_mem hn_in_N hConjN) (N.inv_mem hn_in_N)
  -- Step 6: P ⊓ (MulAut.conj n • T) ≤ MulAut.conj n • D.
  have hPnT_le_nD : (P : Subgroup G) ⊓ (MulAut.conj (n : G) • (T : Subgroup G)) ≤
      MulAut.conj (n : G) • D := by
    rw [hDdef, Subgroup.smul_inf]
    refine le_inf ?_ inf_le_right
    exact (inf_le_inf_left _ hnT_le_N).trans hPN_in_nS
  -- Step 7: conjugate by n⁻¹: (n⁻¹ • P) ⊓ T ≤ D.
  have hnInvP_T_le_D :
      MulAut.conj ((n : G)⁻¹) • (P : Subgroup G) ⊓ (T : Subgroup G) ≤ D := by
    have h1 := Subgroup.pointwise_smul_le_pointwise_smul_iff
      (a := MulAut.conj ((n : G)⁻¹)) |>.mpr hPnT_le_nD
    rw [Subgroup.smul_inf] at h1
    have he1 : MulAut.conj ((n : G)⁻¹) • (MulAut.conj (n : G) • (T : Subgroup G)) =
        (T : Subgroup G) := by
      rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have he2 : MulAut.conj ((n : G)⁻¹) • (MulAut.conj (n : G) • D) = D := by
      rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    rw [he1, he2] at h1
    exact h1
  -- Step 8: define P' := n⁻¹ • P, use minimality of D.
  set P' : Sylow p G := (n : G)⁻¹ • P with hP'def
  have hP'_coe : (P' : Subgroup G) = MulAut.conj ((n : G)⁻¹) • (P : Subgroup G) := by
    rw [hP'def]; exact Sylow.coe_subgroup_smul
  have hP'T_le_D : (P' : Subgroup G) ⊓ (T : Subgroup G) ≤ D := by
    rw [hP'_coe]; exact hnInvP_T_le_D
  have hP'T_eq_D : (P' : Subgroup G) ⊓ (T : Subgroup G) = D := hmin P' T hP'T_le_D
  -- Step 9: D ≤ ↑P', so MulAut.conj n • D ≤ ↑P (re-conjugating).
  have hD_le_P' : D ≤ (P' : Subgroup G) := hP'T_eq_D ▸ inf_le_left
  have hnD_le_P : MulAut.conj (n : G) • D ≤ (P : Subgroup G) := by
    have h1 := Subgroup.pointwise_smul_le_pointwise_smul_iff
      (a := MulAut.conj (n : G)) |>.mpr hD_le_P'
    rw [hP'_coe] at h1
    have he : MulAut.conj (n : G) • (MulAut.conj ((n : G)⁻¹) • (P : Subgroup G)) =
        (P : Subgroup G) := by
      rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    rw [he] at h1
    exact h1
  -- Step 10: K = MulAut.conj n • K (n ∈ N_G(K)), K ≤ D, so K ≤ n • D ≤ ↑P.
  have hnK_eq_K : MulAut.conj (n : G) • K = K := by
    have hn_in_N : (n : G) ∈ normalizer (K : Set G) := by
      change (n : G) ∈ N
      exact n.2
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
      simp only [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv] at hx
      rw [mem_normalizer_iff''] at hn_in_N
      exact (hn_in_N x).mpr hx
    · intro x hx
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp only [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
      rw [mem_normalizer_iff''] at hn_in_N
      exact (hn_in_N x).mp hx
  have hK_le_P : K ≤ (P : Subgroup G) := by
    rw [← hnK_eq_K]
    intro x hx
    exact hnD_le_P (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hKD hx)
  exact hK_le_P hk

/-- **Isaacs Thm 1.37** (Brodkey).  有限群 `G` の各 Sylow `p`-部分群が abelian ならば,
ある `S, T ∈ Syl_p(G)` で `↑S ⊓ ↑T = opCore p G`.

`hAbel` は「各 Sylow `p`-部分群の任意の 2 元が可換」という形.
Sylow C で全 Sylow は同型なので 1 つ abelian なら全 abelian.

証明: `Nat.card (↑S ⊓ ↑T)` を最小化するペア `(S, T)` を取り Thm 1.38
(`opCore_eq_inf_of_minimal_sylow_inter`) を `K := ↑S ⊓ ↑T` に適用.
`S, T` が abelian なので `↑S ⊓ ↑T ≤ ↑S` の任意要素は `↑S` (`↑T`) の元と可換,
すなわち `↑S ≤ N_G(↑S ⊓ ↑T)`, `↑T ≤ N_G(↑S ⊓ ↑T)`.  Thm 1.38 で
`↑S ⊓ ↑T ≤ opCore p G`.  逆方向 `opCore p G ≤ ↑S ⊓ ↑T` は `opCore_le`. -/
theorem exists_pair_inf_eq_opCore_of_abelian
    [Finite G]
    (hAbel : ∀ (S : Sylow p G) (x y : G), x ∈ (S : Subgroup G) → y ∈ (S : Subgroup G) →
      Commute x y) :
    ∃ S T : Sylow p G, (S : Subgroup G) ⊓ (T : Subgroup G) = opCore p G := by
  classical
  haveI := Fintype.ofFinite (Sylow p G)
  obtain ⟨ST, _, hmin⟩ :=
    (Finset.univ : Finset (Sylow p G × Sylow p G)).exists_min_image
      (fun ST => Nat.card ((ST.1 : Subgroup G) ⊓ (ST.2 : Subgroup G) : Subgroup G))
      ⟨(default : Sylow p G × Sylow p G), Finset.mem_univ _⟩
  obtain ⟨S, T⟩ := ST
  refine ⟨S, T, ?_⟩
  -- A pair of *minimum order* intersection is in particular *inclusion-minimal*, which is
  -- the (weaker) hypothesis the book's Thm 1.38 actually assumes.
  have hmin' : ∀ S' T' : Sylow p G,
      (S' : Subgroup G) ⊓ (T' : Subgroup G) ≤ (S : Subgroup G) ⊓ (T : Subgroup G) →
      (S' : Subgroup G) ⊓ (T' : Subgroup G) = (S : Subgroup G) ⊓ (T : Subgroup G) :=
    fun S' T' hle =>
      Subgroup.eq_of_le_of_card_ge hle (hmin (S', T') (Finset.mem_univ _))
  refine le_antisymm ?_ (le_inf (opCore_le S) (opCore_le T))
  -- For abelian Sylow R containing D ≤ R: r ∈ R commutes with d ∈ D ≤ R,
  -- so MulAut.conj r fixes D pointwise ⇒ R ≤ N_G(D).
  have hD_normal_in (R : Sylow p G) (hDR : (S : Subgroup G) ⊓ (T : Subgroup G) ≤ R) :
      (R : Subgroup G) ≤
        normalizer (((S : Subgroup G) ⊓ (T : Subgroup G) : Subgroup G) : Set G) := by
    intro r hr
    change ∀ d, d ∈ ((S : Subgroup G) ⊓ (T : Subgroup G)) ↔
        r * d * r⁻¹ ∈ ((S : Subgroup G) ⊓ (T : Subgroup G))
    intro d
    refine ⟨fun hd => ?_, fun hd => ?_⟩
    · -- d ∈ D, r ∈ R, both in abelian R (d ∈ D ≤ R): r d r⁻¹ = d ∈ D.
      have hd_in_R : d ∈ (R : Subgroup G) := hDR hd
      have hcomm : Commute r d := hAbel R r d hr hd_in_R
      have heq : r * d * r⁻¹ = d := by
        rw [Commute, SemiconjBy] at hcomm
        -- hcomm : r * d = d * r
        calc r * d * r⁻¹ = d * r * r⁻¹ := by rw [hcomm]
          _ = d := by rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [heq]; exact hd
    · -- r d r⁻¹ ∈ D ≤ R, so r and (r d r⁻¹) ∈ R commute (R abelian),
      -- so r⁻¹ * (r d r⁻¹) * r = (r d r⁻¹), hence d = r d r⁻¹ ∈ D.
      have hcomm : Commute r (r * d * r⁻¹) := hAbel R r (r * d * r⁻¹) hr (hDR hd)
      have heq : r⁻¹ * (r * d * r⁻¹) * r = r * d * r⁻¹ := by
        rw [Commute, SemiconjBy] at hcomm
        -- hcomm : r * (rdr⁻¹) = (rdr⁻¹) * r
        calc r⁻¹ * (r * d * r⁻¹) * r
            = r⁻¹ * ((r * d * r⁻¹) * r) := by rw [mul_assoc]
          _ = r⁻¹ * (r * (r * d * r⁻¹)) := by rw [hcomm]
          _ = r * d * r⁻¹ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      have hd_eq : d = r⁻¹ * (r * d * r⁻¹) * r := by group
      rw [hd_eq, heq]; exact hd
  refine opCore_eq_inf_of_minimal_sylow_inter S T hmin' (le_refl _)
    (hD_normal_in S inf_le_left) (hD_normal_in T inf_le_right)

/-- **Isaacs Cor 1.39**.  有限群 `G` で各 Sylow `p`-部分群が abelian な場合,
任意の Sylow `P` について `[G : opCore p G] ≤ [G : P]²`.

証明: Brodkey (Thm 1.37) で `S, T` を `↑S ⊓ ↑T = opCore p G` となるよう取る.
`Subgroup.index_inf_le` で `(↑S ⊓ ↑T).index ≤ ↑S.index * ↑T.index`.
Sylow 部分群は全て同型なので `↑S.index = ↑T.index = ↑P.index`. -/
theorem index_opCore_le_index_sylow_sq
    [Finite G]
    (hAbel : ∀ (S : Sylow p G) (x y : G), x ∈ (S : Subgroup G) → y ∈ (S : Subgroup G) →
      Commute x y) (P : Sylow p G) :
    (opCore p G).index ≤ (P : Subgroup G).index ^ 2 := by
  obtain ⟨S, T, hST⟩ := exists_pair_inf_eq_opCore_of_abelian (G := G) (p := p) hAbel
  have hSidx : (S : Subgroup G).index = (P : Subgroup G).index := by
    have h1 : Nat.card (S : Subgroup G) = Nat.card (P : Subgroup G) :=
      Nat.card_congr (Sylow.equiv (G := G) (p := p) S P).toEquiv
    have hS := (S : Subgroup G).card_mul_index
    have hP := (P : Subgroup G).card_mul_index
    have hPpos : 0 < Nat.card (P : Subgroup G) := Nat.card_pos
    rw [← hS, h1] at hP
    exact (Nat.eq_of_mul_eq_mul_left hPpos hP).symm
  have hTidx : (T : Subgroup G).index = (P : Subgroup G).index := by
    have h1 : Nat.card (T : Subgroup G) = Nat.card (P : Subgroup G) :=
      Nat.card_congr (Sylow.equiv (G := G) (p := p) T P).toEquiv
    have hT := (T : Subgroup G).card_mul_index
    have hP := (P : Subgroup G).card_mul_index
    have hPpos : 0 < Nat.card (P : Subgroup G) := Nat.card_pos
    rw [← hT, h1] at hP
    exact (Nat.eq_of_mul_eq_mul_left hPpos hP).symm
  calc (opCore p G).index
      = ((S : Subgroup G) ⊓ (T : Subgroup G)).index := by rw [hST]
    _ ≤ (S : Subgroup G).index * (T : Subgroup G).index := Subgroup.index_inf_le
    _ = (P : Subgroup G).index ^ 2 := by rw [hSidx, hTidx, sq]

/-- **Isaacs Cor 1.40**.  有限群 `G` で各 Sylow `p`-部分群が abelian かつ
`|G| < |P|²` (= `|P| > |G|^{1/2}`) ならば `opCore p G ≠ ⊥`.

証明: Cor 1.39 で `[G : opCore p G] ≤ [G : P]²`. `|G| < |P|²` から
`[G : P]² < |G|`, 一方 `[G : ⊥] = |G|`. もし `opCore p G = ⊥` なら
`|G| = [G : ⊥] ≤ [G : P]² < |G|`, 矛盾. -/
theorem opCore_ne_bot_of_card_sylow_sq_gt
    [Finite G]
    (hAbel : ∀ (S : Sylow p G) (x y : G), x ∈ (S : Subgroup G) → y ∈ (S : Subgroup G) →
      Commute x y) (P : Sylow p G)
    (hcard : Nat.card G < Nat.card (P : Subgroup G) ^ 2) :
    opCore p G ≠ ⊥ := by
  intro h
  have hidx_le := index_opCore_le_index_sylow_sq (G := G) (p := p) hAbel P
  have hP := (P : Subgroup G).card_mul_index
  have hPpos : 0 < Nat.card (P : Subgroup G) := Nat.card_pos
  have hG_pos : 0 < Nat.card G := Nat.card_pos
  have hsq : Nat.card (P : Subgroup G) ^ 2 * (P : Subgroup G).index ^ 2 = Nat.card G ^ 2 := by
    rw [← mul_pow, hP]
  have hPidx_sq : (P : Subgroup G).index ^ 2 < Nat.card G := by
    by_contra hne
    push Not at hne
    have h_mul : Nat.card (P : Subgroup G) ^ 2 * Nat.card G ≤ Nat.card G ^ 2 :=
      calc Nat.card (P : Subgroup G) ^ 2 * Nat.card G
          ≤ Nat.card (P : Subgroup G) ^ 2 * (P : Subgroup G).index ^ 2 :=
            Nat.mul_le_mul_left _ hne
        _ = Nat.card G ^ 2 := hsq
    have hGmul : Nat.card G ^ 2 < Nat.card (P : Subgroup G) ^ 2 * Nat.card G := by
      rw [sq (Nat.card G)]
      rw [show Nat.card (P : Subgroup G) ^ 2 * Nat.card G =
          Nat.card G * Nat.card (P : Subgroup G) ^ 2 from mul_comm _ _]
      exact (Nat.mul_lt_mul_left hG_pos).mpr hcard
    exact (hGmul.trans_le h_mul).false
  rw [h, Subgroup.index_bot] at hidx_le
  exact (hidx_le.trans_lt hPidx_sq).false

end -- 1F

section /- 1G: Chermak–Delgado (pp. 41-44) -/

/-! ### §1G (Chermak-Delgado): 本体は別ファイルに分離.

実装本体は [`OddOrder/GroupTheory/ChermakDelgado.lean`](../GroupTheory/ChermakDelgado.lean).

mathlib upstream 視野の shared module 化 (`OddOrder/GroupTheory/` 慣用 dir).
本 section は import + 主要 API への再 export. 詳細実装計画:
[`notes/meta/ch01_chermak_delgado_plan.md`](../../notes/meta/ch01_chermak_delgado_plan.md).

実装一覧 (定理は `Subgroup` namespace 内):

* **Lemma 1.42**: `chermakDelgadoMeasure_le_centralizer`
* **Lemma 1.43**: `chermakDelgadoMeasure_mul_le`
* **Thm 1.44 (a)**: `chermakDelgadoLattice_inf_mem`, `chermakDelgadoLattice_sup_mem`
* **Thm 1.44 (b)**: `chermakDelgadoLattice_sup_eq_mul`
* **Thm 1.44 (c)**: `chermakDelgadoLattice_centralizer_mem`,
  `chermakDelgadoLattice_centralizer_centralizer_eq`
* **Cor 1.45**: `chermakDelgadoSubgroup_mem_lattice`,
  `chermakDelgadoSubgroup_isMulCommutative`, `center_le_chermakDelgadoSubgroup`,
  `chermakDelgadoSubgroup_characteristic`
* **Thm 1.41**: `chermakDelgado` (main theorem)
* **Cor 1.46**: `not_isSimpleGroup_and_nonabelian_of_chermakDelgadoMeasure_gt`

汎用 helper (mathlib upstream 候補): [`OddOrder/Mathlib/Subgroup.lean`](../Mathlib/Subgroup.lean)
の `card_HK_mul_card_inf_eq_card_mul_card`, `le_centralizer_centralizer`, `centralizer_sup` を使用.

関連項目: §1F Brodkey (Thm 1.37-1.40) は Chermak-Delgado から派生する Cor 1.39 の
abelian Sylow 版で, こちらは本ファイル §1F に実装済 (`exists_pair_inf_eq_opCore_of_abelian`,
`index_opCore_le_index_sylow_sq`). -/

export Subgroup (chermakDelgadoMeasure chermakDelgadoLattice chermakDelgadoSubgroup
  chermakDelgadoMeasure_le_centralizer chermakDelgadoMeasure_mul_le
  chermakDelgadoLattice_inf_mem chermakDelgadoLattice_sup_mem
  chermakDelgadoLattice_sup_eq_mul
  chermakDelgadoLattice_centralizer_mem chermakDelgadoLattice_centralizer_centralizer_eq
  chermakDelgadoSubgroup_mem_lattice
  center_le_chermakDelgadoSubgroup chermakDelgado
  not_isSimpleGroup_and_nonabelian_of_chermakDelgadoMeasure_gt)

end -- 1G

end OddOrder.Isaacs.Ch01

