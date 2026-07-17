/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch02_Subnormality.DihedralBasics
import OddOrder.Isaacs.Ch02_Subnormality.Theorem211Wielandt

/-!
# TAIL

Prefix-split from `OddOrder.Isaacs.Ch02_Subnormality.Main` (2000-line limit, issue 0103 第 2 パス).
-/
open OddOrder.Isaacs.Ch01

namespace OddOrder.Isaacs.Ch02
section /- 2C: p-local subgroups (pp. 58-61) -/
variable {G : Type*} [Group G]


/-! ### Thm 2.15 — Sylow 2 normal from odd p-local hypothesis

書籍 p.60 の証明骨子:
1. **特殊ケース**: `O_2(G) = ⊥` ならば `|G|` は奇数. Matsuyama (Thm 2.13) + Lemma 2.7.
2. **一般ケース**: `N := O_2(G)` の商 `Ḡ = G/N` に Lemma 2.16 で仮定を持ち上げ,
   特殊ケースを `Ḡ` に適用 (`O_2(Ḡ) = ⊥`).

主要補助補題:
* `opCore_quotient_opCore_eq_bot` — `O_p(G/O_p(G)) = ⊥` (汎用, Ch.1 拡張的補助).
* `normal_sylow_image_under_surjective` — surjective hom で `Subgroup` レベル正規 Sylow の
  像も正規 Sylow.
-/

/-- 補助 (Ch.1 拡張): `O_p(G / O_p(G)) = ⊥`.

証明: `K̄ := O_p(G/O_p G)` の preimage `K := comap (mk' O_p G)` を考える.
`K̄` は正規 p-群 ⇒ `K/O_p G ≅ K̄` も p-群, `O_p G` 自身が p-群なので `K` も p-群.
`K ⊴ G` ゆえ `normal_pgroup_le_opCore` で `K ≤ O_p G`. 一方 `O_p G ≤ K` (preimage
で `O_p G = ker f` を含む). よって `K = O_p G`, ゆえ `K̄ = K.map f = ⊥`. -/
private lemma opCore_quotient_opCore_eq_bot {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] :
    opCore p (G ⧸ opCore p G) = ⊥ := by
  set N : Subgroup G := opCore p G with hN_def
  set f : G →* G ⧸ N := QuotientGroup.mk' N with hf_def
  have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective N
  have hf_ker : f.ker = N := QuotientGroup.ker_mk' N
  -- K̄ := opCore p (G/N)
  set Kbar : Subgroup (G ⧸ N) := opCore p (G ⧸ N) with hKbar_def
  -- K := preimage of Kbar
  set K : Subgroup G := Kbar.comap f with hK_def
  have hK_normal : K.Normal := Kbar.normal_comap f
  -- K is a p-group: |K/N| = |Kbar| (p-power), |N| (p-power), so |K| is p-power.
  have hKbar_pgroup : IsPGroup p Kbar := opCore_isPGroup p (G ⧸ N)
  have hN_pgroup : IsPGroup p N := opCore_isPGroup p G
  have hN_le_K : N ≤ K := by
    intro x hx
    have hfx : f x = 1 := by
      have : x ∈ f.ker := by rw [hf_ker]; exact hx
      exact this
    rw [hK_def, Subgroup.mem_comap, hfx]
    exact Subgroup.one_mem _
  have hK_map : K.map f = Kbar := by
    rw [hK_def]; exact Subgroup.map_comap_eq_self_of_surjective hf_surj Kbar
  -- |K| = |K/N| · |N| where K/N ≅ K.map f = Kbar.
  -- We show IsPGroup p K via cardinality.
  have hK_pgroup : IsPGroup p K := by
    -- |K/(N.subgroupOf K)| = |K.map f| = |Kbar| is p-power
    -- |N.subgroupOf K| ≃ N (since N ≤ K), is p-power
    -- So |K| = p-power · p-power = p-power.
    haveI : Finite K := Subtype.finite
    -- Use IsPGroup.of_card after computing |K|.
    have h_quot_card : Nat.card (↥K ⧸ N.subgroupOf K) = Nat.card Kbar := by
      let g : ↥K →* G ⧸ N := f.comp K.subtype
      have hg_range : g.range = K.map f := by
        simp [g, MonoidHom.range_comp, Subgroup.range_subtype]
      have hg_ker : g.ker = N.subgroupOf K := by
        ext x
        constructor
        · intro hx
          have : f (x : G) = 1 := hx
          have hxN : (x : G) ∈ N := by rw [← hf_ker]; exact this
          exact hxN
        · intro hx
          have hxN : (x : G) ∈ N := hx
          have : (x : G) ∈ f.ker := by rw [hf_ker]; exact hxN
          exact this
      have h_iso : (↥K) ⧸ g.ker ≃* ↥g.range :=
        QuotientGroup.quotientKerEquivRange g
      have h_card_eq : Nat.card ((↥K) ⧸ g.ker) = Nat.card ↥g.range :=
        Nat.card_congr h_iso.toEquiv
      rw [hg_ker] at h_card_eq
      rw [h_card_eq, hg_range, hK_map]
    -- |N.subgroupOf K| = |N| because N ≤ K (subgroupOfEquivOfLe).
    have h_sub_card : Nat.card (N.subgroupOf K) = Nat.card N := by
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_le_K).toEquiv
    -- Combine to show IsPGroup p K.
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hKbar_pgroup
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hN_pgroup
    have hK_card : Nat.card K = p ^ (a + b) := by
      have h_mul : Nat.card K = Nat.card (↥K ⧸ N.subgroupOf K) *
          Nat.card (N.subgroupOf K) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup]
      rw [h_mul, h_quot_card, ha, h_sub_card, hb, pow_add]
    exact IsPGroup.of_card hK_card
  -- K ≤ opCore p G = N (normal_pgroup_le_opCore).
  have hK_le_N : K ≤ N := by
    have := normal_pgroup_le_opCore (N := K) hK_pgroup
    rw [hN_def]; exact this
  have hK_eq_N : K = N := le_antisymm hK_le_N hN_le_K
  -- Then Kbar = K.map f = N.map f = ⊥.
  rw [← hK_map, hK_eq_N]
  apply le_bot_iff.mp
  intro y hy
  rcases hy with ⟨z, hz, hzy⟩
  rw [Subgroup.mem_bot, ← hzy]
  have : z ∈ f.ker := by rw [hf_ker]; exact hz
  exact this

/-- 補助: surjective hom `φ : G →* G'` で `S : Sylow p G` が正規ならば,
`(S : Subgroup G).map φ` は `G'` の正規部分群でかつ `Sylow.mapSurjective hφ S` の台.

`Subgroup.Normal.map` と `Sylow.coe_mapSurjective` の組合せ. -/
private lemma normal_sylow_image_of_surjective
    {G' G'' : Type*} [Group G'] [Group G''] [Finite G']
    {p : ℕ} [Fact p.Prime]
    {φ : G' →* G''} (hφ : Function.Surjective φ)
    (S : Sylow p G') (hS_normal : (S : Subgroup G').Normal) :
    ((S : Subgroup G').map φ).Normal :=
  hS_normal.map φ hφ

/-- **特殊ケース**: `O_2(G) = ⊥` のとき, 奇素数 p-local 部分群がすべて正規 Sylow 2 を
持つならば, `|G|` は奇数.

書籍 p.60 の証明:
1. `|G|` が偶数と仮定して矛盾を導く.
2. Cauchy で `t ∈ G, orderOf t = 2`. `t ≠ 1` で `O_2(G) = ⊥` ゆえ `t ∉ O_2(G)`.
3. Matsuyama (Thm 2.13) で奇素数 p の元 x が `t·x·t = x⁻¹` を満たす.
4. `H := N_G(⟨x⟩)` は p-local (`⟨x⟩` 非自明 p-部分群).
5. `t ∈ H` (`t·x·t⁻¹ = t·x·t = x⁻¹ ∈ ⟨x⟩`).
6. 仮定で `H` に正規 Sylow 2 `S` が存在.
7. `⟨t⟩ ⊆ H` は 2-部分群 ⇒ ある Sylow 2 に含まれる ⇒ `S` が唯一 (normal) ⇒ `t ∈ S`.
8. `⟨x⟩, S` ともに `H` で正規, `⟨x⟩` p-群, `S` 2-群 (p 奇) で互いに素 ⇒ disjoint.
9. Lemma 2.7 (`commute_of_disjoint_normal`) で `x, t` 可換.
10. `t·x·t = x` だが `t·x·t = x⁻¹` で `x = x⁻¹`, `orderOf x ∣ 2`, p ≠ 2 で矛盾. -/
private lemma odd_of_opCore_two_eq_bot_aux {G : Type*} [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → Odd p → ∀ H : Subgroup G, IsPLocal p H →
         ∃ S : Sylow 2 H, (S : Subgroup H).Normal)
    (hO2 : opCore 2 G = ⊥) :
    Odd (Nat.card G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- 1. Suppose |G| is even.
  by_contra heven
  rw [Nat.not_odd_iff_even] at heven
  have h_dvd : 2 ∣ Nat.card G := heven.two_dvd
  -- 2. Cauchy: there's t : G with orderOf t = 2.
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨t, ht_ord⟩ : ∃ t : G, orderOf t = 2 := by
    have h_dvd' : 2 ∣ Fintype.card G := by
      rwa [Nat.card_eq_fintype_card] at h_dvd
    exact exists_prime_orderOf_dvd_card 2 h_dvd'
  have ht_sq : t * t = 1 := by
    have h : t ^ 2 = 1 := by
      rw [← ht_ord]
      exact pow_orderOf_eq_one t
    rwa [pow_two] at h
  have ht_ne_one : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht_ord
    omega
  have ht_notin : t ∉ opCore 2 G := by
    rw [hO2, Subgroup.mem_bot]; exact ht_ne_one
  -- 3. Matsuyama: ∃ x, p odd prime, orderOf x = p, t·x·t = x⁻¹.
  obtain ⟨x, p, hp_prime, hp_odd, hx_ord, hxt⟩ := matsuyama ht_sq ht_notin
  -- 4. X := ⟨x⟩ is a non-trivial p-subgroup.
  set X : Subgroup G := Subgroup.zpowers x with hX_def
  haveI hp_fact : Fact p.Prime := ⟨hp_prime⟩
  have hX_pgroup : IsPGroup p X := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx_ord, pow_one]
  have hX_ne_bot : X ≠ ⊥ := by
    intro h
    have hxmem : x ∈ X := Subgroup.mem_zpowers x
    rw [h, Subgroup.mem_bot] at hxmem
    rw [hxmem, orderOf_one] at hx_ord
    exact absurd hx_ord.symm hp_prime.one_lt.ne'
  -- 5. H := N_G(X) is p-local.
  set H : Subgroup G := Subgroup.normalizer (X : Set G) with hH_def
  have hH_pLocal : IsPLocal p H := ⟨X, hX_ne_bot, hX_pgroup, rfl⟩
  -- 6. t ∈ H since t·x·t⁻¹ = x⁻¹ ∈ X (using t = t⁻¹).
  -- t = t⁻¹ since t * t = 1.
  have ht_inv : t⁻¹ = t :=
    (eq_inv_of_mul_eq_one_left ht_sq).symm
  -- t · x · t⁻¹ = x⁻¹ ∈ X.
  have h_conj_x : t * x * t⁻¹ = x⁻¹ := by
    rw [ht_inv]; exact hxt
  have ht_inH : t ∈ H := by
    rw [hH_def, Subgroup.mem_normalizer_iff]
    -- Use the description of X = zpowers x: y ∈ X ↔ ∃ k, x^k = y.
    -- Goal: ∀ y, y ∈ X ↔ t * y * t⁻¹ ∈ X.
    intro y
    -- Use a closed form: conj by t maps each x^k to (x⁻¹)^k via h_conj_x.
    -- Conjugation by t sends x^k to (x⁻¹)^k = x^(-k).
    have h_conj_pow : ∀ (k : ℤ), t * (x ^ k) * t⁻¹ = x ^ (-k) := by
      intro k
      rw [← conj_zpow, h_conj_x, inv_zpow']
    constructor
    · intro hy
      rw [hX_def, Subgroup.mem_zpowers_iff] at hy
      obtain ⟨k, hk⟩ := hy
      rw [← hk, h_conj_pow]
      rw [hX_def]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _
    · intro hy
      -- t * y * t⁻¹ ∈ X, deduce y ∈ X. Use t = t⁻¹.
      -- y = t * (t * y * t⁻¹) * t⁻¹ since t = t⁻¹.
      have hyeq : y = t * (t * y * t⁻¹) * t⁻¹ := by
        calc y = (t * t) * y * (t * t) := by rw [ht_sq, one_mul, mul_one]
          _ = t * (t * y * t) * t := by group
          _ = t * (t * y * t⁻¹) * t⁻¹ := by rw [ht_inv]
      rw [hX_def, Subgroup.mem_zpowers_iff] at hy
      obtain ⟨k, hk⟩ := hy
      rw [hyeq, ← hk, h_conj_pow]
      rw [hX_def]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _
  -- 7. By hypothesis, H has a normal Sylow 2.
  haveI hH_finite : Finite ↥H := Subtype.finite
  obtain ⟨S, hS_normal⟩ := h p hp_prime hp_odd H hH_pLocal
  -- Now show t (lifted to ↥H) lies in S.
  set t_H : ↥H := ⟨t, ht_inH⟩ with ht_H_def
  -- ⟨t_H⟩ is a 2-subgroup of ↥H.
  have ht_H_sq : t_H * t_H = 1 := by
    apply Subtype.ext
    exact ht_sq
  have h_zpowers_pgroup : IsPGroup 2 (Subgroup.zpowers t_H) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    -- orderOf t_H = 2.
    have : orderOf t_H = orderOf t := by
      exact (orderOf_injective H.subtype Subtype.coe_injective t_H).symm
    rw [this, ht_ord]
  -- Get some Sylow Q containing zpowers t_H, then use uniqueness from normality.
  obtain ⟨Q, hQ_le⟩ := h_zpowers_pgroup.exists_le_sylow
  haveI : Subsingleton (Sylow 2 ↥H) := by
    have huniq := Sylow.unique_of_normal S hS_normal
    exact Unique.instSubsingleton
  have hQS : Q = S := Subsingleton.elim Q S
  have ht_H_inS : t_H ∈ (S : Subgroup ↥H) := by
    have : t_H ∈ Q := hQ_le (Subgroup.mem_zpowers t_H)
    rw [hQS] at this
    exact this
  -- 8. X.subgroupOf H is normal in H (since X ⊴ H = normalizer X).
  haveI hX_subOf_H_normal : (X.subgroupOf H).Normal := by
    rw [hH_def]; exact Subgroup.normal_in_normalizer
  have hX_subOf_H_pgroup : IsPGroup p (X.subgroupOf H) :=
    hX_pgroup.comap_of_injective H.subtype Subtype.coe_injective
  -- 9. Disjoint: X.subgroupOf H (p-group) and S (2-group), p ≠ 2.
  have hp_ne_two : p ≠ 2 := by
    intro h2
    rw [h2] at hp_odd
    rcases hp_odd with ⟨k, hk⟩; omega
  have h_disjoint : Disjoint (X.subgroupOf H) (S : Subgroup ↥H) := by
    apply IsPGroup.disjoint_of_ne p 2 hp_ne_two
    · exact hX_subOf_H_pgroup
    · exact S.2
  -- x as element of H. Note x ∈ X ⊆ H (since X ≤ N_G(X) = H).
  have hx_inX : x ∈ X := Subgroup.mem_zpowers x
  have hx_inH : x ∈ H := by
    rw [hH_def]
    exact Subgroup.le_normalizer hx_inX
  set x_H : ↥H := ⟨x, hx_inH⟩ with hx_H_def
  have hx_H_in : x_H ∈ X.subgroupOf H := by
    change (x_H : G) ∈ X
    exact hx_inX
  -- Apply Lemma 2.7.
  have h_commute : Commute x_H t_H :=
    commute_of_disjoint_normal (M := X.subgroupOf H) (N := (S : Subgroup ↥H))
      h_disjoint hx_H_in ht_H_inS
  -- 10. Extract x * t = t * x in G.
  have h_xt : x * t = t * x := by
    -- Commute x_H t_H : x_H * t_H = t_H * x_H
    have hxt_H : x_H * t_H = t_H * x_H := h_commute
    have hxt_val := congrArg (Subtype.val (p := fun y => y ∈ H)) hxt_H
    simpa using hxt_val
  -- Now t * x * t = (t * x) * t = (x * t) * t = x * (t * t) = x. But matsuyama: t * x * t = x⁻¹.
  have h_x_eq : x = x⁻¹ := by
    have h1 : t * x * t = x := by
      rw [show t * x = x * t from h_xt.symm]
      rw [mul_assoc, ht_sq, mul_one]
    exact h1.symm.trans hxt
  -- So orderOf x ∣ 2.
  have hx_sq : x * x = 1 := by
    have : x * x⁻¹ = 1 := mul_inv_cancel x
    rw [← h_x_eq] at this; rw [this]
  have hx_ord_dvd : orderOf x ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx_sq)
  rw [hx_ord] at hx_ord_dvd
  -- p ∣ 2 and p prime ⇒ p = 2; but p odd ⇒ contradiction.
  have hp_eq_two : p = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hx_ord_dvd with h1 | h2
    · exact absurd h1 hp_prime.one_lt.ne'
    · exact h2
  rw [hp_eq_two] at hp_odd
  rcases hp_odd with ⟨k, hk⟩
  omega

/-- 補助: 仮定 (奇素数 p-local の正規 Sylow 2 存在) を商 `G/N` (`N := opCore 2 G`)
に持ち上げる. Lemma 2.16 (`isPLocal_of_quotient`) で `Ḡ` の p-local `Mbar` を
`G` の p-local `L` の像にし, hypothesis から `L` の正規 Sylow 2 を取り,
`Sylow.mapSurjective` で `Ḡ` 上のものへ送る. -/
private lemma transfer_hypothesis_to_quotient {G : Type*} [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → Odd p → ∀ H : Subgroup G, IsPLocal p H →
         ∃ S : Sylow 2 H, (S : Subgroup H).Normal) :
    ∀ p : ℕ, p.Prime → Odd p →
      ∀ Mbar : Subgroup (G ⧸ opCore 2 G), IsPLocal p Mbar →
      ∃ S' : Sylow 2 Mbar, (S' : Subgroup Mbar).Normal := by
  intro p hp_prime hp_odd Mbar hMbar_pLocal
  haveI hp_fact : Fact p.Prime := ⟨hp_prime⟩
  -- Step 1: Lift Mbar to a p-local L of G with L.map f = Mbar.
  obtain ⟨L, hL_pLocal, hL_map⟩ := isPLocal_of_quotient hMbar_pLocal
  -- Step 2: Get normal Sylow 2 of L.
  obtain ⟨S, hS_normal⟩ := h p hp_prime hp_odd L hL_pLocal
  -- Step 3: The image of S in Mbar is a normal Sylow 2.
  -- Restrict f to L: f|_L : L → L.map f = Mbar. This is surjective.
  set f : G →* G ⧸ opCore 2 G := QuotientGroup.mk' (opCore 2 G) with hf_def
  -- The map L → L.map f = Mbar.
  haveI hL_finite : Finite ↥L := Subtype.finite
  set fL : ↥L →* ↥(L.map f) := f.subgroupMap L with hfL_def
  have hfL_surj : Function.Surjective fL := f.subgroupMap_surjective L
  -- Apply Sylow.mapSurjective.
  set S' : Sylow 2 ↥(L.map f) := S.mapSurjective hfL_surj with hS'_def
  -- S' is normal: image of normal under surjective.
  have hS'_normal : (S' : Subgroup ↥(L.map f)).Normal := by
    have h_eq : (S' : Subgroup ↥(L.map f)) = (S : Subgroup ↥L).map fL := by
      rw [hS'_def]; exact Sylow.coe_mapSurjective hfL_surj S
    rw [h_eq]
    exact hS_normal.map fL hfL_surj
  -- Transport to Mbar via equality L.map f = Mbar.
  -- The MulEquiv from ↥(L.map f) to ↥Mbar gives us a Sylow on Mbar.
  let e : ↥(L.map f) ≃* ↥Mbar := MulEquiv.subgroupCongr hL_map
  let eH : ↥(L.map f) →* ↥Mbar := e.toMonoidHom
  have heH_surj : Function.Surjective eH := e.surjective
  -- The image of S' under e.
  set S'' : Sylow 2 ↥Mbar := S'.mapSurjective heH_surj with hS''_def
  refine ⟨S'', ?_⟩
  have h_eq2 : (S'' : Subgroup ↥Mbar) = (S' : Subgroup ↥(L.map f)).map eH := by
    rw [hS''_def]; exact Sylow.coe_mapSurjective heH_surj S'
  rw [h_eq2]
  exact hS'_normal.map eH heH_surj

/-- **Isaacs Thm 2.15**: 有限群 `G` で全ての奇素数 `p` について全ての p-local 部分群が
正規 Sylow 2-部分群を持つならば, `G` 自身が正規 Sylow 2-部分群を持つ.

書籍 p.60 の証明 (Matsuyama Thm 2.13 経由):
1. **特殊ケース**: `O_2(G) = ⊥` ⇒ `|G|` 奇数 (`odd_of_opCore_two_eq_bot_aux`).
   Matsuyama で奇素数位元 `x` (`t·x·t = x⁻¹`) を取り, `N_G(⟨x⟩)` の正規 Sylow 2 から
   `x, t` 可換を導いて `x = x⁻¹` の矛盾.
2. **一般ケース**: `N := O_2(G)` の商 `Ḡ = G/N` に Lemma 2.16 (`isPLocal_of_quotient`)
   で仮定を持ち上げる. `Ḡ` で `O_2(Ḡ) = ⊥` (`opCore_quotient_opCore_eq_bot`) なので
   特殊ケースを適用し `|Ḡ|` 奇数. ゆえ `N` 自身が `G` の Sylow 2 (2-冪 + index 奇). -/
theorem normal_sylow_two_of_odd_pLocal_normal_sylow_two [Finite G]
    (h : ∀ p : ℕ, p.Prime → Odd p → ∀ H : Subgroup G, IsPLocal p H →
         ∃ S : Sylow 2 H, (S : Subgroup H).Normal) :
    ∃ S : Sylow 2 G, (↑S : Subgroup G).Normal := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Set N := opCore 2 G.
  set N : Subgroup G := opCore 2 G with hN_def
  -- Transfer hypothesis to G/N.
  have h_bar := transfer_hypothesis_to_quotient h
  -- Apply special case to G/N: opCore 2 (G/N) = ⊥, so |G/N| is odd.
  have hO2_bar : opCore 2 (G ⧸ N) = ⊥ := opCore_quotient_opCore_eq_bot 2
  have h_odd_bar : Odd (Nat.card (G ⧸ N)) :=
    odd_of_opCore_two_eq_bot_aux h_bar hO2_bar
  -- N is a 2-group.
  have hN_pgroup : IsPGroup 2 N := opCore_isPGroup 2 G
  obtain ⟨k, hN_card⟩ := IsPGroup.iff_card.mp hN_pgroup
  -- |G| = |N| · |G/N| = 2^k · odd. So (Nat.card G).factorization 2 = k.
  have hN_index : N.index = Nat.card (G ⧸ N) := Subgroup.index_eq_card N
  have h_total : Nat.card G = Nat.card N * N.index :=
    (Subgroup.card_mul_index N).symm
  -- 2-part of |G| = 2^k = |N|.
  have h_two_prime : Nat.Prime 2 := Nat.prime_two
  have h_odd_not_dvd : ¬ 2 ∣ Nat.card (G ⧸ N) := fun hdvd =>
    (Nat.not_even_iff_odd.mpr h_odd_bar) ⟨Nat.card (G ⧸ N) / 2, by
      have := hdvd; omega⟩
  have h_odd_ne_zero : Nat.card (G ⧸ N) ≠ 0 := Nat.card_pos.ne'
  have h_card_ne_zero : (2 ^ k : ℕ) ≠ 0 := by positivity
  have h_fact_two : (Nat.card G).factorization 2 = k := by
    rw [h_total, hN_card, hN_index, Nat.factorization_mul h_card_ne_zero h_odd_ne_zero]
    rw [Finsupp.add_apply]
    rw [Nat.Prime.factorization_pow h_two_prime]
    rw [Nat.factorization_eq_zero_of_not_dvd h_odd_not_dvd]
    simp
  -- Construct Sylow.ofCard N with this cardinality info.
  have hN_card_sylow : Nat.card N = 2 ^ (Nat.card G).factorization 2 := by
    rw [h_fact_two, hN_card]
  let S : Sylow 2 G := Sylow.ofCard N hN_card_sylow
  refine ⟨S, ?_⟩
  -- S as Subgroup G is N (= opCore 2 G), which is normal.
  have hS_eq : (S : Subgroup G) = N := Sylow.coe_ofCard N hN_card_sylow
  rw [hS_eq]
  exact opCore.normal 2 G

/-! ### Lemma 2.17 — image of p-local under p'-quotient is p-local

書籍 p.61 の主張: `N ⊴ G`, `p ∤ |N|`, `P` を `G` の非自明 `p`-部分群とすると,
`P̄` は `Ḡ = G/N` で非自明 `p`-部分群で, さらに `N_Ḡ(P̄) = N_G(P)` (商に送ったもの).
帰結: `L` が `p`-local ならば `L̄` も `p`-local.

書籍の証明:
1. `Coprime |P| |N|` (p-冪 vs. p に互いに素) ⇒ `P ⊓ N = ⊥`.
2. `f := mk' N` の核は `N` なので `f|_P` は injective. ゆえ `|P̄| = |P| ≥ p > 1`.
3. `(N_G(P)).map f ≤ N_Ḡ(P̄)`: `Subgroup.le_normalizer_map`.
4. 逆向き `N_Ḡ(P̄) ≤ (N_G(P)).map f`:
   - `M := (N_Ḡ(P̄)).comap f = N_G(P̄.comap f) = N_G(N ⊔ P)` (`comap_normalizer_eq_of_surjective` +
     `comap_map_mk'`).
   - `P` は `P ⊔ N` の Sylow `p`: `[P ⊔ N : P] = [N : P ⊓ N] = [N : ⊥] = |N|` は `p` で割れない.
   - Frattini in `↥M` (`Sylow.normalizer_sup_eq_top`): `(P ⊔ N).subgroupOf M ⊴ ↥M`, `P` は
     その内の Sylow, ゆえ `N_↥M(P) ⊔ (P ⊔ N).subgroupOf M = ⊤`.
   - `G` に持ち上げ `M = N_M(P) · (P ⊔ N) = N_M(P) · N · P ⊆ N_G(P) ⊔ N`.
   - 商に送る: `M̄ ⊆ (N_G(P)).map f ⊔ N.map f = (N_G(P)).map f`.
-/

/-- 補助: `P ⊓ N = ⊥` のとき `f := mk' N` を `P` に制限すると単射 (`f.ker = N` ⇒
`(f|_P).ker = P ⊓ N = ⊥`). -/
private lemma mk'_restrict_injective_of_inf_eq_bot {G : Type*} [Group G] {N : Subgroup G}
    [N.Normal] {P : Subgroup G} (hP_inf_N : P ⊓ N = ⊥) :
    Function.Injective ((QuotientGroup.mk' N).comp P.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx_N : (x : G) ∈ N := by
    have : (x : G) ∈ (QuotientGroup.mk' N).ker := hx
    rw [QuotientGroup.ker_mk'] at this; exact this
  have hx_P : (x : G) ∈ P := x.2
  have hx_inf : (x : G) ∈ P ⊓ N := ⟨hx_P, hx_N⟩
  rw [hP_inf_N, Subgroup.mem_bot] at hx_inf
  exact Subtype.ext hx_inf

/-- 補助: 上の単射性より `|P.map (mk' N)| = |P|`. -/
private lemma card_map_mk'_eq_of_inf_eq_bot {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] {P : Subgroup G} (hP_inf_N : P ⊓ N = ⊥) :
    Nat.card ↥(P.map (QuotientGroup.mk' N)) = Nat.card ↥P := by
  -- f|_P : ↥P → G/N is injective with range = P.map f.
  let g : ↥P →* G ⧸ N := (QuotientGroup.mk' N).comp P.subtype
  have hg_inj : Function.Injective g := mk'_restrict_injective_of_inf_eq_bot hP_inf_N
  have h_range : g.range = P.map (QuotientGroup.mk' N) := by
    simp [g, MonoidHom.range_comp, Subgroup.range_subtype]
  -- ↥P ≃ ↥g.range via MonoidHom.ofInjective.
  have h_equiv : ↥P ≃* ↥g.range := MonoidHom.ofInjective hg_inj
  have : Nat.card ↥g.range = Nat.card ↥P := (Nat.card_congr h_equiv.toEquiv).symm
  rw [← h_range]; exact this

/-- **Isaacs Lemma 2.17, Part 1 (P̄ is nontrivial)**.

`N ⊴ G`, `p ∤ |N|`, `P` が `G` の非自明 `p`-部分群とすると, `P.map (mk' N)` も非自明. -/
theorem map_ne_bot_of_coprime_kernel [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ}
    [Fact p.Prime] (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_neBot : P ≠ ⊥) (hP_pgroup : IsPGroup p P) :
    P.map (QuotientGroup.mk' N) ≠ ⊥ := by
  intro h_bot
  -- Step 1: P ⊓ N = ⊥.
  obtain ⟨k, hP_card⟩ : ∃ k, Nat.card ↥P = p ^ k := IsPGroup.iff_card.mp hP_pgroup
  have hp_prime : p.Prime := Fact.out
  have h_coprime_PN : Nat.Coprime (Nat.card ↥P) (Nat.card ↥N) := by
    rw [hP_card]
    exact Nat.Coprime.pow_left _ (hp_prime.coprime_iff_not_dvd.mpr hp_coprime)
  have hP_inf_N : P ⊓ N = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard h_coprime_PN).eq_bot
  -- Step 2: |P.map f| = |P|.
  have h_card_eq : Nat.card ↥(P.map (QuotientGroup.mk' N)) = Nat.card ↥P :=
    card_map_mk'_eq_of_inf_eq_bot hP_inf_N
  -- Step 3: h_bot ⇒ |P.map f| = 1.
  have h_card_bot : Nat.card ↥(P.map (QuotientGroup.mk' N)) = 1 := by
    rw [h_bot]; exact Subgroup.card_bot
  rw [h_card_bot] at h_card_eq
  -- |P| = 1 ⇒ P = ⊥, contradiction.
  apply hP_neBot
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have h_sub : Subsingleton ↥P := (Nat.card_eq_one_iff_unique.mp h_card_eq.symm).1
  have : (⟨x, hx⟩ : ↥P) = ⟨1, Subgroup.one_mem _⟩ := Subsingleton.elim _ _
  exact Subtype.ext_iff.mp this

set_option maxHeartbeats 1200000 in
-- 長い構成的証明 (Sylow II + Frattini, ↥M 内で構築 + G への持ち上げ) のため heartbeat を増やす.
/-- **Isaacs Lemma 2.17 (image of normalizer under p'-quotient)**.

`N ⊴ G` で `p ∤ |N|`, `P` が `G` の非自明 `p`-部分群とすると, `f := mk' N` について
`N_Ḡ(P.map f) = (N_G(P)).map f`.

書籍 p.61 の Frattini 議論 (`Sylow.normalizer_sup_eq_top` を `(P ⊔ N).subgroupOf M ⊴ ↥M` に適用). -/
theorem normalizer_map_of_coprime_kernel [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ}
    [Fact p.Prime] (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (_hP_neBot : P ≠ ⊥) (hP_pgroup : IsPGroup p P) :
    Subgroup.normalizer ((P.map (QuotientGroup.mk' N)) : Subgroup (G ⧸ N))
      = (Subgroup.normalizer P).map (QuotientGroup.mk' N) := by
  classical
  set f : G →* G ⧸ N := QuotientGroup.mk' N with hf_def
  have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective N
  have hf_ker : f.ker = N := QuotientGroup.ker_mk' N
  -- Step 1: P ⊓ N = ⊥ (coprimality).
  obtain ⟨k, hP_card⟩ : ∃ k, Nat.card ↥P = p ^ k := IsPGroup.iff_card.mp hP_pgroup
  have hp_prime : p.Prime := Fact.out
  have h_coprime_PN : Nat.Coprime (Nat.card ↥P) (Nat.card ↥N) := by
    rw [hP_card]
    exact Nat.Coprime.pow_left _ (hp_prime.coprime_iff_not_dvd.mpr hp_coprime)
  have hP_inf_N : P ⊓ N = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard h_coprime_PN).eq_bot
  -- Names.
  set Pbar : Subgroup (G ⧸ N) := P.map f with hPbar_def
  set Mbar : Subgroup (G ⧸ N) := Subgroup.normalizer (Pbar : Subgroup (G ⧸ N)) with hMbar_def
  set M : Subgroup G := Mbar.comap f with hM_def
  set L : Subgroup G := Subgroup.normalizer P with hL_def
  set U : Subgroup G := P ⊔ N with hU_def
  -- Step 2: M.map f = Mbar (surjectivity).
  have hM_map : M.map f = Mbar :=
    Subgroup.map_comap_eq_self_of_surjective hf_surj _
  -- Step 3: M = N_G(U) where U = P ⊔ N.
  have hPbar_comap : Pbar.comap f = U := by
    rw [hPbar_def, hU_def, hf_def, QuotientGroup.comap_map_mk' N P, sup_comm]
  have hM_eq_norm_U : M = Subgroup.normalizer U := by
    rw [hM_def, hMbar_def]
    rw [Subgroup.comap_normalizer_eq_of_surjective _ hf_surj, hPbar_comap]
  -- Step 4: L ⊆ M (i.e., N_G(P) ⊆ M).
  -- This is Part 2: (N_G(P)).map f ⊆ N_Ḡ(P̄), reformulated using map_le_iff_le_comap.
  have hL_le_M : L ≤ M := by
    rw [hM_def, ← Subgroup.map_le_iff_le_comap]
    -- Show (N_G(P)).map f ≤ Mbar = N_Ḡ(P̄).
    rw [hMbar_def, hPbar_def]
    exact Subgroup.le_normalizer_map f
  -- We need to also show: L.map f = Mbar (this is the main goal, restated).
  -- ⊇: Already L.map f ≤ Mbar via the above. Now ⊆ needs Frattini.
  -- The goal: Mbar = L.map f.
  -- Strategy: Mbar = M.map f. Show M ≤ L ⊔ N, then M.map f ≤ (L ⊔ N).map f = L.map f.
  refine le_antisymm ?_ ?_
  · -- Mbar ≤ L.map f: requires the Frattini argument.
    -- Step 5: Set up the Frattini argument.
    -- (1) U.subgroupOf M ⊴ ↥M (since M = normalizer U).
    haveI hUM_normal : (U.subgroupOf M).Normal := by
      rw [hM_eq_norm_U]; exact Subgroup.normal_in_normalizer
    have hP_le_U : P ≤ U := le_sup_left
    have hN_le_U : N ≤ U := le_sup_right
    have hP_le_L : P ≤ L := by rw [hL_def]; exact Subgroup.le_normalizer
    have hL_le_norm_U : L ≤ Subgroup.normalizer U := by
      -- L normalizes P. L also normalizes N (N ⊴ G). So L normalizes P ⊔ N = U.
      -- This is the same h_preserve trick used in Lemma 2.16.
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      have hx_in_norm : x ∈ Subgroup.normalizer (P : Set G) := hx
      have hx_inv_in_norm : x⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
        Subgroup.inv_mem _ hx
      have h_conj_P : ∀ q ∈ P, x * q * x⁻¹ ∈ P :=
        fun q hq => (Subgroup.mem_normalizer_iff.mp hx_in_norm q).mp hq
      have h_conj_P_inv : ∀ q ∈ P, x⁻¹ * q * (x⁻¹)⁻¹ ∈ P :=
        fun q hq => (Subgroup.mem_normalizer_iff.mp hx_inv_in_norm q).mp hq
      have h_conj_N : ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun n hn =>
        Subgroup.Normal.conj_mem ‹N.Normal› n hn x
      have h_conj_N_inv : ∀ n ∈ N, x⁻¹ * n * (x⁻¹)⁻¹ ∈ N := fun n hn =>
        Subgroup.Normal.conj_mem ‹N.Normal› n hn x⁻¹
      have h_preserve : ∀ (g : G), (∀ q ∈ P, g * q * g⁻¹ ∈ P) →
          (∀ n ∈ N, g * n * g⁻¹ ∈ N) →
          ∀ z ∈ P ⊔ N, g * z * g⁻¹ ∈ P ⊔ N := by
        intro g hgP hgN z hz
        rw [Subgroup.sup_eq_closure] at hz
        induction hz using Subgroup.closure_induction with
        | mem w hw =>
          rcases hw with hwP | hwN
          · exact Subgroup.mem_sup_left (hgP w hwP)
          · exact Subgroup.mem_sup_right (hgN w hwN)
        | one =>
          have h1 : g * 1 * g⁻¹ = 1 := by group
          rw [h1]; exact Subgroup.one_mem _
        | mul a b _ _ ha hb =>
          have h_eq : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
          rw [h_eq]; exact Subgroup.mul_mem _ ha hb
        | inv a _ ha =>
          have h_eq : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
          rw [h_eq]; exact Subgroup.inv_mem _ ha
      intro y
      constructor
      · intro hy
        rw [hU_def] at hy ⊢
        exact h_preserve x h_conj_P h_conj_N y hy
      · intro hy
        rw [hU_def] at hy ⊢
        have h_pre : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ ∈ P ⊔ N :=
          h_preserve x⁻¹ h_conj_P_inv h_conj_N_inv _ hy
        have h_simp : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y := by group
        rwa [h_simp] at h_pre
    -- (2) P is a Sylow p of U = P ⊔ N.
    -- Plan: |U| = |P| · |N| via second iso (P/(P ⊓ N) ≃ U/N).
    --      Then [U:P] = |N|, which is coprime to p.
    have hU_card_eq : Nat.card ↥U = Nat.card ↥P * Nat.card ↥N := by
      rw [hU_def]
      -- (N.subgroupOf P).index = |P| since P ⊓ N = ⊥ (i.e. N.subgroupOf P = ⊥ in ↥P).
      have hNP_eq_bot : N.subgroupOf P = (⊥ : Subgroup ↥P) := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        have hx_N : (x : G) ∈ N := hx
        have hx_P : (x : G) ∈ P := x.2
        have hx_inf : (x : G) ∈ P ⊓ N := ⟨hx_P, hx_N⟩
        rw [hP_inf_N, Subgroup.mem_bot] at hx_inf
        exact Subtype.ext hx_inf
      have hP_quot_card : Nat.card (↥P ⧸ N.subgroupOf P) = Nat.card ↥P := by
        rw [hNP_eq_bot]
        exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
      -- Second iso: P/(N ⊓ P) ≃* (P ⊔ N)/(N.subgroupOf (P ⊔ N)).
      have h_iso := QuotientGroup.quotientInfEquivProdNormalQuotient P N
      have h_quot_eq : Nat.card (↥P ⧸ N.subgroupOf P)
          = Nat.card (↥(P ⊔ N) ⧸ N.subgroupOf (P ⊔ N)) :=
        Nat.card_congr h_iso.toEquiv
      have h_index_eq : (N.subgroupOf (P ⊔ N)).index = Nat.card ↥P := by
        rw [Subgroup.index_eq_card, ← h_quot_eq, hP_quot_card]
      -- |U| · |N.subgroupOf U| = ... no, use: |N| * [U:N] = |U|.
      -- N.subgroupOf U has |↥(N.subgroupOf U)| = |N| (since N ≤ U).
      have hN_subU_card : Nat.card ↥(N.subgroupOf (P ⊔ N)) = Nat.card ↥N := by
        rw [show Nat.card ↥(N.subgroupOf (P ⊔ N)) =
          Nat.card ↥((N.subgroupOf (P ⊔ N)).map (P ⊔ N).subtype) from
          (Subgroup.card_subtype _ _).symm]
        rw [Subgroup.map_subgroupOf_eq_of_le hN_le_U]
      have h_mul : Nat.card ↥(N.subgroupOf (P ⊔ N)) * (N.subgroupOf (P ⊔ N)).index =
          Nat.card ↥(P ⊔ N) := Subgroup.card_mul_index _
      rw [hN_subU_card, h_index_eq] at h_mul
      linarith
    have hP_subU_index : (P.subgroupOf U).index = Nat.card ↥N := by
      have h_mul : Nat.card ↥(P.subgroupOf U) * (P.subgroupOf U).index = Nat.card ↥U :=
        Subgroup.card_mul_index _
      have hP_subU_card : Nat.card ↥(P.subgroupOf U) = Nat.card ↥P := by
        rw [show Nat.card ↥(P.subgroupOf U) =
          Nat.card ↥((P.subgroupOf U).map U.subtype) from
          (Subgroup.card_subtype _ _).symm]
        rw [Subgroup.map_subgroupOf_eq_of_le hP_le_U]
      rw [hP_subU_card, hU_card_eq] at h_mul
      have hP_pos : 0 < Nat.card ↥P := Nat.card_pos
      have hN_pos : 0 < Nat.card ↥N := Nat.card_pos
      -- |P| * idx = |P| * |N|, so idx = |N|.
      exact Nat.eq_of_mul_eq_mul_left hP_pos h_mul
    have hP_subU_not_dvd : ¬ p ∣ (P.subgroupOf U).index := by
      rw [hP_subU_index]; exact hp_coprime
    -- P.subgroupOf U is a p-group (since it is isomorphic to P).
    haveI : Finite ↥U := Subtype.finite
    have hP_subU_pgroup : IsPGroup p ↥(P.subgroupOf U) :=
      hP_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hP_le_U).symm
    let PS : Sylow p ↥U := hP_subU_pgroup.toSylow hP_subU_not_dvd
    have hPS_eq : (PS : Subgroup ↥U) = P.subgroupOf U :=
      hP_subU_pgroup.toSylow_coe hP_subU_not_dvd
    -- (3) Build P_M : Sylow p ↥(U.subgroupOf M) using e := subgroupOfEquivOfLe hU_le_M.
    have hU_le_M : U ≤ M := by rw [hM_eq_norm_U]; exact Subgroup.le_normalizer
    haveI : Finite ↥M := Subtype.finite
    haveI : Finite ↥(U.subgroupOf M) := Subtype.finite
    let e : ↥(U.subgroupOf M) ≃* ↥U := Subgroup.subgroupOfEquivOfLe hU_le_M
    let P_M : Sylow p ↥(U.subgroupOf M) :=
      Sylow.ofCard ((PS : Subgroup ↥U).comap e.toMonoidHom) (by
        rw [show Nat.card ↥(U.subgroupOf M) = Nat.card ↥U from Nat.card_congr e.toEquiv]
        have h_card_eq : Nat.card ↥((PS : Subgroup ↥U).comap e.toMonoidHom) =
            Nat.card (PS : Subgroup ↥U) := by
          refine Nat.card_congr ?_
          exact {
            toFun := fun x => ⟨e x.1, x.2⟩
            invFun := fun y => ⟨e.symm y.1, by
              change e (e.symm y.1) ∈ (PS : Subgroup ↥U)
              rw [MulEquiv.apply_symm_apply]
              exact y.2⟩
            left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
            right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
          }
        rw [h_card_eq, Sylow.card_eq_multiplicity PS])
    -- (4) Apply Sylow.normalizer_sup_eq_top.
    have h_frattini : Subgroup.normalizer (P_M.map (U.subgroupOf M).subtype) ⊔
        U.subgroupOf M = ⊤ :=
      Sylow.normalizer_sup_eq_top P_M
    -- (5) Identify (P_M.map (U.subgroupOf M).subtype).map M.subtype = P.
    have h_PM_map_eq : ((P_M.map (U.subgroupOf M).subtype : Subgroup ↥M).map M.subtype) = P := by
      ext y
      simp only [Subgroup.mem_map, Subgroup.coe_subtype]
      constructor
      · rintro ⟨a, ⟨b, hb, hba⟩, hay⟩
        have hb' : e b ∈ (PS : Subgroup ↥U) := by
          change b ∈ (PS : Subgroup ↥U).comap e.toMonoidHom at hb
          rw [Subgroup.mem_comap] at hb; exact hb
        rw [hPS_eq] at hb'
        -- e b : ↥U, (e b : G) = b.val.val. We want y ∈ P.
        have he_val : ((e b : ↥U) : G) = ((b : ↥(U.subgroupOf M)) : ↥M).1 := rfl
        have hb_subOf : (e b : G) ∈ P := hb'
        have : ((b : ↥(U.subgroupOf M)) : ↥M).1 = (e b : G) := he_val.symm
        rw [← hay, ← hba]
        change ((b : ↥(U.subgroupOf M)) : ↥M).1 ∈ P
        rw [this]; exact hb_subOf
      · rintro hzP
        refine ⟨⟨y, hU_le_M (hP_le_U hzP)⟩, ⟨e.symm ⟨y, hP_le_U hzP⟩, ?_, ?_⟩, rfl⟩
        · change e.symm ⟨y, hP_le_U hzP⟩ ∈ (PS : Subgroup ↥U).comap e.toMonoidHom
          rw [Subgroup.mem_comap]
          simp only [MulEquiv.apply_symm_apply, MulEquiv.coe_toMonoidHom]
          rw [hPS_eq]
          exact hzP
        · rfl
    -- (6) Frattini in G: each m ∈ M decomposes as m = a * b with a ∈ L = N_G(P), b ∈ U.
    have hM_le_L_sup_U : M ≤ L ⊔ U := by
      intro m hm
      have hm_M : (⟨m, hm⟩ : ↥M) ∈ (⊤ : Subgroup ↥M) := trivial
      rw [← h_frattini] at hm_M
      rcases Subgroup.mem_sup_of_normal_right.mp hm_M with ⟨a, ha, b, hb, hab⟩
      have hMb_U : (b : G) ∈ U := by
        change b ∈ U.subgroupOf M at hb
        exact hb
      have hMa_L : (a : G) ∈ L := by
        rw [hL_def, Subgroup.mem_normalizer_iff]
        intro y
        have ha_norm : a ∈ Subgroup.normalizer (P_M.map (U.subgroupOf M).subtype) := ha
        rw [Subgroup.mem_normalizer_iff] at ha_norm
        constructor
        · intro hy
          have hy_U : y ∈ U := hP_le_U hy
          have hy_M : y ∈ M := hU_le_M hy_U
          have hy_PM_map : (⟨y, hy_M⟩ : ↥M) ∈ P_M.map (U.subgroupOf M).subtype := by
            rw [← h_PM_map_eq] at hy
            rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
            have hx_eq : x = ⟨y, hy_M⟩ := Subtype.ext hxy
            rw [hx_eq] at hx; exact hx
          have h_step := (ha_norm ⟨y, hy_M⟩).mp hy_PM_map
          have h_step_G : (a : G) * y * (a : G)⁻¹ ∈ P := by
            rw [← h_PM_map_eq]
            refine ⟨a * ⟨y, hy_M⟩ * a⁻¹, h_step, ?_⟩
            rfl
          exact h_step_G
        · intro hy
          have ha_inv_norm : a⁻¹ ∈ Subgroup.normalizer (P_M.map (U.subgroupOf M).subtype) :=
            (Subgroup.normalizer _).inv_mem ha
          rw [Subgroup.mem_normalizer_iff] at ha_inv_norm
          have hay_U : (a : G) * y * (a : G)⁻¹ ∈ U := hP_le_U hy
          have hy_M : y ∈ M := by
            have : (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * ((a : G)⁻¹)⁻¹ = y := by group
            rw [← this]
            exact M.mul_mem (M.mul_mem (M.inv_mem a.2) (hU_le_M hay_U)) (M.inv_mem (M.inv_mem a.2))
          have hay_PM_map : (⟨(a : G) * y * (a : G)⁻¹, hU_le_M hay_U⟩ : ↥M)
              ∈ P_M.map (U.subgroupOf M).subtype := by
            rw [← h_PM_map_eq] at hy
            rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
            have hx_eq : x = ⟨(a : G) * y * (a : G)⁻¹, hU_le_M hay_U⟩ := Subtype.ext hxy
            rw [hx_eq] at hx; exact hx
          have h_back := (ha_inv_norm ⟨(a : G) * y * (a : G)⁻¹, hU_le_M hay_U⟩).mp hay_PM_map
          have h_back_G : (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * ((a : G)⁻¹)⁻¹ ∈ P := by
            rw [← h_PM_map_eq]
            refine ⟨a⁻¹ * ⟨(a : G) * y * (a : G)⁻¹, hU_le_M hay_U⟩ * (a⁻¹)⁻¹, h_back, ?_⟩
            rfl
          have h_simp : (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * ((a : G)⁻¹)⁻¹ = y := by group
          rwa [h_simp] at h_back_G
      have hm_eq : m = (a : G) * (b : G) := by
        have h := congrArg ((↑) : ↥M → G) hab
        simp at h; exact h.symm
      rw [hm_eq]
      exact (L ⊔ U).mul_mem (Subgroup.mem_sup_left hMa_L) (Subgroup.mem_sup_right hMb_U)
    -- (7) Now M ⊆ L ⊔ U. Map to quotient: Mbar ⊆ (L ⊔ U).map f.
    -- (L ⊔ U).map f = L.map f ⊔ U.map f = L.map f ⊔ (P ⊔ N).map f
    --              = L.map f ⊔ P.map f ⊔ N.map f
    --              = L.map f ⊔ Pbar ⊔ ⊥ = L.map f (since P ≤ L ⇒ Pbar ≤ L.map f).
    rw [← hM_map]
    have h_step1 : M.map f ≤ (L ⊔ U).map f := Subgroup.map_mono hM_le_L_sup_U
    have h_N_map : N.map f = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      rcases hx with ⟨y, hy, hyx⟩
      rw [Subgroup.mem_bot]
      rw [← hyx]
      have : y ∈ f.ker := by rw [hf_ker]; exact hy
      exact this
    have h_step2 : (L ⊔ U).map f = L.map f := by
      rw [hU_def, ← sup_assoc, Subgroup.map_sup, Subgroup.map_sup]
      have h_P_le_L_map : P.map f ≤ L.map f := Subgroup.map_mono hP_le_L
      rw [h_N_map, sup_bot_eq]
      exact sup_eq_left.mpr h_P_le_L_map
    rw [← h_step2]
    exact h_step1
  · -- L.map f ≤ Mbar: this is Part 2.
    rw [hMbar_def, hPbar_def]
    exact Subgroup.le_normalizer_map f

/-- **Isaacs Lemma 2.17 corollary** (image of `p`-local is `p`-local under `p'`-quotient).

`N ⊴ G` で `p ∤ |N|` のとき, `L` が `G` で `p`-local ならば `L.map (mk' N)` は `Ḡ = G/N` で
`p`-local. -/
theorem isPLocal_map_of_coprime_kernel [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ}
    [Fact p.Prime] (hp_coprime : ¬ p ∣ Nat.card N)
    {L : Subgroup G} (hL : IsPLocal p L) :
    IsPLocal p (L.map (QuotientGroup.mk' N)) := by
  obtain ⟨P, hP_neBot, hP_pgroup, hL_eq⟩ := hL
  refine ⟨P.map (QuotientGroup.mk' N), ?_, ?_, ?_⟩
  · exact map_ne_bot_of_coprime_kernel hp_coprime hP_neBot hP_pgroup
  · exact hP_pgroup.map _
  · rw [hL_eq]
    exact (normalizer_map_of_coprime_kernel hp_coprime hP_neBot hP_pgroup).symm

end -- 2C

section /- 2D: Zenkov + Lucchini (pp. 61-64) -/

variable {G : Type*} [Group G]

/-! ### §2D 状態 (2026-05-24 更新)

* **Thm 2.18 Zenkov**: `zenkov_minimal_le_fitting` ✅ unconditional.
* **Cor 2.19**: `inf_fitting_ne_bot_of_abelian_card_ge_index` ✅ unconditional (Zenkov 経由).
* **Thm 2.20 Lucchini**: K > ⊥ structural reduction (`lucchini_K_pos_reduction`) ✅ 本ファイル内.
  full theorem (`lucchini_index_normalCore_lt_index`) は owner chapter 規則で
  `OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh02.lean` に配置. K = ⊥ case のみ
  `lucchini_K_bot_aux` axiom (Ch.4 §4A-§4B lcs 加法性 完成後に theorem 化予定).
* 補助補題 `card_set_mul_card_inf` は §2A 末尾に置く (Thm 2.11 でも使用).
* Zenkov 用 Case 1 補助補題 (`conj_smul_abelian`, `inf_le_center_of_join_eq_top`,
  `center_le_fitting`) を standalone で提供 — Lucchini 完成時に再利用可.
-/

open scoped Pointwise in
/-- 共役で abelian 性は保たれる: `B` abelian なら `(MulAut.conj g) • B` も abelian.

Zenkov Case 1 / Wielandt Case 1 等で頻用. -/
private lemma conj_smul_abelian {G : Type*} [Group G] {B : Subgroup G}
    (hBab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (g : G) :
    ∀ b ∈ ((MulAut.conj g) • B : Subgroup G),
      ∀ b' ∈ ((MulAut.conj g) • B : Subgroup G), b * b' = b' * b := by
  intro b₁ hb₁ b₂ hb₂
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def] at hb₁ hb₂
  have hb₁' : g⁻¹ * b₁ * g ∈ B := by
    have h : g⁻¹ * b₁ * (g⁻¹)⁻¹ ∈ B := hb₁
    rwa [inv_inv] at h
  have hb₂' : g⁻¹ * b₂ * g ∈ B := by
    have h : g⁻¹ * b₂ * (g⁻¹)⁻¹ ∈ B := hb₂
    rwa [inv_inv] at h
  have habelian := hBab _ hb₁' _ hb₂'
  have hs1 : (g⁻¹ * b₁ * g) * (g⁻¹ * b₂ * g) = g⁻¹ * (b₁ * b₂) * g := by group
  have hs2 : (g⁻¹ * b₂ * g) * (g⁻¹ * b₁ * g) = g⁻¹ * (b₂ * b₁) * g := by group
  rw [hs1, hs2] at habelian
  have hconj := congrArg (fun z => g * z * g⁻¹) habelian
  calc b₁ * b₂ = g * (g⁻¹ * (b₁ * b₂) * g) * g⁻¹ := by group
    _ = g * (g⁻¹ * (b₂ * b₁) * g) * g⁻¹ := hconj
    _ = b₂ * b₁ := by group

/-- `A`, `B` abelian で `⟨A, B⟩ = ⊤` ⇒ `A ⊓ B ⊆ Z(G)`.

Wielandt と Zenkov Case 1 共通の中心性論証. centralizer ⊇ A ∪ B ⇒ centralizer ⊇ ⟨A,B⟩ = ⊤. -/
private lemma inf_le_center_of_join_eq_top {G : Type*} [Group G] {A B : Subgroup G}
    (hAab : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hBab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hsup : A ⊔ B = ⊤) :
    (A ⊓ B : Subgroup G) ≤ Subgroup.center G := by
  intro c hc
  rw [Subgroup.mem_inf] at hc
  obtain ⟨hc_A, hc_B⟩ := hc
  rw [Subgroup.mem_center_iff]
  intro x
  have h_central_A : A ≤ Subgroup.centralizer ({c} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]
    exact (hAab a ha c hc_A).symm
  have h_central_B : B ≤ Subgroup.centralizer ({c} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]
    exact (hBab b hb c hc_B).symm
  have h_sup_le := sup_le h_central_A h_central_B
  have h_centralizer_top : Subgroup.centralizer ({c} : Set G) = ⊤ :=
    top_le_iff.mp (hsup ▸ h_sup_le)
  have hx_central : x ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [h_centralizer_top]; exact Subgroup.mem_top x
  rw [Subgroup.mem_centralizer_iff] at hx_central
  exact (hx_central c (Set.mem_singleton _)).symm

-- rc2: IsMulCommutative→CommGroup is scoped; open locally (file-wide blows up
-- `CommGroup (MulAut ?m)` typeclass search elsewhere in this file).
open scoped IsMulCommutative in
/-- `Subgroup.center G ≤ fitting G`. Center は abelian → 冪零, 正規部分群. -/
private lemma center_le_fitting (G : Type*) [Group G] [Finite G] :
    Subgroup.center G ≤ fitting G := by
  haveI : Group.IsNilpotent ↥(Subgroup.center G) := inferInstance
  exact nilpotent_normal_le_fitting

/-- 有限群 `M` は **その全 Sylow 部分群の sup** で生成される: 各素因子 `p` ごとの
全 Sylow `p` 部分群を sup したものは `⊤_M`.

書籍では「`M` は Sylow 部分群で生成される」と頻用される. mathlib の
`iSup_default_sylow_eq_top_of_nilpotent` は冪零版 (一つの Sylow per prime で十分).
本版は一般有限群対応 (Sylow 共役を全て取る).

証明: 各素因子 `p` に対し `|Sylow p| = p ^ v_p(|M|)` (`Sylow.card_eq_multiplicity`),
これが sup の card を割る. 異素因子で coprime ⇒ factorization 比較で `|sup| = |M|`. -/
private lemma iSup_sylow_eq_top {M : Type*} [Group M] [Finite M] :
    (⨆ p : (Nat.card M).primeFactors, ⨆ P : Sylow p.val M, (P : Subgroup M)) = ⊤ := by
  classical
  set sup := ⨆ p : (Nat.card M).primeFactors, ⨆ P : Sylow p.val M, (P : Subgroup M) with hsup_def
  -- |sup| ∣ |M|.
  have h_sup_dvd : Nat.card sup ∣ Nat.card M := Subgroup.card_subgroup_dvd_card sup
  -- For each p ∈ primeFactors |M|, p^{v_p(|M|)} ∣ |sup|.
  have h_pow_dvd : ∀ p ∈ (Nat.card M).primeFactors,
      p ^ (Nat.card M).factorization p ∣ Nat.card sup := by
    intro p hp
    haveI hp_prime : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    have hP_le : ((default : Sylow p M) : Subgroup M) ≤ sup := by
      rw [hsup_def]
      refine le_trans ?_ (le_iSup (fun q : (Nat.card M).primeFactors =>
        ⨆ Q : Sylow q.val M, (Q : Subgroup M)) ⟨p, hp⟩)
      exact le_iSup (fun Q : Sylow p M => (Q : Subgroup M)) default
    have h_dvd := Subgroup.card_dvd_of_le hP_le
    rwa [Sylow.card_eq_multiplicity] at h_dvd
  -- v_p(|M|) ≤ v_p(|sup|) for all p.
  have h_factorization_le : ∀ p, (Nat.card M).factorization p ≤ (Nat.card sup).factorization p := by
    intro p
    rcases Nat.eq_zero_or_pos ((Nat.card M).factorization p) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hp_in : p ∈ (Nat.card M).primeFactors := by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr (by omega)
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
      exact (hp_prime.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp (h_pow_dvd p hp_in)
  -- v_p(|sup|) ≤ v_p(|M|) for all p.
  have h_factorization_le' : ∀ p, (Nat.card sup).factorization p ≤ (Nat.card M).factorization p :=
    fun p => (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr h_sup_dvd p
  -- |sup| = |M|.
  have h_eq : Nat.card sup = Nat.card M := by
    apply Nat.eq_of_factorization_eq Nat.card_pos.ne' Nat.card_pos.ne'
    intro p
    exact le_antisymm (h_factorization_le' p) (h_factorization_le p)
  exact Subgroup.eq_top_of_card_eq sup h_eq

/-- 補助: `S ≤ opCore p H` (p-subgroup of opCore), `S'` p-subgroup of H ⇒ `S ⊔ S'` p-group.

Zenkov Case 2 で `⟨P, P^x⟩` (P が p-Sylow of M, P^x conjugate) を p-group と
示す核心. `opCore p H ⊴ H` で normal-sup-pgroup を経由. -/
private lemma sup_isPGroup_of_le_opCore_left {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] {S S' : Subgroup H}
    (hS : S ≤ opCore p H) (hS' : IsPGroup p S') :
    IsPGroup p ↥(S ⊔ S' : Subgroup H) := by
  have h_op_pgroup : IsPGroup p ↥(opCore p H) := opCore_isPGroup p H
  haveI : (opCore p H).Normal := opCore.normal p H
  have h_op_sup : IsPGroup p ↥(opCore p H ⊔ S' : Subgroup H) :=
    h_op_pgroup.to_sup_of_normal_left hS'
  exact h_op_sup.to_le (sup_le_sup_right hS _)

open scoped Pointwise in
/-- 補助: G の Zenkov minimality `hMin` を `↥H` に転送 (Zenkov Case 2 IH 適用用).

`A ≤ H` のとき, G レベルの `A ⊓ B^g ≤ A ⊓ B ⇒ equal` から ↥H レベルの対応する
minimality を導く. `conj_smul_subgroupOf` (`h ∈ H` で `H` 共役不変) + subgroupOf 同型. -/
private lemma zenkov_minimality_transfer {G : Type*} [Group G] {A B : Subgroup G}
    (hMin : ∀ g : G, (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) ≤ A ⊓ B →
        (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) = A ⊓ B)
    {H : Subgroup G} (hAH : A ≤ H) :
    ∀ h : ↥H,
      ((A.subgroupOf H : Subgroup ↥H) ⊓
        ((MulAut.conj h) • (B.subgroupOf H) : Subgroup ↥H)) ≤
        A.subgroupOf H ⊓ B.subgroupOf H →
      ((A.subgroupOf H : Subgroup ↥H) ⊓
        ((MulAut.conj h) • (B.subgroupOf H) : Subgroup ↥H)) =
        A.subgroupOf H ⊓ B.subgroupOf H := by
  intro h hle
  have hB_sub : B.subgroupOf H = (B ⊓ H).subgroupOf H :=
    (Subgroup.inf_subgroupOf_right B H).symm
  have hBcap_le_H : (B ⊓ H : Subgroup G) ≤ H := inf_le_right
  have hconj : ((MulAut.conj h) • B.subgroupOf H : Subgroup ↥H) =
      (((MulAut.conj (h : G)) • (B ⊓ H) : Subgroup G).subgroupOf H : Subgroup ↥H) := by
    rw [hB_sub]
    exact Subgroup.conj_smul_subgroupOf hBcap_le_H h
  have h_conj_H_eq_H : ((MulAut.conj (h : G)) • H : Subgroup G) = H := by
    ext y
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def]
    change (h : G)⁻¹ * y * ((h : G)⁻¹)⁻¹ ∈ H ↔ y ∈ H
    rw [inv_inv]
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · have heq : (h : G) * ((h : G)⁻¹ * y * (h : G)) * (h : G)⁻¹ = y := by group
      rw [← heq]
      exact H.mul_mem (H.mul_mem h.2 hy) (H.inv_mem h.2)
    · exact H.mul_mem (H.mul_mem (H.inv_mem h.2) hy) h.2
  have h_conj_inter : ((MulAut.conj (h : G)) • (B ⊓ H) : Subgroup G) =
      ((MulAut.conj (h : G)) • B : Subgroup G) ⊓ H := by
    rw [Subgroup.smul_inf, h_conj_H_eq_H]
  rw [hconj, h_conj_inter] at hle ⊢
  have h_lhs_eq : ((A.subgroupOf H : Subgroup ↥H) ⊓
      (((MulAut.conj (h : G)) • B ⊓ H : Subgroup G).subgroupOf H : Subgroup ↥H)) =
      ((A ⊓ ((MulAut.conj (h : G)) • B) : Subgroup G).subgroupOf H : Subgroup ↥H) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    refine ⟨fun ⟨hxA, hxB_H⟩ => ⟨hxA, hxB_H.1⟩, fun ⟨hxA, hxB⟩ => ⟨hxA, hxB, x.2⟩⟩
  have h_rhs_eq : ((A.subgroupOf H : Subgroup ↥H) ⊓ B.subgroupOf H) =
      ((A ⊓ B : Subgroup G).subgroupOf H : Subgroup ↥H) := by
    ext x; simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [h_lhs_eq, h_rhs_eq] at hle ⊢
  have hLA_le_H : (A ⊓ ((MulAut.conj (h : G)) • B) : Subgroup G) ≤ H :=
    le_trans inf_le_left hAH
  have hle_G : (A ⊓ ((MulAut.conj (h : G)) • B) : Subgroup G) ≤ (A ⊓ B : Subgroup G) := by
    intro y hy
    have hyH : y ∈ H := hLA_le_H hy
    have : (⟨y, hyH⟩ : ↥H) ∈
        ((A ⊓ ((MulAut.conj (h : G)) • B) : Subgroup G).subgroupOf H : Subgroup ↥H) := hy
    exact hle this
  have h_eq_G := hMin (h : G) hle_G
  exact congrArg (·.subgroupOf H) h_eq_G

open scoped Pointwise in
/-- **Zenkov Case 1** (Isaacs Thm 2.18 の Case 1, WLOG `g₀ = 1`):
`A`, `B` abelian, `M = A ⊓ B` minimal in family, **かつ ある `g` で `A ⊔ B^g = ⊤`** ⇒
`M ⊆ F(G)`.

書籍 p.61 Case 1: `A ⊓ B^g ⊆ Z(G)` (A, B^g abelian + 生成) → 中心元は conj 不変
⇒ `A ⊓ B^g ⊆ B` ⇒ `A ⊓ B^g ⊆ M`. Minimality で `M = A ⊓ B^g ⊆ Z(G) ⊆ F(G)`. -/
theorem zenkov_case1_le_fitting {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAab : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hBab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hMin : ∀ g : G, (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) ≤ A ⊓ B →
        (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) = A ⊓ B)
    (hExists : ∃ g : G, A ⊔ ((MulAut.conj g) • B : Subgroup G) = ⊤) :
    (A ⊓ B : Subgroup G) ≤ fitting G := by
  obtain ⟨g, hsup⟩ := hExists
  have hBg_ab := conj_smul_abelian hBab g
  have h_inf_center : (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) ≤
      Subgroup.center G := inf_le_center_of_join_eq_top hAab hBg_ab hsup
  -- A ⊓ B^g ⊆ B: central c は g⁻¹ c g = c, c = g b g⁻¹ ⇒ b = c ∈ B.
  have h_inf_le_B : (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) ≤ B := by
    intro c hc
    have hc_central : c ∈ Subgroup.center G := h_inf_center hc
    rw [Subgroup.mem_inf] at hc
    obtain ⟨_, hc_Bg⟩ := hc
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def] at hc_Bg
    change g⁻¹ * c * (g⁻¹)⁻¹ ∈ B at hc_Bg
    rw [Subgroup.mem_center_iff] at hc_central
    have h_inv_c_g : g⁻¹ * c = c * g⁻¹ := hc_central g⁻¹
    have h_eq : g⁻¹ * c * (g⁻¹)⁻¹ = c := by rw [h_inv_c_g]; group
    rwa [h_eq] at hc_Bg
  have h_inf_le_M : (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) ≤ A ⊓ B :=
    le_inf inf_le_left h_inf_le_B
  have h_eq := hMin g h_inf_le_M
  rw [← h_eq]
  exact h_inf_center.trans (center_le_fitting G)

open scoped Pointwise in
/-- **Isaacs Thm 2.18 (Zenkov)** WLOG version (`g₀ = 1`, `M = A ⊓ B`): `|G|`-induction.
Case 1: `zenkov_case1_le_fitting`. Case 2: Sylow-by-Sylow via Baer iff + IH on `↥H`. -/
private theorem zenkov_wlog_aux : ∀ n : ℕ,
    ∀ (G : Type*) [Group G] [Finite G], Nat.card G ≤ n →
    ∀ (A B : Subgroup G),
      (∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) →
      (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) →
      (∀ g : G, (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) ≤ A ⊓ B →
        (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) = A ⊓ B) →
      (A ⊓ B : Subgroup G) ≤ fitting G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hcard A B _ _ _
    exact absurd hcard (Nat.not_le_of_lt Nat.card_pos)
  | succ n ih =>
    intro G _ _ hcard A B hAab hBab hMin
    classical
    by_cases h_case1 : ∃ g : G, A ⊔ ((MulAut.conj g) • B : Subgroup G) = ⊤
    · exact zenkov_case1_le_fitting hAab hBab hMin h_case1
    push Not at h_case1
    -- Case 2.
    set M := (A ⊓ B : Subgroup G) with hM_def
    -- Show M ≤ fitting G via Sylow + Baer.
    have hM_top_map : ((⊤ : Subgroup ↥M).map M.subtype : Subgroup G) = M := by
      rw [← MonoidHom.range_eq_map, M.range_subtype]
    have hM_eq_sup : (M : Subgroup G) =
        (⨆ p : (Nat.card ↥M).primeFactors, ⨆ P : Sylow p.val ↥M,
          ((P : Subgroup ↥M).map M.subtype : Subgroup G)) := by
      conv_lhs => rw [← hM_top_map, ← iSup_sylow_eq_top (M := ↥M)]
      simp_rw [Subgroup.map_iSup]
    rw [hM_eq_sup]
    refine iSup_le fun p => iSup_le fun P => ?_
    haveI hp_prime : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    set P_in_G : Subgroup G := (P : Subgroup ↥M).map M.subtype with hPG_def
    have hP_pgroup : IsPGroup p.val ↥P_in_G := P.2.map M.subtype
    have hP_in_M : P_in_G ≤ M := by
      rw [hPG_def]
      intro y hy
      obtain ⟨z, _, hz⟩ := hy
      rw [← hz]; exact z.2
    -- Use Baer iff: P_in_G ≤ fitting G iff ∀ x, ⟨P_in_G, P_in_G^x⟩ nilpotent.
    rw [le_fitting_iff_baer_sup_conj_isNilpotent]
    intro x
    set H : Subgroup G := A ⊔ ((MulAut.conj x) • B : Subgroup G) with hH_def
    have hH_proper : H ≠ ⊤ := h_case1 x
    have hH_card_le : Nat.card ↥H ≤ n := by
      have hlt : Nat.card ↥H < Nat.card G := by
        have h_le : Nat.card ↥H ≤ Nat.card G := H.card_le_card_group
        have h_ne : Nat.card ↥H ≠ Nat.card G := fun heq =>
          hH_proper (Subgroup.eq_top_of_card_eq H heq)
        omega
      omega
    have hA_le_H : A ≤ H := le_sup_left
    have hBx_le_H : ((MulAut.conj x) • B : Subgroup G) ≤ H := le_sup_right
    have hM_le_H : M ≤ H := le_trans (inf_le_left : (A ⊓ B : Subgroup G) ≤ A) hA_le_H
    have hP_le_H : P_in_G ≤ H := hP_in_M.trans hM_le_H
    have hP_le_B : P_in_G ≤ B := hP_in_M.trans (inf_le_right : (A ⊓ B : Subgroup G) ≤ B)
    have hPx_le_H : ((MulAut.conj x) • P_in_G : Subgroup G) ≤ H := by
      refine le_trans ?_ hBx_le_H
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hP_le_B
    -- Apply IH on ↥H.
    have hAH_ab : ∀ a ∈ A.subgroupOf H, ∀ b ∈ A.subgroupOf H, a * b = b * a := by
      intro a ha b hb
      rw [Subgroup.mem_subgroupOf] at ha hb
      exact Subtype.ext (hAab _ ha _ hb)
    have hBH_ab : ∀ a ∈ B.subgroupOf H, ∀ b ∈ B.subgroupOf H, a * b = b * a := by
      intro a ha b hb
      rw [Subgroup.mem_subgroupOf] at ha hb
      exact Subtype.ext (hBab _ ha _ hb)
    have hMin_H := zenkov_minimality_transfer hMin hA_le_H
    have hIH : ((A.subgroupOf H : Subgroup ↥H) ⊓ B.subgroupOf H : Subgroup ↥H) ≤
        fitting ↥H := ih ↥H hH_card_le (A.subgroupOf H) (B.subgroupOf H) hAH_ab hBH_ab hMin_H
    -- (A.subgroupOf H) ⊓ B.subgroupOf H = M.subgroupOf H.
    have hMH_eq : (A.subgroupOf H : Subgroup ↥H) ⊓ B.subgroupOf H = M.subgroupOf H := by
      ext y; simp [Subgroup.mem_inf, Subgroup.mem_subgroupOf, hM_def]
    rw [hMH_eq] at hIH
    -- P_in_G.subgroupOf H ≤ M.subgroupOf H ≤ fitting ↥H.
    have hPH_le_MH : P_in_G.subgroupOf H ≤ M.subgroupOf H := Subgroup.subgroupOf_mono _ hP_in_M
    have hPH_le_F : P_in_G.subgroupOf H ≤ fitting ↥H := hPH_le_MH.trans hIH
    -- P_in_G.subgroupOf H is p-group (via subgroupOfEquivOfLe iso).
    have hPH_pgroup : IsPGroup p.val (P_in_G.subgroupOf H) :=
      hP_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hP_le_H).symm
    have hPH_le_op : P_in_G.subgroupOf H ≤ opCore p.val ↥H :=
      mem_opCore_of_le_fitting_of_isPGroup hPH_pgroup hPH_le_F
    -- (P_in_G)^x.subgroupOf H is p-group.
    have hPx_pgroup : IsPGroup p.val ((MulAut.conj x) • P_in_G : Subgroup G) := by
      rw [Subgroup.pointwise_smul_def]
      exact hP_pgroup.map _
    have hPxH_pgroup : IsPGroup p.val (((MulAut.conj x) • P_in_G : Subgroup G).subgroupOf H) :=
      hPx_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hPx_le_H).symm
    -- Sup of the two subgroupOf H is p-group.
    have h_sup_pgroup_H : IsPGroup p.val ↥(P_in_G.subgroupOf H ⊔
        ((MulAut.conj x) • P_in_G : Subgroup G).subgroupOf H : Subgroup ↥H) :=
      sup_isPGroup_of_le_opCore_left hPH_le_op hPxH_pgroup
    -- Sup of subgroupOf = (sup).subgroupOf.
    have hsup_le_H : (P_in_G ⊔ (MulAut.conj x) • P_in_G : Subgroup G) ≤ H :=
      sup_le hP_le_H hPx_le_H
    have h_sup_subgroupOf : (P_in_G ⊔ (MulAut.conj x) • P_in_G : Subgroup G).subgroupOf H =
        P_in_G.subgroupOf H ⊔ ((MulAut.conj x) • P_in_G : Subgroup G).subgroupOf H :=
      Subgroup.subgroupOf_sup hP_le_H hPx_le_H
    rw [← h_sup_subgroupOf] at h_sup_pgroup_H
    -- Transfer p-group property back to G via subgroupOfEquivOfLe.
    have h_sup_pgroup_G : IsPGroup p.val ↥(P_in_G ⊔ (MulAut.conj x) • P_in_G : Subgroup G) :=
      h_sup_pgroup_H.of_equiv (Subgroup.subgroupOfEquivOfLe hsup_le_H)
    exact h_sup_pgroup_G.isNilpotent

open scoped Pointwise in
/-- **Isaacs Thm 2.18 (Zenkov)**: 有限群 `G` の abelian 部分群 `A, B`. `g₀ ∈ G` で
`M = A ⊓ B^{g₀}` が集合 `{A ⊓ B^g | g ∈ G}` の minimal member (包含関係について) なら,
`M ⊆ F(G)`.

書籍 p.61 の証明 (induction on `|G|`):
1. WLOG `g₀ = 1` (B を `B^{g₀}` で置き換え) — 本実装で wrapper.
2. **Case G = ⟨A, B^g⟩ for some g**: `zenkov_case1_le_fitting`.
3. **Case ⟨A, B^g⟩ < G for all g**: Sylow-by-Sylow via Baer iff + IH on ↥H. -/
theorem zenkov_minimal_le_fitting [Finite G] {A B : Subgroup G}
    (hA_ab : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hB_ab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (g₀ : G)
    (hMin : ∀ g : G,
        (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) ≤
          A ⊓ ((MulAut.conj g₀) • B : Subgroup G) →
        (A ⊓ ((MulAut.conj g) • B : Subgroup G) : Subgroup G) =
          A ⊓ ((MulAut.conj g₀) • B : Subgroup G)) :
    (A ⊓ ((MulAut.conj g₀) • B : Subgroup G) : Subgroup G) ≤ fitting G := by
  -- WLOG: replace B with B' := (MulAut.conj g₀) • B. Family is the same.
  set B' : Subgroup G := (MulAut.conj g₀) • B with hB'_def
  have hB'_ab : ∀ b ∈ B', ∀ b' ∈ B', b * b' = b' * b := conj_smul_abelian hB_ab g₀
  have hMin' : ∀ h : G,
      (A ⊓ ((MulAut.conj h) • B' : Subgroup G) : Subgroup G) ≤ A ⊓ B' →
      (A ⊓ ((MulAut.conj h) • B' : Subgroup G) : Subgroup G) = A ⊓ B' := by
    intro h hle
    -- (MulAut.conj h) • B' = (MulAut.conj h) • ((MulAut.conj g₀) • B) = (MulAut.conj (h * g₀)) • B.
    have h_smul_eq : ((MulAut.conj h) • B' : Subgroup G) =
        ((MulAut.conj (h * g₀)) • B : Subgroup G) := by
      rw [hB'_def, ← mul_smul, ← map_mul]
    rw [h_smul_eq] at hle ⊢
    exact hMin (h * g₀) hle
  exact zenkov_wlog_aux (Nat.card G) G le_rfl A B' hA_ab hB'_ab hMin'

open scoped Pointwise in
/-- **Isaacs Cor 2.19**: `G` 非自明有限群, `A` abelian 部分群, `|A| ≥ |G:A|`
⇒ `A ⊓ F(G) ≠ ⊥`.

書籍 p.62 の証明: g ∈ G について `|A| · |A^g| = |A|² ≥ |G|`. `A < G` ならば Lemma 2.10
で `A · A^g ≠ G` (集合), `|A · A^g| = |A|² / |A ⊓ A^g|` の formula で `A ⊓ A^g > 1`.
Zenkov で minimal-card `g₀` を取り `A ⊓ A^{g₀} ⊆ F(G)`, これが `> 1` で `A ⊓ F(G) > 1`. -/
theorem inf_fitting_ne_bot_of_abelian_card_ge_index [Finite G] [Nontrivial G] {A : Subgroup G}
    (hA_ab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCard : A.index ≤ Nat.card A) :
    A ⊓ fitting G ≠ ⊥ := by
  classical
  -- Case 1: A = ⊤. Then G is abelian, F(G) = G ≠ ⊥.
  by_cases hAtop : A = ⊤
  · subst hAtop
    rw [top_inf_eq]
    -- G is commutative via hA_ab on ⊤.
    have hG_commute : ∀ a b : G, a * b = b * a := fun a b =>
      hA_ab a (Subgroup.mem_top a) b (Subgroup.mem_top b)
    -- center G = ⊤.
    have hcenter : Subgroup.center G = ⊤ := by
      ext x
      refine ⟨fun _ => Subgroup.mem_top x, fun _ => ?_⟩
      rw [Subgroup.mem_center_iff]
      intro g
      exact hG_commute g x
    -- G is nilpotent.
    haveI hGnilp : Group.IsNilpotent G := ⟨1, by
      rw [Subgroup.upperCentralSeries_one]; exact hcenter⟩
    -- ↥⊤ is also nilpotent.
    haveI : Group.IsNilpotent ↥(⊤ : Subgroup G) :=
      Group.nilpotent_of_mulEquiv Subgroup.topEquiv.symm
    -- F(G) = ⊤.
    have hFtop : fitting G = ⊤ := top_le_iff.mp (nilpotent_normal_le_fitting (N := ⊤))
    rw [hFtop]
    exact top_ne_bot
  · -- Case 2: A < ⊤.
    -- Pick g₀ minimizing |A ⊓ A^g| over g ∈ G.
    haveI : Fintype G := Fintype.ofFinite G
    set M : G → Subgroup G := fun g => A ⊓ ((MulAut.conj g) • A : Subgroup G) with hM_def
    obtain ⟨g₀, _, hg₀_min⟩ := Finset.exists_min_image Finset.univ
      (fun g => Nat.card ↥(M g)) Finset.univ_nonempty
    -- g₀ is ≤-minimal (used in Zenkov hypothesis).
    have hg₀_minimal : ∀ g : G, M g ≤ M g₀ → M g = M g₀ := by
      intro g hle
      have h_card_g₀_le_g : Nat.card ↥(M g₀) ≤ Nat.card ↥(M g) :=
        hg₀_min g (Finset.mem_univ _)
      -- M g ≤ M g₀ and |M g₀| ≤ |M g| ⇒ M g₀ = M g, hence M g = M g₀.
      exact (Subgroup.eq_of_le_of_card_ge hle h_card_g₀_le_g)
    -- Apply Zenkov to A, A.
    have h_M_le_F : M g₀ ≤ fitting G :=
      zenkov_minimal_le_fitting hA_ab hA_ab g₀ hg₀_minimal
    -- Show M g₀ ≠ ⊥ (using A < ⊤ + Lemma 2.10 + counting).
    have h_M_neBot : M g₀ ≠ ⊥ := by
      intro h_M_bot
      -- M g₀ = ⊥ means |M g₀| = 1.
      have h_card_one : Nat.card ↥(M g₀) = 1 := by
        rw [h_M_bot]; exact Subgroup.card_bot
      -- |A · A^g₀| · |M g₀| = |A| · |A^g₀| (counting helper).
      have h_count : Nat.card ((A : Set G) *
          (((MulAut.conj g₀) • A : Subgroup G) : Set G)) *
          Nat.card ↥(A ⊓ (MulAut.conj g₀) • A : Subgroup G) =
          Nat.card ↥A * Nat.card ↥((MulAut.conj g₀) • A : Subgroup G) :=
        card_set_mul_card_inf A ((MulAut.conj g₀) • A)
      -- |A^g₀| = |A| (conjugation preserves card).
      have h_conj_card : Nat.card ↥((MulAut.conj g₀) • A : Subgroup G) = Nat.card ↥A := by
        rw [Subgroup.pointwise_smul_def]
        exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g₀))
      -- M g₀ = A ⊓ ((MulAut.conj g₀) • A) by definition.
      have h_M_unfold : M g₀ = A ⊓ ((MulAut.conj g₀) • A : Subgroup G) := rfl
      rw [← h_M_unfold] at h_count
      rw [h_card_one, mul_one, h_conj_card] at h_count
      -- h_count : |A · A^g₀| = |A|²
      -- |A|² ≥ |G| (from hypothesis hCard).
      have h_A_sq : Nat.card G ≤ Nat.card ↥A * Nat.card ↥A := by
        calc Nat.card G = Nat.card ↥A * A.index := (Subgroup.card_mul_index A).symm
          _ ≤ Nat.card ↥A * Nat.card ↥A := Nat.mul_le_mul_left _ hCard
      -- |A · A^g₀| ≤ |G| (subset of G).
      have h_prod_subset : (A : Set G) *
          (((MulAut.conj g₀) • A : Subgroup G) : Set G) ⊆ Set.univ :=
        Set.subset_univ _
      -- A · A^g₀ = Set.univ (subset of G with cardinality |G|).
      have h_prod_eq_univ : (A : Set G) *
          (((MulAut.conj g₀) • A : Subgroup G) : Set G) = Set.univ := by
        apply Set.eq_of_subset_of_ncard_le h_prod_subset _ Set.finite_univ
        rw [Set.ncard_univ, ← Nat.card_coe_set_eq, h_count]
        exact h_A_sq
      -- Lemma 2.10: A · A^g₀ = univ ⇒ A = ⊤.
      -- For eq_top_of_set_mul_conj_eq_top, need: A * (MulAut.conj x⁻¹) • A = univ for some x.
      -- With x = g₀⁻¹: (MulAut.conj (g₀⁻¹)⁻¹) • A = (MulAut.conj g₀) • A. So apply with x = g₀⁻¹.
      have h_A_top : A = ⊤ := by
        apply eq_top_of_set_mul_conj_eq_top g₀⁻¹
        convert h_prod_eq_univ using 2
        rw [inv_inv]
      exact hAtop h_A_top
    -- Conclude.
    have h_M_le_inf : M g₀ ≤ A ⊓ fitting G := le_inf inf_le_left h_M_le_F
    intro hbot
    rw [hbot, le_bot_iff] at h_M_le_inf
    exact h_M_neBot h_M_le_inf

/-- **Isaacs Thm 2.20 (Lucchini) K > ⊥ structural reduction**: `K = A.normalCore ≠ ⊥` の
場合, Lucchini の K > ⊥ inductive step を担う **structural lemma**.

Given:
* `Ā := A.map (mk' K) ≤ G ⧸ K` で Lucchini の結論が成立する (`h_quot`).

Conclusion:
* `(A.normalCore.subgroupOf A).index < A.index` が `G` で成立.

証明は subgroup correspondence のみ使用 (Ch.4 等の外部章依存無し):
1. `f := mk' K`, `Ā := A.map f`.
2. **Ā.normalCore = ⊥** in `G/K` (K = A.normalCore の maximality 経由 pullback).
3. `h_quot` を `Ā.normalCore = ⊥` で書き換えると `Nat.card Ā < Ā.index`.
4. `Ā.index = A.index` (`index_map_eq`, `ker f = K ≤ A`).
5. `Nat.card Ā = (K.subgroupOf A).index` (`f.subgroupMap A` の核 + quotient).
6. 結論.

**Lucchini 完全定理本体** (`lucchini_index_normalCore_lt_index`) は
`Ch04_Commutators/ForwardFromCh02.lean` に. K = ⊥ case が Ch.4 §4A-§4B
(lcs 加法性) に依存するため owner chapter (Ch.4) に置く. 詳細は
[`notes/meta/forward_dep_policy.md`](../../notes/meta/forward_dep_policy.md). -/
theorem lucchini_K_pos_reduction [Finite G] {A : Subgroup G}
    (_hAprop : A < ⊤)
    (_hK_ne_bot : A.normalCore ≠ ⊥)
    (h_quot :
      ((A.map (QuotientGroup.mk' A.normalCore)).normalCore.subgroupOf
        (A.map (QuotientGroup.mk' A.normalCore))).index <
      (A.map (QuotientGroup.mk' A.normalCore)).index) :
    (A.normalCore.subgroupOf A).index < A.index := by
  set K := A.normalCore with hKdef
  haveI hKnormal : K.Normal := A.normalCore_normal
  have hK_le_A : K ≤ A := Subgroup.normalCore_le A
  -- Set up the quotient map f : G →* G/K.
  let f : G →* G ⧸ K := QuotientGroup.mk' K
  have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective K
  have hf_ker : f.ker = K := QuotientGroup.ker_mk' K
  set Ā : Subgroup (G ⧸ K) := A.map f with hĀ_def
  -- Ā.normalCore = ⊥ in G/K (the key Ch.2-level fact).
  have hĀ_core_bot : Ā.normalCore = ⊥ := by
    rw [eq_bot_iff]
    intro xbar hxbar
    -- Pullback: comap (Ā.normalCore) ⊴ G with K ≤ comap ≤ A.
    -- So comap ≤ A.normalCore = K, thus comap = K, thus xbar = 1.
    have h_subset : (Subgroup.comap f Ā.normalCore : Subgroup G) ≤ A := by
      have h_le : Ā.normalCore ≤ Ā := Subgroup.normalCore_le _
      have h_comap_le : Subgroup.comap f Ā.normalCore ≤ Subgroup.comap f Ā :=
        Subgroup.comap_mono h_le
      have h_comap_eq : (Subgroup.comap f Ā : Subgroup G) = K ⊔ A := by
        rw [hĀ_def, QuotientGroup.comap_map_mk']
      rw [h_comap_eq, sup_of_le_right hK_le_A] at h_comap_le
      exact h_comap_le
    haveI : (Subgroup.comap f Ā.normalCore).Normal :=
      (Subgroup.normalCore_normal Ā).comap f
    have h_comap_le_K : Subgroup.comap f Ā.normalCore ≤ K :=
      Subgroup.normal_le_normalCore.mpr h_subset
    obtain ⟨g, hgmap⟩ := hf_surj xbar
    have hg_comap : g ∈ Subgroup.comap f Ā.normalCore := by
      change f g ∈ Ā.normalCore; rw [hgmap]; exact hxbar
    have hg_K : g ∈ K := h_comap_le_K hg_comap
    rw [← hgmap]
    change f g = 1
    rw [← hf_ker] at hg_K
    exact hg_K
  -- Translate h_quot. Ā.normalCore = ⊥, so LHS = Nat.card Ā.
  have h_lhs : (Ā.normalCore.subgroupOf Ā).index = Nat.card ↥Ā := by
    rw [hĀ_core_bot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
  -- Ā.index = A.index by index_map_eq (f surjective, K = ker f ≤ A).
  have h_rhs : Ā.index = A.index := by
    rw [hĀ_def]
    exact Subgroup.index_map_eq A hf_surj (by rw [hf_ker]; exact hK_le_A)
  -- Convert h_quot to our notation.
  have hIH : (Ā.normalCore.subgroupOf Ā).index < Ā.index := h_quot
  rw [h_lhs, h_rhs] at hIH
  -- |Ā| = (K.subgroupOf A).index via f.subgroupMap A.
  have h_card_Ā : Nat.card ↥Ā = (K.subgroupOf A).index := by
    rw [hĀ_def]
    -- ker (f.subgroupMap A) = K.subgroupOf A (as subgroup of A).
    have hker_eq : (f.subgroupMap A).ker = K.subgroupOf A := by
      ext x
      simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      constructor
      · intro hx
        have hf_eq : f ↑x = 1 := by
          have h := congr_arg (Subtype.val : A.map f → G ⧸ K) hx
          change f ↑x = (1 : G ⧸ K) at h
          exact h
        have : (↑x : G) ∈ f.ker := hf_eq
        rwa [hf_ker] at this
      · intro hx
        have hf_eq : f ↑x = 1 := by
          have : (↑x : G) ∈ f.ker := by rw [hf_ker]; exact hx
          exact this
        apply Subtype.ext
        change f ↑x = (1 : G ⧸ K)
        exact hf_eq
    have h_eq : Nat.card ↥(A.map f) = Nat.card (A ⧸ (f.subgroupMap A).ker) :=
      Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective (f.subgroupMap A)
          (f.subgroupMap_surjective A)).symm.toEquiv
    rw [h_eq, hker_eq, ← Subgroup.index_eq_card]
  rw [h_card_Ā] at hIH
  exact hIH

end -- 2D

end OddOrder.Isaacs.Ch02

