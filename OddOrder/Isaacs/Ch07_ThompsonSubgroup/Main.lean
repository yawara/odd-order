/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.Basic

/-!
# TAIL

Prefix-split from `OddOrder.Isaacs.Ch07_ThompsonSubgroup.Main` (2000-line limit, issue 0103 第 2 パス).
-/
namespace OddOrder.Isaacs.Ch07
open scoped commutatorElement
open scoped Pointwise
open scoped IsMulCommutative -- rc2: IsMulCommutative→CommGroup/Monoid now scoped

variable {G : Type*} [Group G]


/-! ### §7D Step 8 — normal `J` for `p`-type maximals (Isaacs L4045-4063)

Helper lemmas toward discharging Step 8 (the `normal_J` hypotheses for `M`). -/


/-- **§7D Step 8 helper** — `2 ∤ |M|` for a subgroup `M` of a simple `p^a q^b`
group with `p, q` both odd.  Hence Sylow-`2` subgroups of `M` are trivial. -/
theorem two_not_dvd_card_subgroup_of_odd_primes
    {H : Type*} [Group H] [Finite H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (_hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (M : Subgroup H) :
    ¬ (2 : ℕ) ∣ Nat.card ↥M := by
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  intro h2_dvd
  have h2_dvd_H : (2 : ℕ) ∣ Nat.card H := h2_dvd.trans M.card_subgroup_dvd_card
  rw [hH_card] at h2_dvd_H
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2_dvd_H with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp_prime).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  · exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq_prime).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm

/-- **§7D Step 8 helper** — Sylow-`2` subgroups of `M` are abelian (in fact
trivial) when `2 ∤ |M|`.  Phrased as the `normal_J` hypothesis. -/
theorem sylow2_abelian_of_two_not_dvd
    {M : Type*} [Group M] [Finite M]
    (h2 : ¬ (2 : ℕ) ∣ Nat.card M) :
    ∀ S : Subgroup M, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S hS x y
  -- `S` is a `2`-group; `|S| ∣ |M|`; since `2 ∤ |M|`, `|S| = 1`, so `S` is trivial.
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hS_dvd : Nat.card ↥S ∣ Nat.card M := S.card_subgroup_dvd_card
  have hn0 : n = 0 := by
    by_contra hne
    exact h2 ((hn ▸ dvd_pow_self 2 hne).trans hS_dvd)
  have hS_card_one : Nat.card ↥S = 1 := by rw [hn, hn0, pow_zero]
  haveI : Subsingleton ↥S := Nat.card_eq_one_iff_unique.mp hS_card_one |>.1
  exact Subsingleton.elim (x * y) (y * x)

/-- **§7D Step 8 — fifth normal-J hypothesis** (Isaacs L4055-4063): for a
`p`-type maximal `M` and `S ∈ Syl_p(M)`, the centralizer of `Z(S)` in `M`
is exactly `S`: `C_M(Z(S)) = S`.

Textbook proof: `S ⊆ C_M(Z(S))` always.  For the reverse it suffices that
`C_M(Z(S))` is a `p`-group (a `p`-subgroup of `M` containing the Sylow `S` must
equal `S`).  Otherwise an order-`q` element `y ∈ C_M(Z(S))` gives a nontrivial
`q`-subgroup `Y = ⟨y⟩` normalized by `Z(S)`; choosing `P ∈ Syl_p(H)` with
`S = M ∩ P` and `M = N_H(O_p(M))`, the nontrivial center `Z(P)` lies in
`M ∩ P = S` and centralizes `S`, hence `Z(S)` contains a `p`-central element `x`
of `H`.  Then `x` normalizes `Y`, contradicting Step 6 (with `p, q` swapped). -/
theorem step8_centralizer_center_eq_sylow
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_pType : IsPType p M)
    (S : Sylow p ↥M) :
    Subgroup.centralizer
      (((Subgroup.center (S : Subgroup ↥M)).map (S : Subgroup ↥M).subtype) : Set ↥M)
      = (S : Subgroup ↥M) := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  -- `p ∣ |H|`, `q ∣ |H|`.
  obtain ⟨hp_dvd, hq_dvd⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  -- Abbreviations.
  set ZS : Subgroup ↥M :=
    (Subgroup.center (S : Subgroup ↥M)).map (S : Subgroup ↥M).subtype with hZS_def
  set C : Subgroup ↥M := Subgroup.centralizer (ZS : Set ↥M) with hC_def
  -- (A) `S ≤ C_M(Z(S))`: every `s ∈ S` commutes with `Z(S)`.
  have hS_le_C : (S : Subgroup ↥M) ≤ C := by
    intro s hs
    rw [hC_def, Subgroup.mem_centralizer_iff]
    intro z hz
    -- `z ∈ Z(S).map subtype`: `z = ↑z₀` with `z₀ ∈ center S`.
    obtain ⟨z₀, hz₀_center, rfl⟩ := hz
    -- `z₀` central in `S` ⇒ commutes with `⟨s, hs⟩`.
    have := (Subgroup.mem_center_iff.mp hz₀_center) ⟨s, hs⟩
    -- push to `↥M`.
    have h2 := congrArg (Subgroup.subtype (S : Subgroup ↥M)) this
    simpa [mul_comm] using h2.symm
  -- (B) `C` is a `p`-group.  Suppose not, and derive a contradiction via Step 6.
  have hC_pgroup : IsPGroup p C := by
    by_contra hC_not_p
    -- `q ∣ |C|`: a prime `r ∣ |C|` with `r ≠ p` must be `q` (since `|C| ∣ |M| ∣ p^a q^b`).
    -- Some prime `r ∣ |C|` is `≠ p` (else `C` would be a `p`-group).
    have hq_dvd_C : q ∣ Nat.card ↥C := by
      by_contra hq_ndvd
      -- Every prime factor of `|C|` is `p`, so `C` is a `p`-group — contradiction.
      apply hC_not_p
      apply OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton (G := ↥M) (p := p)
      intro r hr
      obtain ⟨hr_prime, hr_dvd_C, _⟩ := Nat.mem_primeFactors.mp hr
      have hr_dvd_M : r ∣ Nat.card ↥M := hr_dvd_C.trans C.card_subgroup_dvd_card
      have hr_dvd_paqb : r ∣ p ^ a * q ^ b := by
        rw [← hH_card]; exact hr_dvd_M.trans M.card_subgroup_dvd_card
      simp only [Set.mem_singleton_iff]
      rcases (Nat.Prime.dvd_mul hr_prime).mp hr_dvd_paqb with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hr_prime hp_prime).mp (hr_prime.dvd_of_dvd_pow h)
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp
          (hr_prime.dvd_of_dvd_pow h) ▸ hr_dvd_C) hq_ndvd
    -- Cauchy: an order-`q` element `y₀ ∈ C`.
    haveI : Fact q.Prime := ⟨hq_prime⟩
    obtain ⟨y₀, hy₀_ord⟩ := exists_prime_orderOf_dvd_card' q hq_dvd_C
    -- `Y₀ = ⟨y₀.val⟩` is a nontrivial `q`-subgroup of `↥M`; map to `H`.
    set yM : ↥M := (y₀ : ↥M) with hyM_def
    have hyM_ord : orderOf yM = q := by rw [hyM_def, Subgroup.orderOf_coe, hy₀_ord]
    have hyM_ne_one : yM ≠ 1 := by
      intro h1; rw [h1, orderOf_one] at hyM_ord; exact hq_prime.ne_one hyM_ord.symm
    set Y₀ : Subgroup ↥M := Subgroup.zpowers yM with hY₀_def
    have hY₀_q : IsPGroup q Y₀ := by
      apply IsPGroup.of_card (n := 1)
      rw [pow_one, hY₀_def, Nat.card_zpowers, hyM_ord]
    set YH : Subgroup H := Y₀.map M.subtype with hYH_def
    have hYH_q : IsPGroup q YH := hY₀_q.map M.subtype
    -- `YH ≠ ⊥` (since `yM ≠ 1` maps to `↑yM ≠ 1`).
    have hYH_ne_bot : YH ≠ ⊥ := by
      rw [hYH_def, hY₀_def]
      intro hbot
      apply hyM_ne_one
      have : (M.subtype yM) = 1 := by
        have hmem : M.subtype yM ∈ (Subgroup.zpowers yM).map M.subtype :=
          ⟨yM, Subgroup.mem_zpowers yM, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem; exact hmem
      simpa using this
    -- Build the ambient `p`-central element `x ∈ Z(S) ⊆ M ∩ P` normalizing `YH`.
    -- (i) `M = N_H(V)` for `V = O_p(M).map subtype`.
    set K₀ : Subgroup ↥M := OddOrder.Isaacs.Ch01.opCore p ↥M with hK₀_def
    haveI hK₀_normal : K₀.Normal := by rw [hK₀_def]; infer_instance
    set V : Subgroup H := K₀.map M.subtype with hV_def
    have hV_ne_bot : V ≠ ⊥ := by
      intro hbot
      -- `V = ⊥` and `subtype` injective ⇒ `K₀ = ⊥`, contradicting `IsPType`.
      have hK₀_bot : K₀ = ⊥ := by
        rw [hV_def] at hbot
        exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp hbot
      exact hM_pType.2 hK₀_bot
    have hV_le_M : V ≤ M := by rw [hV_def]; exact Subgroup.map_subtype_le _
    have hM_norm_V : (M : Subgroup H) ≤ Subgroup.normalizer V := by
      -- `K₀ ⊴ ↥M` ⇒ `normalizer K₀ = ⊤`; map by `subtype` lands in `normalizer V`.
      have h1 : (Subgroup.normalizer (K₀ : Set ↥M)).map M.subtype
          ≤ Subgroup.normalizer ((K₀.map M.subtype : Subgroup H) : Set H) :=
        Subgroup.le_normalizer_map M.subtype
      rw [Subgroup.normalizer_eq_top_iff.mpr hK₀_normal] at h1
      have h3 : (⊤ : Subgroup ↥M).map M.subtype = M := by
        rw [← MonoidHom.range_eq_map, M.range_subtype]
      rw [h3] at h1
      rw [hV_def]
      exact h1
    have hM_eq_NV : Subgroup.normalizer V = M :=
      maximal_eq_normalizer_of_M_normalizes hM_pType.1 hV_ne_bot hV_le_M hM_norm_V
    -- (ii) `S_H := S.map subtype` extends to `P_H ∈ Syl_p(H)`.
    set SH : Subgroup H := (S : Subgroup ↥M).map M.subtype with hSH_def
    have hSH_p : IsPGroup p SH := S.isPGroup'.map M.subtype
    obtain ⟨PH, hSH_le_PH⟩ := IsPGroup.exists_le_sylow hSH_p
    have hPH_ne_bot : (PH : Subgroup H) ≠ ⊥ := Sylow.ne_bot_of_dvd_card hp_dvd PH
    -- (iii) `V ≤ SH ≤ PH` (since `K₀ = O_p(↥M) ≤ S`).
    have hV_le_SH : V ≤ SH := by
      rw [hV_def, hSH_def]
      exact Subgroup.map_mono (hK₀_def ▸ OddOrder.Isaacs.Ch01.opCore_le S)
    have hV_le_PH : V ≤ (PH : Subgroup H) := hV_le_SH.trans hSH_le_PH
    -- (iv) Nontrivial `Z(PH)` element `x`, `p`-central.
    haveI : Nontrivial ↥(PH : Subgroup H) :=
      (PH : Subgroup H).nontrivial_iff_ne_bot.mpr hPH_ne_bot
    have hPHpg : IsPGroup p ↥(PH : Subgroup H) := PH.isPGroup'
    have hZPH_nt : Nontrivial (Subgroup.center ↥(PH : Subgroup H)) := hPHpg.center_nontrivial
    obtain ⟨⟨⟨x, hx_mem_PH⟩, hx_center⟩, hx_ne_one⟩ :=
      exists_ne (1 : Subgroup.center ↥(PH : Subgroup H))
    have hx_ne_one' : x ≠ 1 := by
      intro h1; apply hx_ne_one; apply Subtype.ext; apply Subtype.ext; exact h1
    have hx_pcentral : IsPCentral p x := ⟨hx_ne_one', PH, ⟨x, hx_mem_PH⟩, hx_center, rfl⟩
    -- (v) `x ∈ M` (since `x ∈ Z(PH) ⊆ C_H(V) ⊆ N_H(V) = M`).
    have hx_centralizes_V : x ∈ Subgroup.centralizer (V : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv_PH : v ∈ (PH : Subgroup H) := hV_le_PH hv
      have hcomm := (Subgroup.mem_center_iff.mp hx_center) ⟨v, hv_PH⟩
      have := congrArg (Subgroup.subtype (PH : Subgroup H)) hcomm
      simpa [Subgroup.coe_mul] using this
    have hx_in_NV : x ∈ Subgroup.normalizer V := centralizer_le_normalizer V hx_centralizes_V
    have hx_in_M : x ∈ M := hM_eq_NV ▸ hx_in_NV
    -- (vi) `S = PH.subgroupOf M` (a `p`-subgroup of `↥M` containing the Sylow `S`).
    set xM : ↥M := ⟨x, hx_in_M⟩ with hxM_def
    have hPH_subOf_p : IsPGroup p ((PH : Subgroup H).subgroupOf M) :=
      hPHpg.comap_subtype
    have hS_le_PH_subOf : (S : Subgroup ↥M) ≤ (PH : Subgroup H).subgroupOf M := by
      intro s hs
      -- `↑s ∈ SH ≤ PH`.
      have : M.subtype s ∈ SH := ⟨s, hs, rfl⟩
      exact hSH_le_PH this
    have hS_eq : (PH : Subgroup H).subgroupOf M = (S : Subgroup ↥M) :=
      S.is_maximal' hPH_subOf_p hS_le_PH_subOf
    -- `xM ∈ S` since `↑xM = x ∈ PH`, i.e. `xM ∈ PH.subgroupOf M = S`.
    have hxM_in_S : xM ∈ (S : Subgroup ↥M) := by
      rw [← hS_eq, Subgroup.mem_subgroupOf]; exact hx_mem_PH
    -- (vii) `xM ∈ Z(S)`: `xM` centralizes `S` because `x ∈ Z(PH)` centralizes `PH ⊇ SH`.
    have hxM_center_S : (⟨xM, hxM_in_S⟩ : ↥(S : Subgroup ↥M)) ∈
        Subgroup.center (S : Subgroup ↥M) := by
      rw [Subgroup.mem_center_iff]
      intro s
      apply Subtype.ext
      apply Subtype.ext
      -- Reduce to commutation in `H`: `x * ↑s = ↑s * x`.
      have hs_PH : M.subtype (s : ↥M) ∈ (PH : Subgroup H) := by
        have : M.subtype (s : ↥M) ∈ SH := ⟨(s : ↥M), s.2, rfl⟩
        exact hSH_le_PH this
      have hcomm := (Subgroup.mem_center_iff.mp hx_center) ⟨M.subtype (s : ↥M), hs_PH⟩
      have hcomm' := congrArg (Subgroup.subtype (PH : Subgroup H)) hcomm
      simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at hcomm'
      -- `hcomm' : x * ↑s = ↑s * x`; goal is `↑s * x = x * ↑s`.
      simpa [Subgroup.coe_mul, hxM_def] using hcomm'
    have hxM_in_ZS : xM ∈ ZS :=
      ⟨⟨xM, hxM_in_S⟩, hxM_center_S, rfl⟩
    -- (viii) `xM` centralizes `yM` (since `yM ∈ C = C_M(Z(S))` and `xM ∈ Z(S)`).
    have hyM_in_C : yM ∈ C := y₀.2
    have hxM_comm_yM : x * M.subtype yM = M.subtype yM * x := by
      rw [hC_def, Subgroup.mem_centralizer_iff] at hyM_in_C
      have hcomm := hyM_in_C xM hxM_in_ZS
      -- `hcomm : xM * yM = yM * xM` in `↥M`; push to `H`.
      have := congrArg (Subgroup.subtype M) hcomm
      simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at this
      -- `↑xM = x`.
      simpa [hxM_def] using this
    -- (ix) `x` centralizes `↑yM`, hence `x ∈ N_H(YH)`.
    have hx_norm_YH : x ∈ Subgroup.normalizer YH := by
      apply centralizer_le_normalizer YH
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [hYH_def] at hw
      obtain ⟨w₀, hw₀_mem, rfl⟩ := hw
      -- `w₀ ∈ ⟨yM⟩`, so `w₀ = yM ^ k`; `x` commutes with `↑yM` ⇒ with `↑w₀`.
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw₀_mem
      -- `M.subtype (yM ^ k) = (M.subtype yM) ^ k`; `x` commutes with `M.subtype yM`.
      rw [map_zpow]
      -- goal: `(M.subtype yM)^k * x = x * (M.subtype yM)^k`.
      have hcx : Commute x (M.subtype yM) := hxM_comm_yM
      exact (hcx.zpow_right k).symm
    -- (x) Step 6 swapped: `x` `p`-central normalizing nontrivial `q`-subgroup `YH` ⇒ False.
    exact step6_qCentral_not_normalizes_nontrivial_pSubgroup (p := q) (q := p) (a := b) (b := a)
      (Ne.symm hpq) (by rw [hH_card]; ring) hH_nsol hSubgroupsSolvable hx_pcentral
      hYH_ne_bot hYH_q hx_norm_YH
  -- (C) `C` is a `p`-subgroup of `↥M` containing the Sylow `S`, hence `C = S`.
  exact S.is_maximal' hC_pgroup hS_le_C

/-- **§7D Step 8 — full Sylow** (Isaacs L4060-4063): for a `p`-type maximal `M`
and `S ∈ Syl_p(M)`, the image `S.map subtype` is a *full* Sylow `p`-subgroup of
the ambient group `H`.

Textbook proof: by the first part of Step 8, `J(S) ⊴ M`, and since `M` is
maximal with `J(S) ≤ M` nontrivial and `M`-normalized, `N_H(J(S)) = M`.  If
`S_H := S.map subtype` were not a full Sylow of `H`, then `S_H < T` for a
`p`-subgroup `T` (take `T = N_{P_H}(S_H)` for `P_H ∈ Syl_p(H)` containing `S_H`,
which strictly contains `S_H` by the normalizer condition for the nilpotent
group `P_H`); as `J(S_H)` is characteristic in `S_H`, `T` normalizes `J(S_H)`,
so `T ⊆ N_H(J(S_H)) = M`, making `T` a `p`-subgroup of `M` containing the Sylow
`S = M ∩ P_H` — but `T > S_H`, contradiction.  Hence `S_H = P_H` is a full
Sylow. -/
theorem step8_sylow_full
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (_hpq : p ≠ q)
    {a b : ℕ} (_hH_card : Nat.card H = p ^ a * q ^ b)
    (_hH_nsol : ¬ IsSolvable H)
    (_hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_pType : IsPType p M)
    (S : Sylow p ↥M)
    (hJ_normal : (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal) :
    ((S : Subgroup ↥M).map M.subtype) ∈
      Set.range (fun P : Sylow p H => (P : Subgroup H)) := by
  classical
  have hp_prime : p.Prime := Fact.out
  -- `M ≠ ⊥`; `O_p(↥M) ≠ ⊥`.
  have hOp_ne_bot : OddOrder.Isaacs.Ch01.opCore p ↥M ≠ ⊥ := hM_pType.2
  -- `SH := S.map subtype`, a `p`-group; extend to `PH ∈ Syl_p(H)`.
  set SH : Subgroup H := (S : Subgroup ↥M).map M.subtype with hSH_def
  have hSH_p : IsPGroup p SH := S.isPGroup'.map M.subtype
  obtain ⟨PH, hSH_le_PH⟩ := IsPGroup.exists_le_sylow hSH_p
  -- `SH ≠ ⊥` (since `O_p(↥M) ≤ S`, `O_p(↥M).map subtype ≤ SH` nontrivial).
  have hSH_ne_bot : SH ≠ ⊥ := by
    rw [hSH_def]
    intro hbot
    apply hOp_ne_bot
    have hOp_le_S : OddOrder.Isaacs.Ch01.opCore p ↥M ≤ (S : Subgroup ↥M) :=
      OddOrder.Isaacs.Ch01.opCore_le S
    have : (OddOrder.Isaacs.Ch01.opCore p ↥M).map M.subtype = ⊥ :=
      le_bot_iff.mp ((Subgroup.map_mono hOp_le_S).trans (le_of_eq hbot))
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp this
  -- `J(SH) = (J S).map subtype`.
  have hJSH : Subgroup.thompsonJ SH p = (Subgroup.thompsonJ (S : Subgroup ↥M) p).map M.subtype :=
    Subgroup.thompsonJ_map_of_injective M.subtype_injective (S : Subgroup ↥M) p
  -- `J(SH) ≠ ⊥`, `J(SH) ≤ M`.
  have hJSH_ne_bot : Subgroup.thompsonJ SH p ≠ ⊥ := Subgroup.thompsonJ_ne_bot hSH_p hSH_ne_bot
  have hJSH_le_M : Subgroup.thompsonJ SH p ≤ M :=
    (Subgroup.thompsonJ_le SH p).trans (hSH_def ▸ Subgroup.map_subtype_le _)
  -- `M ≤ N_H(J(SH))` from `J(S) ⊴ M` (the image is M-conjugation-invariant).
  have hM_norm_JSH : (M : Subgroup H) ≤ Subgroup.normalizer (Subgroup.thompsonJ SH p) := by
    have h1 : (Subgroup.normalizer (Subgroup.thompsonJ (S : Subgroup ↥M) p)).map M.subtype
        ≤ Subgroup.normalizer ((Subgroup.thompsonJ (S : Subgroup ↥M) p).map M.subtype) :=
      Subgroup.le_normalizer_map M.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr hJ_normal] at h1
    have h3 : (⊤ : Subgroup ↥M).map M.subtype = M := by
      rw [← MonoidHom.range_eq_map, M.range_subtype]
    rw [h3] at h1
    rw [hJSH]; exact h1
  -- `N_H(J(SH)) = M` (maximality).
  have hNJSH_eq_M : Subgroup.normalizer (Subgroup.thompsonJ SH p) = M :=
    maximal_eq_normalizer_of_M_normalizes hM_pType.1 hJSH_ne_bot hJSH_le_M hM_norm_JSH
  -- `S = PH.subgroupOf M`, i.e. `SH = M ⊓ PH`.
  have hPH_subOf_p : IsPGroup p ((PH : Subgroup H).subgroupOf M) := PH.isPGroup'.comap_subtype
  have hS_le_PH_subOf : (S : Subgroup ↥M) ≤ (PH : Subgroup H).subgroupOf M := by
    intro s hs
    have : M.subtype s ∈ SH := ⟨s, hs, rfl⟩
    exact hSH_le_PH this
  have hS_eq : (PH : Subgroup H).subgroupOf M = (S : Subgroup ↥M) :=
    S.is_maximal' hPH_subOf_p hS_le_PH_subOf
  -- Goal: `SH = PH`.  Suffices, then `SH = ↑PH ∈ range`.
  suffices hSH_eq : SH = (PH : Subgroup H) by exact ⟨PH, hSH_eq.symm⟩
  -- Show `SH = PH` by `le_antisymm`; `≤` is `hSH_le_PH`.
  refine le_antisymm hSH_le_PH ?_
  by_contra hPH_not_le
  -- `SH < PH`; use the normalizer condition in the nilpotent `p`-group `↥PH`.
  have hSH_lt_PH : SH < (PH : Subgroup H) := lt_of_le_of_ne hSH_le_PH (by
    intro h; exact hPH_not_le (le_of_eq h.symm))
  -- Work inside `↥PH`: `SH.subgroupOf PH < ⊤`.
  haveI : Group.IsNilpotent ↥(PH : Subgroup H) := PH.isPGroup'.isNilpotent
  have hNC : NormalizerCondition ↥(PH : Subgroup H) :=
    Group.normalizerCondition_of_isNilpotent (G := ↥(PH : Subgroup H))
  have hSH_subOf_lt_top : SH.subgroupOf (PH : Subgroup H) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact absurd (le_antisymm hSH_le_PH htop) (by
      intro h; exact hPH_not_le (le_of_eq h.symm))
  -- `SH.subgroupOf PH < N(SH.subgroupOf PH)`.
  have hlt := hNC (SH.subgroupOf (PH : Subgroup H)) hSH_subOf_lt_top
  -- Get `t : ↥PH` with `t ∈ N(SH.subgroupOf PH)`, `t ∉ SH.subgroupOf PH`.
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt hlt
  -- `↑t ∈ N_H(SH)` (transport normalizer), `↑t ∉ SH`.
  rw [← Subgroup.subgroupOf_normalizer_eq hSH_le_PH, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  set tH : H := (t : H) with htH_def
  -- `tH` normalizes `J(SH)` (since `tH ∈ N_H(SH)`), so `tH ∈ N_H(J(SH)) = M`.
  have htH_norm_JSH : tH ∈ Subgroup.normalizer (Subgroup.thompsonJ SH p) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hconj : (Subgroup.thompsonJ SH p).map (MulAut.conj tH).toMonoidHom
        = Subgroup.thompsonJ SH p :=
      Subgroup.thompsonJ_map_conj_eq_of_mem_normalizer ht_norm
    constructor
    · intro hw
      have : tH * w * tH⁻¹ ∈ (Subgroup.thompsonJ SH p).map (MulAut.conj tH).toMonoidHom :=
        ⟨w, hw, rfl⟩
      rwa [hconj] at this
    · intro hw
      have : tH * w * tH⁻¹ ∈ (Subgroup.thompsonJ SH p).map (MulAut.conj tH).toMonoidHom := by
        rw [hconj]; exact hw
      obtain ⟨z, hz, hz_eq⟩ := this
      have hzw : w = z := by
        have heq : tH * z * tH⁻¹ = tH * w * tH⁻¹ := hz_eq
        -- cancel `tH⁻¹` on the right, then `tH` on the left.
        exact (mul_left_cancel (mul_right_cancel heq)).symm
      rw [hzw]; exact hz
  have htH_in_M : tH ∈ M := hNJSH_eq_M ▸ htH_norm_JSH
  -- `tH ∈ M ∩ PH`, so `(⟨tH, _⟩ : ↥M) ∈ PH.subgroupOf M = S`, i.e. `tH ∈ SH`.
  have htH_in_PH : tH ∈ (PH : Subgroup H) := t.2
  have htM_in_S : (⟨tH, htH_in_M⟩ : ↥M) ∈ (S : Subgroup ↥M) := by
    rw [← hS_eq, Subgroup.mem_subgroupOf]; exact htH_in_PH
  have htH_in_SH : tH ∈ SH := ⟨⟨tH, htH_in_M⟩, htM_in_S, rfl⟩
  -- But `t ∉ SH.subgroupOf PH` means `↑t ∉ SH`, contradiction.
  exact ht_not htH_in_SH

/-- **§7D Step 8** (Isaacs L4045-4063) — *normal `J` and full Sylow for a
`p`-type maximal*.

Let `M` be a `p`-type maximal subgroup and `S ∈ Syl_p(M)`.  Then `J(S) ⊴ M` and
`S` is a full Sylow `p`-subgroup of `G`.

Textbook proof: verify the five hypotheses of the normal-J theorem (Thm 7.6) on
the solvable group `M` — `p`-solvable, `p ≠ 2`, Sylow-2 abelian (trivial since
Step 7), `O_{p'}(M) = O_q(M) = 1` (Step 3), and `C_M(Z(S)) = S` (the latter via
Step 6: `Z(S)` contains a `p`-central element, so a hypothetical order-`q`
subgroup `Y ⊆ C_M(Z(S))` would be normalized by `Z(S)`, contradicting Step 6).
Then `J(S) ⊴ M` by Thm 7.6, and `S` full Sylow since `T > S` would give
`T ⊆ N_G(J(S)) = M`. -/
theorem step8_normalJ_and_fullSylow
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    {M : Subgroup H} (hM_pType : IsPType p M)
    (S : Sylow p ↥M) :
    (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal ∧
      IsPGroup p ((S : Subgroup ↥M).map M.subtype) ∧
      ((S : Subgroup ↥M).map M.subtype) ∈
        Set.range (fun P : Sylow p H => (P : Subgroup H)) := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  -- `M ≠ ⊥`, `M ≠ ⊤`, `M` solvable.
  have hM_ne_bot : M ≠ ⊥ := by
    intro hMbot
    have : Subsingleton ↥M := by rw [hMbot]; infer_instance
    exact hM_pType.2 (Subgroup.eq_bot_of_subsingleton _)
  have hM_ne_top : M ≠ ⊤ := hM_pType.1.ne_top
  haveI hM_sol : IsSolvable ↥M := hSubgroupsSolvable M hM_ne_top
  -- Step 7: both primes odd.
  obtain ⟨hp2, hq2⟩ := step7_p_ne_two_and_q_ne_two hpq hH_card hH_nsol hSubgroupsSolvable
  -- The five normal-J hypotheses on the group `↥M`.
  -- (1) `↥M` is `p`-solvable (it is solvable).
  haveI hM_pSep : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) ↥M := inferInstance
  -- (2) `p ≠ 2`.
  -- (3) Sylow-`2` subgroups abelian (trivial since `2 ∤ |M|`).
  have h2_not_dvd : ¬ (2 : ℕ) ∣ Nat.card ↥M :=
    two_not_dvd_card_subgroup_of_odd_primes hpq hH_card hp2 hq2 M
  have h2abelian : ∀ T : Subgroup ↥M, IsPGroup 2 T → ∀ x y : ↥T, x * y = y * x :=
    sylow2_abelian_of_two_not_dvd h2_not_dvd
  -- (4) `O_{p'}(M) = ⊥`.
  have h_oPiPrime : OddOrder.Isaacs.Ch03.oPiCore {r | r ≠ p} ↥M = ⊥ :=
    oPiCore_pPrime_eq_bot_of_isPType hpq hH_card hSubgroupsSolvable hM_pType
  -- The `normal_J` 4th hypothesis is phrased with `{q | q ≠ p}`; align the set.
  have h_oPiPrime' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} ↥M = ⊥ := h_oPiPrime
  -- (5) `C_M(Z(S)) = S`.
  have h_centralizer : Subgroup.centralizer
      (((Subgroup.center (S : Subgroup ↥M)).map (S : Subgroup ↥M).subtype) : Set ↥M)
      = (S : Subgroup ↥M) :=
    step8_centralizer_center_eq_sylow hpq hH_card hH_nsol hSubgroupsSolvable hM_pType S
  -- Conclude `J(S) ⊴ M` by the normal-J theorem.
  have hJ_normal : (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal :=
    normal_J S hp2 hM_pSep h2abelian h_oPiPrime' h_centralizer
  refine ⟨hJ_normal, ?_, ?_⟩
  · -- (2) `S.map M.subtype` is a `p`-group (image of the `p`-group `S`).
    exact (S.isPGroup'.map M.subtype)
  · -- (3) `S.map M.subtype` is a full Sylow `p`-subgroup of `H` (Step 8 second half).
    exact step8_sylow_full hpq hH_card hH_nsol hSubgroupsSolvable hM_pType S hJ_normal

/-! ### §7D Step 9 — terminal contradiction (Isaacs L4065-4093)

Step 9 is now **proven** (no longer an axiom).  We first land six reusable
helper lemmas, then `step9_core` (the WLOG-`|G|_p > |G|_q` argument), then the
dispatcher `step9_contradiction` that case-splits on which Sylow is larger. -/

/-- In a group of order `p^a q^b` (`p ≠ q` prime), a Sylow `p`-subgroup has
order `p^a`. -/
theorem sylow_p_card_eq_of_paqb
    {H : Type*} [Group H] [Finite H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (P : Sylow p H) :
    Nat.card (P : Subgroup H) = p ^ a := by
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  have hp_ne_dvd_q : ¬ p ∣ q := by
    rw [Nat.prime_dvd_prime_iff_eq hp_prime hq_prime]; exact hpq
  have hfact_p : (p ^ a * q ^ b).factorization p = a := by
    rw [Nat.factorization_mul (pow_ne_zero a hp_prime.ne_zero)
        (pow_ne_zero b hq_prime.ne_zero), Finsupp.add_apply,
        Nat.factorization_pow_self hp_prime,
        Nat.factorization_pow, Finsupp.smul_apply,
        Nat.factorization_eq_zero_of_not_dvd hp_ne_dvd_q, smul_eq_mul, mul_zero, add_zero]
  rw [P.card_eq_multiplicity, hH_card, hfact_p]

theorem sylow_inter_ne_bot_of_card_sq_gt
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (P : Sylow p H) (hcard : Nat.card H < Nat.card (P : Subgroup H) ^ 2)
    (S T : Sylow p H) :
    (S : Subgroup H) ⊓ (T : Subgroup H) ≠ ⊥ := by
  intro hbot
  have hS_card : Nat.card (S : Subgroup H) = Nat.card (P : Subgroup H) :=
    Nat.card_congr (Sylow.equiv S P).toEquiv
  have hT_card : Nat.card (T : Subgroup H) = Nat.card (P : Subgroup H) :=
    Nat.card_congr (Sylow.equiv T P).toEquiv
  have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card
    (S : Subgroup H) (T : Subgroup H)
  rw [hbot] at hprod
  simp only [Subgroup.card_bot, mul_one] at hprod
  rw [hS_card, hT_card] at hprod
  have hST_le : Nat.card ((↑(S : Subgroup H) : Set H) * (↑(T : Subgroup H) : Set H))
      ≤ Nat.card H :=
    Nat.card_le_card_of_injective (Subtype.val) Subtype.val_injective
  rw [hprod] at hST_le
  rw [sq] at hcard
  omega


theorem exists_thompsonJ_ne
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H) :
    ∃ S T : Sylow p H,
      Subgroup.thompsonJ (S : Subgroup H) p ≠ Subgroup.thompsonJ (T : Subgroup H) p := by
  classical
  by_contra h_all_eq
  push Not at h_all_eq
  obtain ⟨hp_dvd, _⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := H)
  have hP_ne_bot : (P : Subgroup H) ≠ ⊥ := Sylow.ne_bot_of_dvd_card hp_dvd P
  set J₀ : Subgroup H := Subgroup.thompsonJ (P : Subgroup H) p with hJ₀_def
  have hJ₀_ne_bot : J₀ ≠ ⊥ := Subgroup.thompsonJ_ne_bot P.isPGroup' hP_ne_bot
  have hJ₀_pgroup : IsPGroup p J₀ :=
    P.isPGroup'.of_injective (Subgroup.inclusion (Subgroup.thompsonJ_le (P : Subgroup H) p))
      (Subgroup.inclusion_injective _)
  -- J₀ normal: conj g maps J₀ to J of the conjugate Sylow = J₀.
  have hJ₀_normal : J₀.Normal := by
    apply Subgroup.Normal.of_conjugate_fixed
    intro g
    change J₀.map (MulAut.conj g).toMonoidHom = J₀
    -- J₀.map (conj g) = J((↑P).map (conj g)) = J(↑(g • P)) = J(↑(g•P)) = J₀.
    have h1 : J₀.map (MulAut.conj g).toMonoidHom
        = Subgroup.thompsonJ ((P : Subgroup H).map (MulAut.conj g).toMonoidHom) p :=
      (Subgroup.thompsonJ_map_of_injective (MulAut.conj g).injective (P : Subgroup H) p).symm
    have h2 : (P : Subgroup H).map (MulAut.conj g).toMonoidHom
        = ((g • P : Sylow p H) : Subgroup H) :=
      Sylow.coe_subgroup_smul.symm
    rw [h1, h2, h_all_eq (g • P) P]
  have hOp_bot : OddOrder.Isaacs.Ch01.opCore p H = ⊥ :=
    opCore_eq_bot_of_simple_nonsolvable inferInstance hH_nsol
  have hJ₀_le_Op : J₀ ≤ OddOrder.Isaacs.Ch01.opCore p H :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hJ₀_pgroup
  rw [hOp_bot, le_bot_iff] at hJ₀_le_Op
  exact hJ₀_ne_bot hJ₀_le_Op

theorem exists_sylowM_of_full_sylow_le
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] {M : Subgroup H}
    (U : Sylow p H) (hUM : (U : Subgroup H) ≤ M) :
    ∃ UM : Sylow p ↥M, (UM : Subgroup ↥M).map M.subtype = (U : Subgroup H) := by
  classical
  have hUsub_p : IsPGroup p ((U : Subgroup H).subgroupOf M) := U.isPGroup'.comap_subtype
  obtain ⟨UM, hUsub_le⟩ := hUsub_p.exists_le_sylow
  refine ⟨UM, ?_⟩
  have hUM_p : IsPGroup p ((UM : Subgroup ↥M).map M.subtype) := UM.isPGroup'.map M.subtype
  have hmap_eq : ((U : Subgroup H).subgroupOf M).map M.subtype = (U : Subgroup H) := by
    rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, M.range_subtype]
    exact inf_eq_right.mpr hUM
  have hU_le : (U : Subgroup H) ≤ (UM : Subgroup ↥M).map M.subtype := by
    rw [← hmap_eq]; exact Subgroup.map_mono hUsub_le
  exact U.is_maximal' hUM_p hU_le

/-- §7D Step 9 bridge: for a `p`-type maximal `M` whose Sylow Thompson subgroups
are `M`-normal (Step 8), any two full Sylow `p`-subgroups of `H` lying in `M`
have the same Thompson subgroup. -/
theorem thompsonJ_eq_of_full_sylow_le_pType
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] {M : Subgroup H}
    (hStep8 : ∀ {N : Subgroup H} (_ : IsPType p N) (S : Sylow p ↥N),
      (Subgroup.thompsonJ (S : Subgroup ↥N) p).Normal)
    (hM_pType : IsPType p M)
    (U V : Sylow p H) (hUM : (U : Subgroup H) ≤ M) (hVM : (V : Subgroup H) ≤ M) :
    Subgroup.thompsonJ (U : Subgroup H) p = Subgroup.thompsonJ (V : Subgroup H) p := by
  classical
  obtain ⟨UM, hUM_eq⟩ := exists_sylowM_of_full_sylow_le U hUM
  obtain ⟨VM, hVM_eq⟩ := exists_sylowM_of_full_sylow_le V hVM
  -- J(↑U) = (J(↑UM)).map subtype.
  have hJU : Subgroup.thompsonJ (U : Subgroup H) p
      = (Subgroup.thompsonJ (UM : Subgroup ↥M) p).map M.subtype := by
    rw [← hUM_eq, Subgroup.thompsonJ_map_of_injective M.subtype_injective]
  have hJV : Subgroup.thompsonJ (V : Subgroup H) p
      = (Subgroup.thompsonJ (VM : Subgroup ↥M) p).map M.subtype := by
    rw [← hVM_eq, Subgroup.thompsonJ_map_of_injective M.subtype_injective]
  rw [hJU, hJV]
  -- Suffices: J(↑UM) = J(↑VM) in ↥M.
  suffices hJeq : Subgroup.thompsonJ (UM : Subgroup ↥M) p
      = Subgroup.thompsonJ (VM : Subgroup ↥M) p by rw [hJeq]
  -- UM, VM are M-conjugate.
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥M) UM VM
  -- J(↑UM) ⊴ M (Step 8).
  have hJUM_normal : (Subgroup.thompsonJ (UM : Subgroup ↥M) p).Normal := hStep8 hM_pType UM
  -- J(↑VM) = J(↑(g • UM)) = J((↑UM).map (conj g)) = (J(↑UM)).map (conj g) = J(↑UM).
  have h1 : Subgroup.thompsonJ (VM : Subgroup ↥M) p
      = Subgroup.thompsonJ ((UM : Subgroup ↥M).map (MulAut.conj g).toMonoidHom) p := by
    rw [← hg]; rfl
  haveI := hJUM_normal
  rw [h1, Subgroup.thompsonJ_map_of_injective (MulAut.conj g).injective]
  -- goal: J(↑UM) = (J(↑UM)).map (conj g); use normality (map = smul = self).
  exact (Subgroup.Normal.conj_smul_eq_self g (Subgroup.thompsonJ (UM : Subgroup ↥M) p)).symm

theorem step9_core
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    (hgt : q ^ b < p ^ a)
    (hStep8 : ∀ {M : Subgroup H} (_ : IsPType p M) (S : Sylow p ↥M),
      (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal) :
    False := by
  classical
  letI : Fintype (Sylow p H) := Fintype.ofFinite _
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  obtain ⟨hp_dvd, hq_dvd⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  -- For P : Sylow p H, |P| = p^a, and |P|² > |H|.
  obtain ⟨P₀⟩ := Sylow.nonempty (p := p) (G := H)
  have hP₀_card : Nat.card (P₀ : Subgroup H) = p ^ a := sylow_p_card_eq_of_paqb hpq hH_card P₀
  have hcard_sq : Nat.card H < Nat.card (P₀ : Subgroup H) ^ 2 := by
    rw [hP₀_card, hH_card, sq]
    have hpa_pos : 0 < p ^ a := pow_pos hp_prime.pos a
    calc p ^ a * q ^ b < p ^ a * p ^ a := by
          exact (Nat.mul_lt_mul_left hpa_pos).mpr hgt
      _ = p ^ a * p ^ a := rfl
  -- (1) all p-Sylow pairs meet nontrivially.
  have hinter : ∀ S T : Sylow p H, (S : Subgroup H) ⊓ (T : Subgroup H) ≠ ⊥ := fun S T =>
    sylow_inter_ne_bot_of_card_sq_gt P₀ hcard_sq S T
  -- (2) ∃ pair with distinct J.
  obtain ⟨S₀, T₀, hJ_ne⟩ := exists_thompsonJ_ne hpq hH_card hH_nsol
  -- (3) maximize |↑S ⊓ ↑T| over distinct-J pairs.
  let distinctJ : Finset (Sylow p H × Sylow p H) :=
    Finset.univ.filter (fun ST =>
      Subgroup.thompsonJ (ST.1 : Subgroup H) p ≠ Subgroup.thompsonJ (ST.2 : Subgroup H) p)
  have hne : distinctJ.Nonempty := ⟨(S₀, T₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ_ne⟩⟩
  obtain ⟨STm, hSTm_mem, hSTm_max⟩ :=
    distinctJ.exists_max_image
      (fun ST => Nat.card ((ST.1 : Subgroup H) ⊓ (ST.2 : Subgroup H) : Subgroup H)) hne
  obtain ⟨S, T⟩ := STm
  have hST_Jne : Subgroup.thompsonJ (S : Subgroup H) p ≠ Subgroup.thompsonJ (T : Subgroup H) p :=
    (Finset.mem_filter.mp hSTm_mem).2
  have hmaxJ : ∀ R₁ R₂ : Sylow p H,
      Subgroup.thompsonJ (R₁ : Subgroup H) p ≠ Subgroup.thompsonJ (R₂ : Subgroup H) p →
      Nat.card ((R₁ : Subgroup H) ⊓ (R₂ : Subgroup H) : Subgroup H) ≤
      Nat.card ((S : Subgroup H) ⊓ (T : Subgroup H) : Subgroup H) := by
    intro R₁ R₂ hR
    exact hSTm_max (R₁, R₂) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR⟩)
  set D : Subgroup H := (S : Subgroup H) ⊓ (T : Subgroup H) with hD_def
  have hD_ne_bot : D ≠ ⊥ := hinter S T
  -- S ≠ T, ↑S ≠ ↑T.
  have hST_ne : S ≠ T := by intro h; exact hST_Jne (by rw [h])
  have hcoeST_ne : (S : Subgroup H) ≠ (T : Subgroup H) := by
    intro h; exact hST_ne (Sylow.ext h)
  -- D < ↑S (else ↑S ≤ ↑T, equal card ⇒ equal, contra).
  have hD_lt_S : D < (S : Subgroup H) := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hDS
    -- D = ↑S ⇒ ↑S ≤ ↑T ⇒ (equal card) ↑S = ↑T.
    have hS_le_T : (S : Subgroup H) ≤ (T : Subgroup H) := by
      rw [hD_def] at hDS; rw [← hDS]; exact inf_le_right
    have hcard_eq : Nat.card (S : Subgroup H) = Nat.card (T : Subgroup H) :=
      Nat.card_congr (Sylow.equiv S T).toEquiv
    exact hcoeST_ne (Subgroup.eq_of_le_of_card_ge hS_le_T (le_of_eq hcard_eq.symm))
  -- (5) N_H(D) < ⊤, maximal M ⊇ N_H(D).
  have hD_ne_top : D ≠ ⊤ := by
    intro h
    rw [h] at hD_lt_S
    exact (lt_irrefl _ (lt_of_lt_of_le hD_lt_S le_top))
  have hND_ne_top : Subgroup.normalizer (D : Set H) ≠ ⊤ := by
    intro hNtop
    have hD_normal : D.Normal := by rw [← Subgroup.normalizer_eq_top_iff]; exact hNtop
    rcases hD_normal.eq_bot_or_eq_top with hb | ht
    · exact hD_ne_bot hb
    · exact hD_ne_top ht
  obtain ⟨M, hM_max, hND_le⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom
      (Subgroup.normalizer (D : Set H))).resolve_left hND_ne_top
  -- D is a p-subgroup.
  have hD_pgroup : IsPGroup p D :=
    S.isPGroup'.of_injective (Subgroup.inclusion (le_of_lt hD_lt_S))
      (Subgroup.inclusion_injective _)
  -- (6) D < N_H(D) ⊓ ↑S.
  have hD_lt_NS : D < Subgroup.normalizer (D : Set H) ⊓ (S : Subgroup H) := by
    have := lt_normalizer_inf_sylow_of_lt S hD_lt_S
    -- normalizer of D (as subgroup) coerces to normalizer (D : Set H)
    exact this
  -- (7) M is p-type.
  -- M ≠ ⊥.
  have hD_le_M : D ≤ M := le_trans Subgroup.le_normalizer hND_le
  have hM_ne_bot : M ≠ ⊥ := by
    intro hbot; rw [hbot, le_bot_iff] at hD_le_M; exact hD_ne_bot hD_le_M
  -- p-central x centralizing D ⇒ x ∈ M.
  obtain ⟨x, hx_pcentral, hx_comm⟩ := exists_isPCentral_centralizing hp_dvd D hD_pgroup
  have hx_in_CD : x ∈ Subgroup.centralizer (D : Set H) := by
    rw [Subgroup.mem_centralizer_iff]; intro v hv; exact (hx_comm v hv).symm
  have hx_in_ND : x ∈ Subgroup.normalizer (D : Set H) := centralizer_le_normalizer D hx_in_CD
  have hx_in_M : x ∈ M := hND_le hx_in_ND
  have hM_pType : IsPType p M := by
    rcases maximal_isPType_xor_isQType hpq hH_card hSubgroupsSolvable hM_max hM_ne_bot with h | h
    · exact h.1
    · exfalso
      exact step5b_pType_no_qCentral (Ne.symm hpq) (a := b) (b := a)
        (by rw [hH_card]; ring) hH_nsol hSubgroupsSolvable h.1 hx_pcentral hx_in_M
  -- (8) Full Sylows U ⊇ M ⊓ ↑S and V ⊇ M ⊓ ↑T of H, contained in M.
  -- Generic: from a p-subgroup K ≤ M, get full Sylow W of H with ↑W ≤ M, K ≤ ↑W.
  have hfull : ∀ K : Subgroup H, K ≤ M → IsPGroup p K →
      ∃ W : Sylow p H, (W : Subgroup H) ≤ M ∧ K ≤ (W : Subgroup H) := by
    intro K hKM hK_p
    -- K.subgroupOf M is a p-group of ↥M; extend to Sylow W_M.
    have hKsub_p : IsPGroup p (K.subgroupOf M) := hK_p.comap_subtype
    obtain ⟨WM, hKsub_le⟩ := hKsub_p.exists_le_sylow
    -- (↑WM).map subtype is a full Sylow of H.
    obtain ⟨_, _, hWM_range⟩ :=
      step8_normalJ_and_fullSylow hpq hH_card hH_nsol hSubgroupsSolvable hM_pType WM
    obtain ⟨W, hW_eq⟩ := hWM_range
    simp only at hW_eq
    -- hW_eq : ↑W = (↑WM).map subtype
    refine ⟨W, ?_, ?_⟩
    · -- ↑W = (↑WM).map subtype ≤ M.
      rw [hW_eq]; exact Subgroup.map_subtype_le _
    · -- K ≤ ↑W: K = (K.subgroupOf M).map subtype ≤ (↑WM).map subtype = ↑W.
      rw [hW_eq]
      have hKmap : (K.subgroupOf M).map M.subtype = K := by
        rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, M.range_subtype]
        exact inf_eq_right.mpr hKM
      rw [← hKmap]; exact Subgroup.map_mono hKsub_le
  -- M ⊓ ↑S and M ⊓ ↑T are p-subgroups ≤ M.
  have hMS_p : IsPGroup p (M ⊓ (S : Subgroup H) : Subgroup H) :=
    S.isPGroup'.of_injective (Subgroup.inclusion (inf_le_right))
      (Subgroup.inclusion_injective _)
  have hMT_p : IsPGroup p (M ⊓ (T : Subgroup H) : Subgroup H) :=
    T.isPGroup'.of_injective (Subgroup.inclusion (inf_le_right))
      (Subgroup.inclusion_injective _)
  obtain ⟨U, hU_le_M, hMS_le_U⟩ := hfull (M ⊓ (S : Subgroup H)) inf_le_left hMS_p
  obtain ⟨V, hV_le_M, hMT_le_V⟩ := hfull (M ⊓ (T : Subgroup H)) inf_le_left hMT_p
  -- (9) ↑U ⊓ ↑S ⊇ N_H(D) ⊓ ↑S ⊋ D, similarly ↑V ⊓ ↑T ⊋ D.
  -- D < N_H(D) ⊓ ↑S ≤ M ⊓ ↑S ≤ ↑U; and N_H(D) ⊓ ↑S ≤ ↑U ⊓ ↑S, so D < ↑U ⊓ ↑S.
  have hNS_le_MS : Subgroup.normalizer (D : Set H) ⊓ (S : Subgroup H) ≤ M ⊓ (S : Subgroup H) :=
    inf_le_inf_right _ hND_le
  have hD_lt_US : D < (U : Subgroup H) ⊓ (S : Subgroup H) := by
    refine lt_of_lt_of_le hD_lt_NS ?_
    -- N_H(D) ⊓ ↑S ≤ ↑U ⊓ ↑S : left ≤ M⊓↑S ≤ ↑U; right ≤ ↑S.
    exact le_inf (le_trans hNS_le_MS hMS_le_U) inf_le_right
  have hD_lt_VT : D < (V : Subgroup H) ⊓ (T : Subgroup H) := by
    -- By symmetry: D = ↑S ⊓ ↑T = ↑T ⊓ ↑S; N_H(D) ⊓ ↑T ⊋ D.
    have hD_lt_T : D < (T : Subgroup H) := by
      refine lt_of_le_of_ne inf_le_right ?_
      intro hDT
      have hT_le_S : (T : Subgroup H) ≤ (S : Subgroup H) := by
        rw [hD_def] at hDT; rw [← hDT]; exact inf_le_left
      have hcard_eq : Nat.card (T : Subgroup H) = Nat.card (S : Subgroup H) :=
        Nat.card_congr (Sylow.equiv T S).toEquiv
      exact hcoeST_ne (Subgroup.eq_of_le_of_card_ge hT_le_S (le_of_eq hcard_eq.symm)).symm
    have hD_lt_NT : D < Subgroup.normalizer (D : Set H) ⊓ (T : Subgroup H) :=
      lt_normalizer_inf_sylow_of_lt T hD_lt_T
    have hNT_le_MT : Subgroup.normalizer (D : Set H) ⊓ (T : Subgroup H) ≤ M ⊓ (T : Subgroup H) :=
      inf_le_inf_right _ hND_le
    refine lt_of_lt_of_le hD_lt_NT ?_
    exact le_inf (le_trans hNT_le_MT hMT_le_V) inf_le_right
  -- (10) J(↑S) = J(↑U) and J(↑T) = J(↑V) by maximality of |D|.
  have hJS_eq_JU :
      Subgroup.thompsonJ (S : Subgroup H) p = Subgroup.thompsonJ (U : Subgroup H) p := by
    by_contra hne
    -- (S, U) distinct-J pair with |↑S ⊓ ↑U| > |D|, contradicting hmaxJ.
    have hle := hmaxJ S U hne
    have hcard_gt : Nat.card (D : Subgroup H)
        < Nat.card ((S : Subgroup H) ⊓ (U : Subgroup H) : Subgroup H) := by
      have : ((U : Subgroup H) ⊓ (S : Subgroup H))
          = ((S : Subgroup H) ⊓ (U : Subgroup H)) := inf_comm _ _
      rw [← this]
      exact Set.Finite.card_lt_card (Set.toFinite _) (hD_lt_US : (D : Set H) ⊂ _)
    omega
  have hJT_eq_JV :
      Subgroup.thompsonJ (T : Subgroup H) p = Subgroup.thompsonJ (V : Subgroup H) p := by
    by_contra hne
    have hle := hmaxJ T V hne
    have hcard_gt : Nat.card (D : Subgroup H)
        < Nat.card ((T : Subgroup H) ⊓ (V : Subgroup H) : Subgroup H) := by
      have : ((V : Subgroup H) ⊓ (T : Subgroup H))
          = ((T : Subgroup H) ⊓ (V : Subgroup H)) := inf_comm _ _
      rw [← this]
      exact Set.Finite.card_lt_card (Set.toFinite _) (hD_lt_VT : (D : Set H) ⊂ _)
    omega
  -- (11) J(↑U) = J(↑V) (both full Sylows ≤ M, M p-type).
  have hJU_eq_JV : Subgroup.thompsonJ (U : Subgroup H) p = Subgroup.thompsonJ (V : Subgroup H) p :=
    thompsonJ_eq_of_full_sylow_le_pType hStep8 hM_pType U V hU_le_M hV_le_M
  -- (12) J(↑S) = J(↑U) = J(↑V) = J(↑T), contradiction.
  exact hST_Jne (hJS_eq_JU.trans (hJU_eq_JV.trans hJT_eq_JV.symm))

/-- **§7D Step 9** (Isaacs L4065-4093) — *the terminal contradiction*.

Now a **theorem** (was an axiom).  Dispatches on whether `|G|_p > |G|_q` or
`|G|_q > |G|_p` (the two are unequal since `p^a = q^b` is impossible for distinct
primes with `a, b ≥ 1`), running `step9_core` with the prime whose Sylow is
larger.  Step 8 (`step8_normalJ_and_fullSylow`) and the partition
(`maximal_isPType_or_isQType`) are derived internally for that prime. -/
theorem step9_contradiction
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {a b : ℕ} (hH_card : Nat.card H = p ^ a * q ^ b)
    (hH_nsol : ¬ IsSolvable H)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K)
    (_hp2 : p ≠ 2) (_hq2 : q ≠ 2) :
    False := by
  classical
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  obtain ⟨hp_dvd, hq_dvd⟩ :=
    p_and_q_dvd_card_of_simple_nonsolvable hpq inferInstance hH_nsol (dvd_of_eq hH_card)
  -- a, b ≥ 1.
  have ha_pos : 0 < a := by
    by_contra h; push Not at h
    interval_cases a
    rw [pow_zero, one_mul] at hH_card
    -- p ∣ |H| = q^b ⇒ p = q.
    rw [hH_card] at hp_dvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp (hp_prime.dvd_of_dvd_pow hp_dvd))
  have hb_pos : 0 < b := by
    by_contra h; push Not at h
    interval_cases b
    rw [pow_zero, mul_one] at hH_card
    rw [hH_card] at hq_dvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp
      (hq_prime.dvd_of_dvd_pow hq_dvd)).symm
  -- p^a ≠ q^b.
  have hpa_ne_qb : p ^ a ≠ q ^ b := by
    intro heq
    -- p ∣ p^a = q^b ⇒ p = q.
    have : p ∣ q ^ b := heq ▸ dvd_pow_self p ha_pos.ne'
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp (hp_prime.dvd_of_dvd_pow this))
  have hH_card_swap : Nat.card H = q ^ b * p ^ a := by rw [hH_card]; ring
  rcases lt_or_gt_of_ne hpa_ne_qb with hlt | hgt
  · -- p^a < q^b: run core with (q, p) swapped.
    -- need hStep8 for q-type and partition for q.
    have hStep8' : ∀ {M : Subgroup H} (_ : IsPType q M) (S : Sylow q ↥M),
        (Subgroup.thompsonJ (S : Subgroup ↥M) q).Normal := by
      intro M hM S
      exact (step8_normalJ_and_fullSylow (Ne.symm hpq) hH_card_swap hH_nsol
        hSubgroupsSolvable hM S).1
    exact step9_core (Ne.symm hpq) hH_card_swap hH_nsol hSubgroupsSolvable hlt hStep8'
  · -- p^a > q^b: run core directly.
    have hStep8' : ∀ {M : Subgroup H} (_ : IsPType p M) (S : Sylow p ↥M),
        (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal := by
      intro M hM S
      exact (step8_normalJ_and_fullSylow hpq hH_card hH_nsol hSubgroupsSolvable hM S).1
    exact step9_core hpq hH_card hH_nsol hSubgroupsSolvable hgt hStep8'

/-- **§7D — no finite simple non-solvable group of order `p^a q^b`** (Isaacs
§7D, Thm 7.8 contradiction).

Now a **theorem**, threading the per-step decomposition:
* Step 2 (`step2_*`, proven) — complementary Sylow product.
* Step 3 (`step3_not_both_opCore_ne_bot`, axiom) + partition
  (`maximal_isPType_or_isQType`, proven) — `p`-type XOR `q`-type dichotomy.
* Steps 4-6 (`step4_*`, `step6_*`, axioms) — `q`-central elements normalize no
  nontrivial `p`-subgroup.
* Step 7 (`step7_p_ne_two_and_q_ne_two`, proven from Step 6) — both primes odd.
* Step 8 (`step8_normalJ_and_fullSylow`, axiom) — `J(S) ⊴ M` for `p`-type `M`.
* Step 9 (`step9_contradiction`, axiom) — terminal contradiction. -/
theorem noNonsolvableSimplePaQb.{u}
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (H : Type u) [Group H] [Finite H]
    (hH_simple : IsSimpleGroup H)
    (hH_nsol : ¬ IsSolvable H)
    (hH_order : ∃ a b : ℕ, Nat.card H ∣ p ^ a * q ^ b)
    (hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K) :
    False := by
  classical
  haveI := hH_simple
  -- Upgrade |H| ∣ p^a q^b to an exact equality |H| = p^a' q^b'.
  obtain ⟨a, b, hH_dvd⟩ := hH_order
  obtain ⟨a', b', hH_card⟩ : ∃ a' b' : ℕ, Nat.card H = p ^ a' * q ^ b' :=
    ⟨_, _, card_eq_pow_mul_pow_of_dvd Fact.out Fact.out hpq Nat.card_pos.ne' hH_dvd⟩
  -- Step 7: p, q both odd.
  obtain ⟨hp2, hq2⟩ :=
    step7_p_ne_two_and_q_ne_two hpq hH_card hH_nsol hSubgroupsSolvable
  -- Partition: every maximal (≠ ⊥) is p-type or q-type.
  have hPartition : ∀ {M : Subgroup H}, IsCoatom M → M ≠ ⊥ →
      IsPType p M ∨ IsQType q M := by
    intro M hM_max hM_ne_bot
    exact maximal_isPType_or_isQType hpq hH_card hM_max hM_ne_bot
      (hSubgroupsSolvable M hM_max.1)
  -- Step 8 packaged.
  have hStep8 : ∀ {M : Subgroup H} (_ : IsPType p M) (S : Sylow p ↥M),
      (Subgroup.thompsonJ (S : Subgroup ↥M) p).Normal := by
    intro M hM_pType S
    exact (step8_normalJ_and_fullSylow hpq hH_card hH_nsol hSubgroupsSolvable hM_pType S).1
  -- Step 9: terminal contradiction.
  exact step9_contradiction hpq hH_card hH_nsol hSubgroupsSolvable hp2 hq2

/-- **Isaacs Thm 7.8** (Burnside `p^a q^b` solvability).

> If `|G| = p^a * q^b` for primes `p, q`, then `G` is solvable.

The textbook proof (Isaacs p.219-222) is the character-free
**Goldschmidt-Bender-Matsuyama 9-step argument**: assume `G` is a minimum
counterexample (non-solvable group of minimum order `p^a q^b`).  Steps 1-3
establish that `G` is simple and identify maximal subgroups of `p`-type or
`q`-type; Steps 4-7 develop `p`-central element machinery and apply
Matsuyama 2.13 to force `p, q` odd; Step 8 applies the **normal-J theorem
(Thm 7.6)** to get `J(S) ⊴ M` for `S ∈ Syl_p(M)`; Step 9 derives a
contradiction from `J(S) ⊴ M` together with Thompson factorization
properties of `M`.

**Implementation strategy**: the actual 9-step argument is encapsulated in
the local axiom `noNonsolvableSimplePaQb` (issue 0032).  We carry out the
strong-induction-on-`Nat.card` reduction, peel off the simplicity reduction
via `isSimpleGroup_of_minCounterexample`, then invoke the axiom.

⚠ **書籍どおり `p ≠ q` を仮定しない** (2026-07-19 に一般化)。Isaacs 7.8 は
「Let `G` be a finite group of order `p^a q^b`, where `p` and `q` are primes」とだけ言い
相異性を課さない。`p = q` は `|G| = p^(a+b)` すなわち `p`-群の場合で、冪零ゆえ可解
(`IsPGroup.isNilpotent` + `IsNilpotent.to_isSolvable`) — 下の第 1 分岐がそれ。
これにより下流 (`ForwardFromCh03`) が素因子 1 個のときに**偽の第 2 素数を捏造して**
`hpq` を満たす必要がなくなった。 -/
theorem burnside_p_pow_q_pow.{u}
    {G : Type u} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hG_order : ∃ a b : ℕ, Nat.card G = p ^ a * q ^ b) :
    IsSolvable G := by
  rcases eq_or_ne p q with rfl | hpq
  · -- `p = q`: `|G| = p^(a+b)` is a `p`-group, hence nilpotent, hence solvable.
    obtain ⟨a, b, hab⟩ := hG_order
    haveI hGp : IsPGroup p G := IsPGroup.of_card (n := a + b) (by rw [hab, pow_add])
    haveI : Group.IsNilpotent G := hGp.isNilpotent
    infer_instance
  classical
  -- Strong induction on `Nat.card` via an explicit motive over arbitrary finite
  -- groups whose order divides `|G|`.
  let motive : ℕ → Prop := fun n =>
    ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H ∣ Nat.card G → Nat.card H = n → IsSolvable H
  suffices hmain : motive (Nat.card G) by
    exact hmain G dvd_rfl rfl
  refine Nat.strong_induction_on (Nat.card G) ?_
  intro n ih H _ _ hH_dvd hH_card
  -- Apply the minimum-counterexample contradiction.
  by_contra hH_nsol
  have hG_pos : 0 < Nat.card G := Nat.card_pos
  have hH_pos : 0 < Nat.card H := Nat.pos_of_dvd_of_pos hH_dvd hG_pos
  -- Subgroup orders divide the ambient order; use Lagrange + IH.
  -- Every proper subgroup (not necessarily normal) is solvable.
  have hSubgroupsSolvable : ∀ K : Subgroup H, K ≠ ⊤ → IsSolvable K := by
    intro K hK_top
    have hK_dvd_H : Nat.card K ∣ Nat.card H := K.card_subgroup_dvd_card
    have hK_dvd_G : Nat.card K ∣ Nat.card G := hK_dvd_H.trans hH_dvd
    have hK_le : Nat.card K ≤ Nat.card H := Nat.le_of_dvd hH_pos hK_dvd_H
    have hK_ne : Nat.card K ≠ Nat.card H := fun h_eq =>
      hK_top (Subgroup.eq_top_of_card_eq _ h_eq)
    have hK_lt : Nat.card K < n :=
      (lt_of_le_of_ne hK_le hK_ne).trans_eq hH_card
    exact ih (Nat.card K) hK_lt K hK_dvd_G rfl
  -- Restriction of the above to normal proper subgroups.
  have hN_solvable :
      ∀ N : Subgroup H, N ≠ ⊤ → N.Normal → IsSolvable N := fun N hN _ =>
    hSubgroupsSolvable N hN
  -- Quotient orders divide the ambient order; use index-bound + IH.
  have hQ_solvable :
      ∀ (N : Subgroup H) [N.Normal], N ≠ ⊥ → IsSolvable (H ⧸ N) := by
    intro N hN_norm hN_bot
    have hQ_dvd_H : Nat.card (H ⧸ N) ∣ Nat.card H := N.card_quotient_dvd_card
    have hQ_dvd_G : Nat.card (H ⧸ N) ∣ Nat.card G := hQ_dvd_H.trans hH_dvd
    -- |H| = |H/N| * |N| with |N| ≥ 2 ⇒ |H/N| < |H|.
    have hN_card_two : 1 < Nat.card N := N.one_lt_card_iff_ne_bot.mpr hN_bot
    have hH_eq : Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hQ_pos : 0 < Nat.card (H ⧸ N) :=
      Nat.pos_of_dvd_of_pos hQ_dvd_H hH_pos
    have hQ_lt_H : Nat.card (H ⧸ N) < Nat.card H := by
      calc Nat.card (H ⧸ N)
          = Nat.card (H ⧸ N) * 1 := (Nat.mul_one _).symm
        _ < Nat.card (H ⧸ N) * Nat.card N :=
            Nat.mul_lt_mul_of_pos_left hN_card_two hQ_pos
        _ = Nat.card H := hH_eq.symm
    have hQ_lt : Nat.card (H ⧸ N) < n := hQ_lt_H.trans_eq hH_card
    exact ih (Nat.card (H ⧸ N)) hQ_lt (H ⧸ N) hQ_dvd_G rfl
  -- H is nontrivial: |H| = n.  If n = 1 then H is trivial which is solvable
  -- (contradicting hH_nsol).
  haveI hH_nontriv : Nontrivial H := by
    by_contra h_not_nontriv
    rw [not_nontrivial_iff_subsingleton] at h_not_nontriv
    exact hH_nsol inferInstance
  -- Step 1 reduction: H is simple.
  have hH_simple : IsSimpleGroup H :=
    isSimpleGroup_of_minCounterexample hH_nsol hN_solvable hQ_solvable
  -- Order divides p^a q^b: extract a',b' such that Nat.card H ∣ p^a' q^b'.
  obtain ⟨a, b, hG_card⟩ := hG_order
  have hH_dvd_paqb : ∃ a' b' : ℕ, Nat.card H ∣ p ^ a' * q ^ b' :=
    ⟨a, b, hG_card ▸ hH_dvd⟩
  -- Invoke the §7D core axiom.
  exact noNonsolvableSimplePaQb hpq H hH_simple hH_nsol hH_dvd_paqb
    hSubgroupsSolvable


end OddOrder.Isaacs.Ch07

