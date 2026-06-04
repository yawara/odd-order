/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.Ch1_Preliminary.S05_NarrowPGroups
import OddOrder.BG.Ch2_Uniqueness.S07_Transitivity
import OddOrder.BG.Ch2_Uniqueness.S08_FittingOfMaximal
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.GroupTheory.AInvariantPiSubgroups
import OddOrder.GroupTheory.PRank
import OddOrder.GroupTheory.OmegaSubgroup
import OddOrder.GroupTheory.ElementaryAbelianFamily
import OddOrder.GroupTheory.NarrowPGroup

/-!
# BG §9: The Uniqueness Theorem

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter II §9 (pp. 62-66), mmd `references/bg/local-analysis.mmd`
L2486-2630, **6 結果** (Thm 9.1, 9.6 + Cor 9.2, 9.3 + Lem 9.4, 9.5)。

§9 は **Uniqueness Theorem (Thm 9.6)** を完成させる線形チェーン 9.1→9.2→9.3→9.4→9.5→9.6。
結論はすべて「`K ∈ 𝒰`」(= `IsUniquelyMaximal`)。新規定義は無し (𝒰/ℋ/F(M)/rank を使用)。

## 記法 (BG → repo)

- `M ∈ ℳ` = `M ∈ maximalSubgroups G`; `𝒰` = `IsUniquelyMaximal`。
- `ℰ_p(M)` (M の elem-ab p-部分群) = `B.IsElementaryAbelian p ∧ B ≤ M`。
- `ℋ_G(B;p')` = `hInvariant ⊤ B {p}ᶜ`; `⟨·⟩` = `sSup`。
- `F(M)` = `S08.fittingInG M`; `m(A)`/`r(K)` = `rank ↥·`; `r_p(·)` = `pRank ↥· p`。
- `SCN₃(p)` = `S07.scn3Global p G`; `ℰ²(G)` = `elemAbelianOfRank G p 2`;
  `ℰ*(G)` = `IsMaximalElementaryAbelian p`。
- 固定 G は `(hG : IsMinimalSimpleOdd G)` を明示 thread。

## proof は後続

faithful statement + `sorry`。proof は §7 (Thm 7.4/7.6) + §8 (Thm 8.1) + §6 Thm 6.2
+ §5 Lem 5.1 + §4 (Thm 4.20, Cor 4.19) + Prop 1.16 に依存 (foundation-first)。

## Lane C gate map for §4/§5 obligations

* 9.1 consumes BG Thm 8.1 and BG Thm 4.20 at mmd L2533. It does not directly consume
  BG Lem 4.13, BG Thm 4.16, or the §5 narrow classification theorems.
* 9.3 uses BG Lem 4.5 at mmd L2549, then Cor 9.2. This is p-group infrastructure,
  not the Blackburn endpoint.
* 9.5 consumes BG Thm 7.6 + Thm 7.4 at mmd L2579, Cor 4.19 at L2605, and Thm 4.20 at
  L2615. Its `SCN₃(p)` input is already explicit.
* 9.6 is the one direct §5 gate in §9: mmd L2629 uses BG Lem 5.1 to choose
  `A ∈ SCN₃(P)`. That gate depends on BG Lem 4.7's hard direction, not on Thm 4.16.
  Keep Blackburn/narrow type-classification assumptions downstream in §10+.
-/

namespace OddOrder.BG.Ch2.S09

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- `C_G(x) < ⊤` for `x ≠ 1` in a minimal simple group (`Z(G) = 1`). -/
private theorem centralizer_singleton_lt_top [Finite G] (hG : IsMinimalSimpleOdd G) {x : G}
    (hx : x ≠ (1 : G)) : Subgroup.centralizer ({x} : Set G) < ⊤ := by
  have hZbot : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact absurd (isSolvable_of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm) hG.notSolvable
  rw [lt_top_iff_ne_top]
  intro htop
  refine hx (Subgroup.mem_bot.mp (hZbot ▸ ?_))
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (htop ▸ Subgroup.mem_top g) x (Set.mem_singleton x)).symm

/-- If `L` has a unique containing maximal subgroup and `x` centralizes `L`, then the
centralizer of any nontrivial such `x` lies in that unique maximal subgroup. -/
private theorem centralizer_singleton_le_uniqueMaximalSubgroup_of_mem_centralizer [Finite G]
    (hG : IsMinimalSimpleOdd G) {L : Subgroup G} (hL : IsUniquelyMaximal L)
    {x : G} (hxL : x ∈ Subgroup.centralizer (L : Set G)) (hx : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ hL.uniqueMaximalSubgroup := by
  classical
  have hCGlt : Subgroup.centralizer ({x} : Set G) < ⊤ :=
    centralizer_singleton_lt_top hG hx
  have hLleCG : L ≤ Subgroup.centralizer ({x} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact (Subgroup.mem_centralizer_iff.mp hxL l hl).symm
  obtain ⟨N, hNco, hCGleN⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.centralizer ({x} : Set G))).resolve_left hCGlt.ne
  have hLleN : L ≤ N := hLleCG.trans hCGleN
  have hN_eq : N = hL.uniqueMaximalSubgroup :=
    hL.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hNco hLleN
  exact hCGleN.trans (le_of_eq hN_eq)

/-- **BG Theorem 9.1** (mmd L2492): `p` prime, `M ∈ ℳ`, `B ∈ ℰ_p(M)` noncyclic で、
(a) 任意の `b ∈ B^#` で `C_G(b) ⊆ M`、または (b) `⟨ℋ_G(B;p')⟩ ⊆ M`、のいずれかなら `B ∈ 𝒰`。

Proof gate: mmd L2533 invokes BG Thm 8.1 and BG Thm 4.20 after Eq. (9.5). Do not add
BG Lem 4.13, BG Thm 4.16, or §5 narrow hypotheses to this theorem. -/
theorem noncyclic_isUniquelyMaximal_of_centralizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {B : Subgroup G} (hBea : B.IsElementaryAbelian p) (hBle : B ≤ M) (hBnc : ¬ IsCyclic ↥B)
    (hcase :
      (∀ b : G, b ∈ B → b ≠ 1 → Subgroup.centralizer {b} ≤ M) ∨
      sSup (hInvariant ⊤ B {p}ᶜ) ≤ M) :
    IsUniquelyMaximal B := by
  sorry

/-- **BG Corollary 9.2** (mmd L2541): `L ∈ 𝒰`, `K ≤ C_G(L)`, `r(K) ≥ 2` ⇒ `K ∈ 𝒰`。 -/
theorem isUniquelyMaximal_of_le_centralizer_of_two_le_rank [Finite G] (hG : IsMinimalSimpleOdd G)
    {L K : Subgroup G} (hL : IsUniquelyMaximal L) (hKL : K ≤ Subgroup.centralizer (L : Set G))
    (hr : 2 ≤ rank ↥K) :
    IsUniquelyMaximal K := by
  classical
  obtain ⟨p, hp, A, hAea, hAK, hAnc⟩ :=
    exists_isElementaryAbelian_not_isCyclic_le_of_two_le_rank K hr
  haveI : Fact p.Prime := ⟨hp⟩
  let M : Subgroup G := hL.uniqueMaximalSubgroup
  have hKleM : K ≤ M := by
    intro k hk
    by_cases hk1 : k = 1
    · simp [M, hk1]
    · have hkL : k ∈ Subgroup.centralizer (L : Set G) := hKL hk
      have hCGleM : Subgroup.centralizer ({k} : Set G) ≤ M :=
        centralizer_singleton_le_uniqueMaximalSubgroup_of_mem_centralizer hG hL hkL hk1
      exact hCGleM (by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        rfl)
  have hAleM : A ≤ M := hAK.trans hKleM
  have hcent : ∀ b : G, b ∈ A → b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ M := by
    intro b hb hb1
    have hbL : b ∈ Subgroup.centralizer (L : Set G) := hKL (hAK hb)
    exact centralizer_singleton_le_uniqueMaximalSubgroup_of_mem_centralizer hG hL hbL hb1
  have hAU : IsUniquelyMaximal A :=
    noncyclic_isUniquelyMaximal_of_centralizer_le hG
      (hM := hL.uniqueMaximalSubgroup_isCoatom) hAea hAleM hAnc (Or.inl hcent)
  have hKlt : K < ⊤ :=
    lt_of_le_of_lt hKleM hL.uniqueMaximalSubgroup_isCoatom.1.lt_top
  exact hAU.of_le_of_lt_top hAK hKlt

/-- A noncyclic `p`-subgroup of a minimal odd simple group has rank at least two.

This is the small rank bridge used at the end of BG Corollary 9.3: once the
intermediate rank-three elementary abelian subgroup has been put in `𝒰`, Corollary 9.2
can be applied to the original noncyclic `p`-subgroup. -/
private theorem two_le_rank_of_noncyclic_pSubgroup [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {B : Subgroup G} (hBp : IsPGroup p B)
    (hBnc : ¬ IsCyclic ↥B) :
    2 ≤ rank ↥B := by
  classical
  have hp_dvd_B : p ∣ Nat.card B := by
    obtain ⟨n, hn⟩ := hBp.exists_card_eq
    have hnpos : 0 < n := by
      by_contra hn0
      have hn_zero : n = 0 := by omega
      have hBcard_one : Nat.card B = 1 := by simpa [hn_zero] using hn
      haveI : Subsingleton ↥B := Finite.card_le_one_iff_subsingleton.mp (by omega)
      exact hBnc isCyclic_of_subsingleton
    rw [hn]
    exact dvd_pow_self p hnpos.ne'
  have hp_odd : Odd p :=
    hG.odd.of_dvd_nat (hp_dvd_B.trans (Subgroup.card_subgroup_dvd_card B))
  obtain ⟨E, hEea, hEcard⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
      hBp hp_odd hBnc
  have hElog : 2 ≤ Nat.log p (Nat.card E) := by
    rw [hEcard, Nat.log_pow (Fact.out : p.Prime).one_lt]
  have h2pRank : 2 ≤ pRank ↥B p := hElog.trans (le_pRank E hEea)
  exact h2pRank.trans (pRank_le_rank (G := ↥B) p)

/-- In a finite `p`-group, elementary abelian subgroups for a different prime have
zero logarithmic size. This is the local arithmetic bridge behind turning BG rank
of a `p`-group back into the same-prime `pRank`. -/
private theorem pRank_eq_zero_of_isPGroup_of_ne_prime {H : Type*} [Group H] [Finite H]
    {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p) (hH : IsPGroup p H) :
    pRank H q = 0 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  apply le_antisymm ?_ (Nat.zero_le _)
  rw [pRank_le_iff]
  intro E hE
  have hE_p : IsPGroup p E := hH.to_subgroup E
  have hE_q : IsPGroup q E := hE.isPGroup
  obtain ⟨a, ha⟩ := hE_p.exists_card_eq
  obtain ⟨b, hb⟩ := hE_q.exists_card_eq
  have hcard_one : Nat.card E = 1 := by
    by_contra hne
    have hbpos : 0 < b := by
      by_contra hb0
      have hb_zero : b = 0 := by omega
      have hEcard_one : Nat.card E = 1 := by
        simpa [hb_zero] using hb
      exact hne hEcard_one
    have hq_dvd_card : q ∣ Nat.card E := by
      rw [hb]
      exact dvd_pow_self q hbpos.ne'
    have hq_dvd_powa : q ∣ p ^ a := by
      rwa [ha] at hq_dvd_card
    have hq_dvd_p : q ∣ p := hq.dvd_of_dvd_pow hq_dvd_powa
    have hqeqp : q = p :=
      (Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp hq_dvd_p
    exact hqp hqeqp
  simp [hcard_one]

/-- A finite `p`-group has no rank contribution from primes other than `p`. -/
private theorem rank_le_pRank_of_isPGroup {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hH : IsPGroup p H) :
    rank H ≤ pRank H p := by
  rw [rank_le_iff]
  intro q hq
  by_cases hqp : q = p
  · subst q
    exact le_rfl
  · rw [pRank_eq_zero_of_isPGroup_of_ne_prime (H := H) (p := p) (q := q) hq hqp hH]
    exact Nat.zero_le _

/-- In a finite `p`-group, a rank-three lower bound is witnessed at the same prime `p`. -/
private theorem three_le_pRank_of_isPGroup_of_three_le_rank {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hH : IsPGroup p H) (hr : 3 ≤ rank H) :
    3 ≤ pRank H p :=
  hr.trans (rank_le_pRank_of_isPGroup hH)

/-- A positive `pRank` lower bound forces `p` to divide the group order. -/
private theorem mem_primeFactors_card_of_pos_pRank {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hpos : 0 < pRank H p) :
    p ∈ (Nat.card H).primeFactors := by
  obtain ⟨E, hEea, hElog⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := H) (p := p) (n := 1) (by norm_num) hpos
  have hEp : IsPGroup p E := hEea.isPGroup
  have hp_dvd_E : p ∣ Nat.card E := by
    obtain ⟨n, hn⟩ := hEp.exists_card_eq
    have hnpos : 0 < n := by
      by_contra hn0
      have hn_zero : n = 0 := by omega
      rw [hn_zero, pow_zero] at hn
      rw [hn] at hElog
      norm_num at hElog
    rw [hn]
    exact dvd_pow_self p hnpos.ne'
  exact Nat.mem_primeFactors.mpr
    ⟨Fact.out, hp_dvd_E.trans (Subgroup.card_subgroup_dvd_card E), Nat.card_pos.ne'⟩

/-- Extend an elementary abelian subgroup contained in `H` to one maximal inside `H`. -/
private theorem exists_isMaxElemAbelianIn_ge_of_le [Finite G] {p : ℕ}
    {E H : Subgroup G} (hE : E.IsElementaryAbelian p) (hEH : E ≤ H) :
    ∃ A₀ : Subgroup G, E ≤ A₀ ∧ S08.isMaxElemAbelianIn p A₀ H := by
  obtain ⟨A₀, hEA₀, hA₀max⟩ :=
    Finite.exists_le_maximal
      (p := fun A₀ : Subgroup G => A₀.IsElementaryAbelian p ∧ A₀ ≤ H) ⟨hE, hEH⟩
  refine ⟨A₀, hEA₀, hA₀max.1.1, hA₀max.1.2, ?_⟩
  intro B hB hBH hA₀B
  exact le_antisymm (hA₀max.2 ⟨hB, hBH⟩ hA₀B) hA₀B

/-- A `pRank ≥ 3` subgroup has a rank-three maximal elementary abelian subgroup inside it. -/
private theorem exists_isMaxElemAbelianIn_rank_three_of_three_le_pRank [Finite G]
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} (h3 : 3 ≤ pRank ↥H p) :
    ∃ A₀ : Subgroup G, S08.isMaxElemAbelianIn p A₀ H ∧ 3 ≤ rank ↥A₀ := by
  obtain ⟨E, hEea, hElog⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥H) (p := p) (n := 3) (by norm_num) h3
  let EG : Subgroup G := E.map H.subtype
  have hEG_ea : EG.IsElementaryAbelian p := by
    change (E.map H.subtype).IsElementaryAbelian p
    exact Subgroup.IsElementaryAbelian.map H.subtype_injective hEea
  have hEGH : EG ≤ H := by
    change E.map H.subtype ≤ H
    exact Subgroup.map_subtype_le E
  obtain ⟨A₀, hEGA₀, hA₀max⟩ := exists_isMaxElemAbelianIn_ge_of_le hEG_ea hEGH
  have hEGlog : 3 ≤ Nat.log p (Nat.card EG) := by
    change 3 ≤ Nat.log p (Nat.card (E.map H.subtype))
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hElog
  have h3EG : 3 ≤ pRank ↥EG p := hEGlog.trans hEG_ea.log_card_le_pRank
  have h3A₀p : 3 ≤ pRank ↥A₀ p :=
    h3EG.trans
      (pRank_le_of_injective (f := Subgroup.inclusion hEGA₀)
        (Subgroup.inclusion_injective hEGA₀))
  exact ⟨A₀, hA₀max, h3A₀p.trans (pRank_le_rank (G := ↥A₀) p)⟩

/-- An abelian rank-three `p`-subgroup has centralizer of `pRank` at least three. -/
private theorem three_le_pRank_centralizer_of_isMulCommutative_of_isPGroup_of_three_le_rank
    [Finite G] {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAab : IsMulCommutative A) (hAp : IsPGroup p A) (hr : 3 ≤ rank ↥A) :
    3 ≤ pRank ↥(Subgroup.centralizer (A : Set G)) p := by
  have h3A : 3 ≤ pRank ↥A p := three_le_pRank_of_isPGroup_of_three_le_rank hAp hr
  have hA_le_C : A ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (isMulCommutative_iff.mp hAab ⟨y, hy⟩ ⟨x, hx⟩)
  exact h3A.trans
    (pRank_le_of_injective (f := Subgroup.inclusion hA_le_C)
      (Subgroup.inclusion_injective hA_le_C))

/-- Rank at least two rules out cyclicity. -/
private theorem not_isCyclic_of_two_le_rank [Finite G] {A : Subgroup G}
    (hr : 2 ≤ rank ↥A) :
    ¬ IsCyclic ↥A := by
  obtain ⟨q, hq, E, _hEea, hEA, hEnc⟩ :=
    exists_isElementaryAbelian_not_isCyclic_le_of_two_le_rank A hr
  intro hAcyc
  exact hEnc
    (isCyclic_of_injective (Subgroup.inclusion hEA)
      (Subgroup.inclusion_injective hEA))

/-- A finite odd `p`-group of `pRank` at least three has a normal elementary abelian
subgroup of order `p^2`.

This is the local S09 package of BG Lemma 5.1(b) followed by BG Lemma 1.22: first get a
normal elementary abelian subgroup of order `p^3`, then take a normal subgroup of order
`p^2` inside it. -/
private theorem exists_normal_isElementaryAbelian_card_prime_sq_of_three_le_pRank
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hR : IsPGroup p R) (h3 : 3 ≤ pRank R p) :
    ∃ D : Subgroup R, D.Normal ∧ D.IsElementaryAbelian p ∧ Nat.card D = p ^ 2 := by
  obtain ⟨A, hA⟩ := OddOrder.BG.Ch1.S05.scn3_nonempty_of_three_le_pRank hp hR h3
  obtain ⟨B, hB_normal, hB_elem, hBcard⟩ :=
    OddOrder.BG.Ch1.S05.exists_normal_isElementaryAbelian_card_prime_cube_of_scn3 hR hA
  haveI : B.Normal := hB_normal
  have hB_dvd : p ^ 2 ∣ Nat.card B := by
    rw [hBcard]
    exact pow_dvd_pow p (by norm_num : 2 ≤ 3)
  obtain ⟨D, hD_normal, hD_le_B, hDcard⟩ :=
    OddOrder.BG.Ch1.S01.normal_subgroup_card_pow_le_of_pGroup
      (G := R) (p := p) hR (N := B) (r := 2) hB_dvd
  have hD_elem : D.IsElementaryAbelian p := by
    have hD_sub_elem : (D.subgroupOf B).IsElementaryAbelian p :=
      hB_elem.to_subgroup (D.subgroupOf B)
    exact IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hD_le_B)
      hD_sub_elem
  exact ⟨D, hD_normal, hD_elem, hDcard⟩

/-- In a minimal odd group, a rank-three `p`-subgroup forces `p` to be odd. -/
private theorem odd_prime_of_isPGroup_of_three_le_rank [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAp : IsPGroup p A) (hmA : 3 ≤ rank ↥A) :
    Odd p := by
  classical
  have h3pRankA : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp hmA
  obtain ⟨A₀, hA₀ea, hA₀log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥A) (p := p) (n := 3) (by norm_num) h3pRankA
  let Astar : Subgroup G := A₀.map A.subtype
  have hAstar_ea : Astar.IsElementaryAbelian p := by
    change (A₀.map A.subtype).IsElementaryAbelian p
    exact Subgroup.IsElementaryAbelian.map A.subtype_injective hA₀ea
  have hAstar_log : 3 ≤ Nat.log p (Nat.card Astar) := by
    change 3 ≤ Nat.log p (Nat.card (A₀.map A.subtype))
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hA₀log
  have hAstar_p : IsPGroup p Astar := hAstar_ea.isPGroup
  have hp_dvd_Astar : p ∣ Nat.card Astar := by
    obtain ⟨n, hn⟩ := hAstar_p.exists_card_eq
    have hnpos : 0 < n := by
      by_contra hn0
      have hn_zero : n = 0 := by omega
      rw [hn_zero, pow_zero] at hn
      rw [hn] at hAstar_log
      norm_num at hAstar_log
    rw [hn]
    exact dvd_pow_self p hnpos.ne'
  exact hG.odd.of_dvd_nat (hp_dvd_Astar.trans (Subgroup.card_subgroup_dvd_card Astar))

/-- Ambient form of the normal `E_{p^2}` witness inside an overgroup `P`.

If `A ≤ P`, `A` is a rank-three `p`-subgroup, and `P` is a finite `p`-group, then `P`
contains an ambient subgroup `D ≤ P` such that `D.subgroupOf P` is normal in `P`, `D` is
integer elementary abelian of order `p^2`. -/
private theorem exists_normal_isElementaryAbelian_card_prime_sq_in_overgroup_of_pSubgroup_rank_three
    [Finite G] {p : ℕ} [Fact p.Prime] {A P : Subgroup G}
    (hp : Odd p) (hPp : IsPGroup p P) (hAp : IsPGroup p A) (hAP : A ≤ P)
    (hmA : 3 ≤ rank ↥A) :
    ∃ D : Subgroup G,
      D ≤ P ∧ (D.subgroupOf P).Normal ∧ D.IsElementaryAbelian p ∧ Nat.card D = p ^ 2 := by
  classical
  have h3pRankA : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp hmA
  obtain ⟨A₀, hA₀ea, hA₀log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥A) (p := p) (n := 3) (by norm_num) h3pRankA
  let Astar : Subgroup G := A₀.map A.subtype
  have hAstar_ea : Astar.IsElementaryAbelian p := by
    change (A₀.map A.subtype).IsElementaryAbelian p
    exact Subgroup.IsElementaryAbelian.map A.subtype_injective hA₀ea
  have hAstar_log : 3 ≤ Nat.log p (Nat.card Astar) := by
    change 3 ≤ Nat.log p (Nat.card (A₀.map A.subtype))
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hA₀log
  have hAstarP : Astar ≤ P := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, _hy, rfl⟩ := hx
    exact hAP y.2
  let AstarP : Subgroup ↥P := Astar.subgroupOf P
  have hAstarP_ea : AstarP.IsElementaryAbelian p := by
    change (Astar.subgroupOf P).IsElementaryAbelian p
    exact IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAstarP).symm
      hAstar_ea
  have hAstarP_log : 3 ≤ Nat.log p (Nat.card AstarP) := by
    change 3 ≤ Nat.log p (Nat.card (Astar.subgroupOf P))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAstarP).toEquiv]
    exact hAstar_log
  have h3P : 3 ≤ pRank ↥P p := hAstarP_log.trans (le_pRank AstarP hAstarP_ea)
  obtain ⟨D₀, hD₀norm, hD₀ea, hD₀card⟩ :=
    exists_normal_isElementaryAbelian_card_prime_sq_of_three_le_pRank
      (R := ↥P) hp hPp h3P
  let D : Subgroup G := D₀.map P.subtype
  have hDP : D ≤ P := by
    change D₀.map P.subtype ≤ P
    exact Subgroup.map_subtype_le D₀
  have hDnormP : (D.subgroupOf P).Normal := by
    have htarget : D.subgroupOf P = D₀ := by
      apply (Subgroup.map_subtype_inj (H := P)).mp
      rw [Subgroup.map_subgroupOf_eq_of_le hDP]
    rwa [htarget]
  have hDea : D.IsElementaryAbelian p := by
    change (D₀.map P.subtype).IsElementaryAbelian p
    exact Subgroup.IsElementaryAbelian.map P.subtype_injective hD₀ea
  have hDcard : Nat.card D = p ^ 2 := by
    change Nat.card (D₀.map P.subtype) = p ^ 2
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact hD₀card
  exact ⟨D, hDP, hDnormP, hDea, hDcard⟩

/-- A normal elementary abelian subgroup D of order p^2 cuts rank at most one from a
rank-three elementary abelian subgroup.

This is the cardinal-to-rank bridge used in BG Corollary 9.3 after Lemma 4.5 supplies the
normal E_{p^2} witness. The proof reuses the §5 conjugation-count estimate
|B0 ∩ C_G(D)| >= p^2 for an elementary abelian B0 of order p^3, then converts the
resulting cardinal lower bound back into rank >= 2. -/
private theorem two_le_rank_inf_centralizer_of_normal_card_prime_sq_of_log_three [Finite G]
    {p : ℕ} [Fact p.Prime] {D Bstar : Subgroup G} [D.Normal]
    (hDea : D.IsElementaryAbelian p) (hDcard : Nat.card D = p ^ 2)
    (hBstarea : Bstar.IsElementaryAbelian p)
    (hBstarlog : 3 ≤ Nat.log p (Nat.card Bstar)) :
    2 ≤ rank ↥(Bstar ⊓ Subgroup.centralizer (D : Set G)) := by
  classical
  have hBstar_card_ge : p ^ 3 ≤ Nat.card Bstar :=
    Nat.pow_le_of_le_log Nat.card_pos.ne' hBstarlog
  obtain ⟨B₀, hB₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card (n := 3)
      (Fact.out : p.Prime) hBstarea.isPGroup hBstar_card_ge
  let B₀G : Subgroup G := B₀.map Bstar.subtype
  have hB₀G_ea : B₀G.IsElementaryAbelian p := by
    change (B₀.map Bstar.subtype).IsElementaryAbelian p
    exact Subgroup.IsElementaryAbelian.map Bstar.subtype_injective
      (hBstarea.to_subgroup B₀)
  have hB₀Gcard : Nat.card B₀G = p ^ 3 := by
    change Nat.card (B₀.map Bstar.subtype) = p ^ 3
    rw [Subgroup.card_map_of_injective Bstar.subtype_injective, hB₀card]
  let H : Subgroup G := B₀G ⊓ Subgroup.centralizer (D : Set G)
  have hHcard : p ^ 2 ≤ Nat.card H := by
    change p ^ 2 ≤ Nat.card ↥(B₀G ⊓ Subgroup.centralizer (D : Set G))
    exact OddOrder.BG.Ch1.S05.card_inf_centralizer_ge_prime_sq_of_card_prime_cube
      (E := D) (B := B₀G) hDea hDcard hB₀G_ea hB₀Gcard
  have hH_ea : H.IsElementaryAbelian p := by
    have hH_le_B₀G : H ≤ B₀G := by
      dsimp [H]
      exact inf_le_left
    have hH_sub_ea : (H.subgroupOf B₀G).IsElementaryAbelian p :=
      hB₀G_ea.to_subgroup (H.subgroupOf B₀G)
    exact IsElementaryAbelian.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hH_le_B₀G) hH_sub_ea
  have hHlog : 2 ≤ Nat.log p (Nat.card H) :=
    Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt hHcard
  have h2pRankH : 2 ≤ pRank ↥H p := hHlog.trans hH_ea.log_card_le_pRank
  let K : Subgroup G := Bstar ⊓ Subgroup.centralizer (D : Set G)
  have hB₀G_le_Bstar : B₀G ≤ Bstar := by
    change B₀.map Bstar.subtype ≤ Bstar
    exact Subgroup.map_subtype_le B₀
  have hHleK : H ≤ K := by
    intro x hx
    exact ⟨hB₀G_le_Bstar hx.1, hx.2⟩
  have hmono : pRank ↥H p ≤ pRank ↥K p :=
    pRank_le_of_injective (f := Subgroup.inclusion hHleK)
      (Subgroup.inclusion_injective hHleK)
  exact (h2pRankH.trans hmono).trans (pRank_le_rank (G := ↥K) p)

/-- Local-overgroup form of the preceding rank-drop bridge.

If `D` is normal in an overgroup `P`, the same rank drop can be proved inside `P` and then
transported back to the ambient group `G`. This is the form needed for BG Corollary 9.3,
where Lemma 4.5 supplies `D ⊴ P` for a Sylow `p`-subgroup rather than `D ⊴ G`. -/
private theorem two_le_rank_inf_centralizer_of_normal_in_overgroup_card_prime_sq_of_log_three
    [Finite G] {p : ℕ} [Fact p.Prime] {P D Bstar : Subgroup G}
    (hDP : D ≤ P) (hBstarP : Bstar ≤ P) (hDnormP : (D.subgroupOf P).Normal)
    (hDea : D.IsElementaryAbelian p) (hDcard : Nat.card D = p ^ 2)
    (hBstarea : Bstar.IsElementaryAbelian p)
    (hBstarlog : 3 ≤ Nat.log p (Nat.card Bstar)) :
    2 ≤ rank ↥(Bstar ⊓ Subgroup.centralizer (D : Set G)) := by
  classical
  let DP : Subgroup P := D.subgroupOf P
  let BP : Subgroup P := Bstar.subgroupOf P
  haveI : DP.Normal := by
    simpa [DP] using hDnormP
  have hDP_ea : DP.IsElementaryAbelian p := by
    dsimp [DP]
    exact IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDP).symm hDea
  have hDP_card : Nat.card DP = p ^ 2 := by
    dsimp [DP]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv, hDcard]
  have hBP_ea : BP.IsElementaryAbelian p := by
    dsimp [BP]
    exact IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBstarP).symm
      hBstarea
  have hBP_log : 3 ≤ Nat.log p (Nat.card BP) := by
    dsimp [BP]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBstarP).toEquiv]
    exact hBstarlog
  let KP : Subgroup P := BP ⊓ Subgroup.centralizer (DP : Set P)
  let KG : Subgroup G := Bstar ⊓ Subgroup.centralizer (D : Set G)
  have hKP_rank : 2 ≤ rank ↥KP := by
    dsimp [KP]
    exact two_le_rank_inf_centralizer_of_normal_card_prime_sq_of_log_three
      (G := P) (D := DP) (Bstar := BP) hDP_ea hDP_card hBP_ea hBP_log
  let H : Subgroup G := KP.map P.subtype
  have hHleKG : H ≤ KG := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · change (y : G) ∈ Bstar
      simpa [BP] using hy.1
    · change (y : G) ∈ Subgroup.centralizer (D : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      let dP : P := ⟨d, hDP hd⟩
      have hdP : dP ∈ DP := by
        change (d : G) ∈ D
        exact hd
      have hcommP := Subgroup.mem_centralizer_iff.mp hy.2 dP hdP
      exact congrArg Subtype.val hcommP
  have hKP_rank_le_H : rank ↥KP ≤ rank ↥H :=
    rank_le_of_injective
      (f := (Subgroup.equivMapOfInjective KP P.subtype P.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective KP P.subtype P.subtype_injective).injective
  have hH_rank_le_KG : rank ↥H ≤ rank ↥KG :=
    rank_le_of_injective (f := Subgroup.inclusion hHleKG)
      (Subgroup.inclusion_injective hHleKG)
  exact (hKP_rank.trans hKP_rank_le_H).trans hH_rank_le_KG

/-- `A`-side local rank-drop bridge for BG Corollary 9.3.

If a finite `p`-subgroup `A ≤ P` has BG rank at least three and `D ⊴ P` is elementary
abelian of order `p^2`, then `A ∩ C_G(D)` has rank at least two. The proof extracts a
rank-three elementary abelian subgroup of `A` at the same prime `p`, applies the already
proved elementary abelian rank-drop inside `P`, then includes back into `A ∩ C_G(D)`. -/
private theorem two_le_rank_inf_centralizer_of_pSubgroup_rank_three [Finite G]
    {p : ℕ} [Fact p.Prime] {P D A : Subgroup G}
    (hAp : IsPGroup p A) (hAP : A ≤ P) (hDP : D ≤ P)
    (hDnormP : (D.subgroupOf P).Normal)
    (hDea : D.IsElementaryAbelian p) (hDcard : Nat.card D = p ^ 2)
    (hmA : 3 ≤ rank ↥A) :
    2 ≤ rank ↥(A ⊓ Subgroup.centralizer (D : Set G)) := by
  classical
  have h3pRankA : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp hmA
  obtain ⟨A₀, hA₀ea, hA₀log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥A) (p := p) (n := 3) (by norm_num) h3pRankA
  let Astar : Subgroup G := A₀.map A.subtype
  have hAstar_ea : Astar.IsElementaryAbelian p := by
    change (A₀.map A.subtype).IsElementaryAbelian p
    exact Subgroup.IsElementaryAbelian.map A.subtype_injective hA₀ea
  have hAstar_log : 3 ≤ Nat.log p (Nat.card Astar) := by
    change 3 ≤ Nat.log p (Nat.card (A₀.map A.subtype))
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hA₀log
  have hAstarP : Astar ≤ P := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, _hy, rfl⟩ := hx
    exact hAP y.2
  have hAstar_le_A : Astar ≤ A := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, _hy, rfl⟩ := hx
    exact y.2
  have hAstar_rank :
      2 ≤ rank ↥(Astar ⊓ Subgroup.centralizer (D : Set G)) :=
    two_le_rank_inf_centralizer_of_normal_in_overgroup_card_prime_sq_of_log_three
      (P := P) (D := D) (Bstar := Astar) hDP hAstarP hDnormP hDea hDcard
      hAstar_ea hAstar_log
  have hle :
      Astar ⊓ Subgroup.centralizer (D : Set G) ≤
        A ⊓ Subgroup.centralizer (D : Set G) := by
    intro x hx
    exact ⟨hAstar_le_A hx.1, hx.2⟩
  exact hAstar_rank.trans
    (rank_le_of_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle))

/-- BG Corollary 9.3's Corollary-9.2 cascade, after the Lemma-4.5 witness `D` and the
two cyclic-quotient rank drops have been supplied.

In the book proof, `D ⊴ P`, `|D| = p²`, and `B* ≤ C_G(B)` with `m(B*) = 3` are chosen so
that `m(C_A(D)) ≥ 2` and `m(C_{B*}(D)) ≥ 2`. This lemma formalizes the remaining
successive applications of Corollary 9.2:
`A → C_A(D) → D → C_{B*}(D) → B* → B`. -/
private theorem isUniquelyMaximal_of_rank_drop_witness [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A B D Bstar : Subgroup G}
    (hAab : IsMulCommutative A) (hAU : IsUniquelyMaximal A)
    (hBp : IsPGroup p B) (hBnc : ¬ IsCyclic ↥B)
    (hDea : D.IsElementaryAbelian p) (hDcard : Nat.card D = p ^ 2)
    (hBstarea : Bstar.IsElementaryAbelian p)
    (hBstarlog : 3 ≤ Nat.log p (Nat.card Bstar))
    (hBstar_le_CB : Bstar ≤ Subgroup.centralizer (B : Set G))
    (hrCAD : 2 ≤ rank ↥(A ⊓ Subgroup.centralizer (D : Set G)))
    (hrCBD : 2 ≤ rank ↥(Bstar ⊓ Subgroup.centralizer (D : Set G))) :
    IsUniquelyMaximal B := by
  classical
  let CAD : Subgroup G := A ⊓ Subgroup.centralizer (D : Set G)
  let CBD : Subgroup G := Bstar ⊓ Subgroup.centralizer (D : Set G)
  have hCAD_le_CA : CAD ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val
      ((hAab.is_comm.comm (⟨x, hx.1⟩ : A) (⟨a, ha⟩ : A)).symm)
  have hCADU : IsUniquelyMaximal CAD :=
    isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hAU hCAD_le_CA hrCAD
  have hD_le_CCAD : D ≤ Subgroup.centralizer (CAD : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp hc.2 d hd).symm
  have hrD : 2 ≤ rank ↥D := by
    have hlog_le : Nat.log p (Nat.card D) ≤ pRank ↥D p := hDea.log_card_le_pRank
    have hlog : Nat.log p (Nat.card D) = 2 := by
      rw [hDcard, Nat.log_pow (Fact.out : p.Prime).one_lt]
    exact ((le_of_eq hlog.symm).trans hlog_le).trans (pRank_le_rank (G := ↥D) p)
  have hDU : IsUniquelyMaximal D :=
    isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hCADU hD_le_CCAD hrD
  have hCBD_le_CD : CBD ≤ Subgroup.centralizer (D : Set G) := inf_le_right
  have hCBDU : IsUniquelyMaximal CBD :=
    isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hDU hCBD_le_CD hrCBD
  have hBstar_le_CCBD : Bstar ≤ Subgroup.centralizer (CBD : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact congrArg Subtype.val
      ((hBstarea.comm (⟨b, hb⟩ : Bstar) (⟨c, hc.1⟩ : Bstar)).symm)
  have hrBstar : 2 ≤ rank ↥Bstar := by
    have hlog_le : Nat.log p (Nat.card Bstar) ≤ pRank ↥Bstar p :=
      hBstarea.log_card_le_pRank
    exact ((by omega : 2 ≤ Nat.log p (Nat.card Bstar)).trans hlog_le).trans
      (pRank_le_rank (G := ↥Bstar) p)
  have hBstarU : IsUniquelyMaximal Bstar :=
    isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hCBDU hBstar_le_CCBD hrBstar
  have hB_le_CBstar : B ≤ Subgroup.centralizer (Bstar : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro bstar hbstar
    exact (Subgroup.mem_centralizer_iff.mp (hBstar_le_CB hbstar) b hb).symm
  have hrB : 2 ≤ rank ↥B := two_le_rank_of_noncyclic_pSubgroup hG hBp hBnc
  exact isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hBstarU hB_le_CBstar hrB

/-- `MulAut` pointwise action on subgroups is the corresponding subgroup map. -/
private theorem mulAut_smul_eq_map (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by
  rw [Subgroup.pointwise_smul_def]
  rfl

/-- Any finite `p`-subgroup can be conjugated into a chosen Sylow `p`-subgroup.

This is the Sylow-conjugacy bridge used in BG Corollary 9.3's line "replacing by
conjugates": after extracting a `p`-subgroup witness, choose a Sylow containing it and
conjugate that Sylow to the fixed one. -/
private theorem exists_conj_le_sylow_of_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] {Q : Subgroup G} (hQ : IsPGroup p Q) (P : Sylow p G) :
    ∃ g : G, ((MulAut.conj g) • Q : Subgroup G) ≤ (P : Subgroup G) := by
  classical
  obtain ⟨Q', hQQ'⟩ := hQ.exists_le_sylow
  haveI : MulAction.IsPretransitive G (Sylow p G) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q' P
  refine ⟨g, ?_⟩
  have hle : ((MulAut.conj g) • Q : Subgroup G) ≤
      ((MulAut.conj g) • (Q' : Subgroup G) : Subgroup G) :=
    (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr hQQ'
  have hQ'eq : ((MulAut.conj g) • (Q' : Subgroup G) : Subgroup G) =
      (P : Subgroup G) := by
    have := congrArg Sylow.toSubgroup hg
    rwa [Sylow.coe_subgroup_smul] at this
  exact hle.trans (le_of_eq hQ'eq)

/-- Centralizer containment is preserved when both sides are conjugated by the same element.

This is the Corollary 9.3 bookkeeping needed after replacing `B*` by a conjugate: the
subgroup `B` must be conjugated at the same time for `B* ≤ C_G(B)` to remain true. -/
private theorem conj_smul_le_centralizer_conj_smul {B Bstar : Subgroup G} {g : G}
    (hBstar_le_CB : Bstar ≤ Subgroup.centralizer (B : Set G)) :
    ((MulAut.conj g) • Bstar : Subgroup G) ≤
      Subgroup.centralizer (((MulAut.conj g) • B : Subgroup G) : Set G) := by
  rintro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases hx with ⟨x0, hx0, rfl⟩
  rcases hy with ⟨y0, hy0, rfl⟩
  have hcomm : y0 * x0 = x0 * y0 :=
    Subgroup.mem_centralizer_iff.mp (hBstar_le_CB hx0) y0 hy0
  simpa [map_mul] using congrArg (MulAut.conj g) hcomm

/-- BG Corollary 9.3 cascade with the `B*`-side rank drop supplied by a normal
`E_{p^2}` witness inside an overgroup `P`.

This leaves only the `A ∩ C_G(D)` rank drop explicit. In the book proof, that is the other
cyclic-quotient calculation after choosing the same Lemma 4.5 witness `D ⊴ P`. -/
private theorem isUniquelyMaximal_of_overgroup_rank_drop_witness [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A B D Bstar P : Subgroup G}
    (hAab : IsMulCommutative A) (hAU : IsUniquelyMaximal A)
    (hBp : IsPGroup p B) (hBnc : ¬ IsCyclic ↥B)
    (hDP : D ≤ P) (hBstarP : Bstar ≤ P) (hDnormP : (D.subgroupOf P).Normal)
    (hDea : D.IsElementaryAbelian p) (hDcard : Nat.card D = p ^ 2)
    (hBstarea : Bstar.IsElementaryAbelian p)
    (hBstarlog : 3 ≤ Nat.log p (Nat.card Bstar))
    (hBstar_le_CB : Bstar ≤ Subgroup.centralizer (B : Set G))
    (hrCAD : 2 ≤ rank ↥(A ⊓ Subgroup.centralizer (D : Set G))) :
    IsUniquelyMaximal B := by
  classical
  have hrCBD : 2 ≤ rank ↥(Bstar ⊓ Subgroup.centralizer (D : Set G)) :=
    two_le_rank_inf_centralizer_of_normal_in_overgroup_card_prime_sq_of_log_three
      (P := P) (D := D) (Bstar := Bstar) hDP hBstarP hDnormP hDea hDcard
      hBstarea hBstarlog
  exact isUniquelyMaximal_of_rank_drop_witness hG hAab hAU hBp hBnc hDea hDcard
    hBstarea hBstarlog hBstar_le_CB hrCAD hrCBD

/-- BG Corollary 9.3 cascade with both cyclic-quotient rank drops discharged from a
single normal `E_{p^2}` witness `D ⊴ P`.

This is the form left after choosing the Lemma-4.5 witness and a rank-three elementary
abelian subgroup `B* ≤ C_G(B)` inside the same overgroup `P`. -/
private theorem isUniquelyMaximal_of_overgroup_rank_three_witness [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A B D Bstar P : Subgroup G}
    (hAab : IsMulCommutative A) (hAp : IsPGroup p A) (hAU : IsUniquelyMaximal A)
    (hBp : IsPGroup p B) (hBnc : ¬ IsCyclic ↥B)
    (hAP : A ≤ P) (hDP : D ≤ P) (hBstarP : Bstar ≤ P)
    (hDnormP : (D.subgroupOf P).Normal)
    (hDea : D.IsElementaryAbelian p) (hDcard : Nat.card D = p ^ 2)
    (hBstarea : Bstar.IsElementaryAbelian p)
    (hBstarlog : 3 ≤ Nat.log p (Nat.card Bstar))
    (hBstar_le_CB : Bstar ≤ Subgroup.centralizer (B : Set G))
    (hmA : 3 ≤ rank ↥A) :
    IsUniquelyMaximal B := by
  classical
  have hrCAD : 2 ≤ rank ↥(A ⊓ Subgroup.centralizer (D : Set G)) :=
    two_le_rank_inf_centralizer_of_pSubgroup_rank_three
      (P := P) (D := D) (A := A) hAp hAP hDP hDnormP hDea hDcard hmA
  exact isUniquelyMaximal_of_overgroup_rank_drop_witness hG hAab hAU hBp hBnc hDP
    hBstarP hDnormP hDea hDcard hBstarea hBstarlog hBstar_le_CB hrCAD

/-- Conjugate the `B*` side into the chosen overgroup, run the rank-three witness wrapper,
and transport uniqueness back to the original `B`.

This packages the Corollary 9.3 replacement step where `B*` is conjugated into the Sylow
overgroup containing `A`; the centralizer hypothesis is kept valid by conjugating `B` by the
same element. -/
private theorem isUniquelyMaximal_of_conj_overgroup_rank_three_witness [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A B D Bstar P : Subgroup G}
    {g : G} (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    (hAU : IsUniquelyMaximal A) (hBp : IsPGroup p B) (hBnc : ¬ IsCyclic ↥B)
    (hAP : A ≤ P) (hDP : D ≤ P)
    (hBstarP : ((MulAut.conj g) • Bstar : Subgroup G) ≤ P)
    (hDnormP : (D.subgroupOf P).Normal)
    (hDea : D.IsElementaryAbelian p) (hDcard : Nat.card D = p ^ 2)
    (hBstarea : Bstar.IsElementaryAbelian p)
    (hBstarlog : 3 ≤ Nat.log p (Nat.card Bstar))
    (hBstar_le_CB : Bstar ≤ Subgroup.centralizer (B : Set G))
    (hmA : 3 ≤ rank ↥A) :
    IsUniquelyMaximal B := by
  classical
  let φ : MulAut G := MulAut.conj g
  let Bconj : Subgroup G := φ • B
  let Bstarconj : Subgroup G := φ • Bstar
  have hBconj_eq : Bconj = B.map (φ : G →* G) := by
    change φ • B = B.map (φ : G →* G)
    exact mulAut_smul_eq_map φ B
  have hBstarconj_eq : Bstarconj = Bstar.map (φ : G →* G) := by
    change φ • Bstar = Bstar.map (φ : G →* G)
    exact mulAut_smul_eq_map φ Bstar
  have hBconj_p : IsPGroup p Bconj := by
    rw [hBconj_eq]
    exact hBp.map (φ : G →* G)
  have hBconj_nc : ¬ IsCyclic ↥Bconj := by
    intro hcyc
    apply hBnc
    rw [hBconj_eq] at hcyc
    let e : ↥B ≃* ↥(B.map (φ : G →* G)) :=
      Subgroup.equivMapOfInjective B (φ : G →* G) φ.injective
    letI : IsCyclic ↥(B.map (φ : G →* G)) := hcyc
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hBstarconj_ea : Bstarconj.IsElementaryAbelian p := by
    rw [hBstarconj_eq]
    exact Subgroup.IsElementaryAbelian.map φ.injective hBstarea
  have hBstarconj_log : 3 ≤ Nat.log p (Nat.card Bstarconj) := by
    rw [hBstarconj_eq, Subgroup.card_map_of_injective φ.injective]
    exact hBstarlog
  have hBstarconj_le_CBconj :
      Bstarconj ≤ Subgroup.centralizer (Bconj : Set G) := by
    change ((MulAut.conj g) • Bstar : Subgroup G) ≤
      Subgroup.centralizer (((MulAut.conj g) • B : Subgroup G) : Set G)
    exact conj_smul_le_centralizer_conj_smul hBstar_le_CB
  have hBconjU : IsUniquelyMaximal Bconj :=
    isUniquelyMaximal_of_overgroup_rank_three_witness hG hAab hAp hAU hBconj_p
      hBconj_nc hAP hDP hBstarP hDnormP hDea hDcard hBstarconj_ea
      hBstarconj_log hBstarconj_le_CBconj hmA
  have hBmapU : IsUniquelyMaximal (B.map (φ : G →* G)) := by
    simpa [hBconj_eq] using hBconjU
  have hback :
      IsUniquelyMaximal ((B.map (φ : G →* G)).comap (φ : G →* G)) :=
    hBmapU.comap_equiv φ
  have hcomap : (B.map (φ : G →* G)).comap (φ : G →* G) = B :=
    Subgroup.comap_map_eq_self_of_injective (f := (φ : G →* G)) φ.injective B
  simpa [hcomap] using hback

/-- Extract the rank-three elementary abelian subgroup `B* ≤ C_G(B)` used in
BG Corollary 9.3 from the `pRank` hypothesis. -/
private theorem exists_elementaryAbelian_le_centralizer_of_three_le_pRank [Finite G]
    {p : ℕ} [Fact p.Prime] {B : Subgroup G}
    (hrB : 3 ≤ pRank ↥(Subgroup.centralizer (B : Set G)) p) :
    ∃ Bstar : Subgroup G,
      Bstar.IsElementaryAbelian p ∧
        Bstar ≤ Subgroup.centralizer (B : Set G) ∧
          3 ≤ Nat.log p (Nat.card Bstar) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (B : Set G)
  obtain ⟨B₀, hB₀ea, hB₀log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥C) (p := p) (n := 3) (by norm_num) hrB
  let Bstar : Subgroup G := B₀.map C.subtype
  refine ⟨Bstar, ?_, ?_, ?_⟩
  · change (B₀.map C.subtype).IsElementaryAbelian p
    exact Subgroup.IsElementaryAbelian.map C.subtype_injective hB₀ea
  · change B₀.map C.subtype ≤ C
    exact Subgroup.map_subtype_le B₀
  · change 3 ≤ Nat.log p (Nat.card (B₀.map C.subtype))
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hB₀log

/-- **BG Corollary 9.3** (mmd L2545): `p` prime, `A` abelian `p`-部分群, `B` noncyclic
`p`-部分群、`A ∈ 𝒰`, `m(A) ≥ 3`, `r_p(C_G(B)) ≥ 3` ⇒ `B ∈ 𝒰`。 -/
theorem isUniquelyMaximal_of_abelian_rank_three [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A B : Subgroup G} (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    (hBp : IsPGroup p B) (hBnc : ¬ IsCyclic ↥B) (hAU : IsUniquelyMaximal A)
    (hmA : 3 ≤ rank ↥A) (hrB : 3 ≤ pRank ↥(Subgroup.centralizer (B : Set G)) p) :
    IsUniquelyMaximal B := by
  classical
  obtain ⟨Bstar, hBstarea, hBstar_le_CB, hBstarlog⟩ :=
    exists_elementaryAbelian_le_centralizer_of_three_le_pRank (B := B) hrB
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  have hp_odd : Odd p := odd_prime_of_isPGroup_of_three_le_rank hG hAp hmA
  obtain ⟨g, hBstarP⟩ :=
    exists_conj_le_sylow_of_isPGroup hBstarea.isPGroup P
  obtain ⟨D, hDP, hDnormP, hDea, hDcard⟩ :=
    exists_normal_isElementaryAbelian_card_prime_sq_in_overgroup_of_pSubgroup_rank_three
      (P := (P : Subgroup G)) hp_odd P.isPGroup' hAp hAP hmA
  exact isUniquelyMaximal_of_conj_overgroup_rank_three_witness hG hAab hAp hAU hBp
    hBnc hAP hDP hBstarP hDnormP hDea hDcard hBstarea hBstarlog hBstar_le_CB hmA

/-- **BG Lemma 9.4** (mmd L2555): `p` prime, `M ∈ ℳ`, `r_p(F(M)) ≥ 3` ⇒ `𝒰` は rank `≥ 3` の
すべての abelian `p`-群を含む。 -/
theorem abelian_rank_three_isUniquelyMaximal_of_fitting [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hr : 3 ≤ pRank ↥(S08.fittingInG M) p) :
    ∀ A : Subgroup G, IsMulCommutative A → IsPGroup p A → 3 ≤ rank ↥A → IsUniquelyMaximal A := by
  classical
  have hpF : p ∈ (Nat.card ↥(S08.fittingInG M)).primeFactors :=
    mem_primeFactors_card_of_pos_pRank (H := ↥(S08.fittingInG M))
      (p := p) (by omega)
  obtain ⟨A₀, hA₀max, hA₀rank⟩ :=
    exists_isMaxElemAbelianIn_rank_three_of_three_le_pRank
      (H := S08.fittingInG M) hr
  have hWitness :
      ∃ U : Subgroup G,
        IsMulCommutative U ∧ IsPGroup p U ∧ IsUniquelyMaximal U ∧ 3 ≤ rank ↥U := by
    by_cases hFp : IsPGroup p ↥(S08.fittingInG M)
    · have hFpM : IsPGroup p ((S08.fittingInG M).subgroupOf M) :=
        hFp.of_equiv (Subgroup.subgroupOfEquivOfLe (S08.fittingInG_le M)).symm
      obtain ⟨P, hFP⟩ := hFpM.exists_le_sylow
      have h3Fsub : 3 ≤ pRank ↥((S08.fittingInG M).subgroupOf M) p :=
        hr.trans
          (pRank_le_of_injective
            (f := (Subgroup.subgroupOfEquivOfLe (S08.fittingInG_le M)).symm.toMonoidHom)
            (Subgroup.subgroupOfEquivOfLe (S08.fittingInG_le M)).symm.injective)
      have h3P : 3 ≤ pRank ↥(P : Subgroup ↥M) p :=
        h3Fsub.trans
          (pRank_le_of_injective (f := Subgroup.inclusion hFP)
            (Subgroup.inclusion_injective hFP))
      have hp_dvd_G : p ∣ Nat.card G :=
        (Nat.mem_primeFactors.mp hpF).2.1.trans
          (Subgroup.card_subgroup_dvd_card (S08.fittingInG M))
      have hp_odd : Odd p := hG.odd.of_dvd_nat hp_dvd_G
      obtain ⟨Asc, hAsc_scn⟩ :=
        OddOrder.BG.Ch1.S05.scn3_nonempty_of_three_le_pRank hp_odd P.isPGroup' h3P
      let A_M : Subgroup ↥M := Asc.map (P : Subgroup ↥M).subtype
      have hA_MP : A_M ≤ (P : Subgroup ↥M) := by
        change Asc.map (P : Subgroup ↥M).subtype ≤ (P : Subgroup ↥M)
        exact Subgroup.map_subtype_le Asc
      have hA_M_scn : IsSCN₃ p (A_M.subgroupOf (P : Subgroup ↥M)) := by
        have htarget : A_M.subgroupOf (P : Subgroup ↥M) = Asc := by
          apply (Subgroup.map_subtype_inj (H := (P : Subgroup ↥M))).mp
          rw [Subgroup.map_subgroupOf_eq_of_le hA_MP]
        rwa [htarget]
      have h8 :=
        (S08.sylow_isSylow_and_scn3_isUniquelyMaximal_of_pGroup
          hG hM hpF hA₀max hA₀rank P hFp).2 A_M hA_MP hA_M_scn
      let U : Subgroup G := A_M.map M.subtype
      have hA_Mab : IsMulCommutative A_M := by
        haveI : IsMulCommutative Asc := hAsc_scn.isSCN.isMulCommutative
        change IsMulCommutative (Asc.map (P : Subgroup ↥M).subtype)
        exact Subgroup.map_isMulCommutative Asc (P : Subgroup ↥M).subtype
      have hUab : IsMulCommutative U := by
        haveI : IsMulCommutative A_M := hA_Mab
        change IsMulCommutative (A_M.map M.subtype)
        exact Subgroup.map_isMulCommutative A_M M.subtype
      have hA_Mp : IsPGroup p A_M := by
        change IsPGroup p (Asc.map (P : Subgroup ↥M).subtype)
        exact (P.isPGroup'.to_subgroup Asc).map (P : Subgroup ↥M).subtype
      have hUp : IsPGroup p U := by
        change IsPGroup p (A_M.map M.subtype)
        exact hA_Mp.map M.subtype
      have hA_M_rank : 3 ≤ pRank ↥A_M p := by
        let ePM := Subgroup.equivMapOfInjective Asc (P : Subgroup ↥M).subtype
          (P : Subgroup ↥M).subtype_injective
        exact hAsc_scn.le_pRank.trans
          (pRank_le_of_injective (f := ePM.toMonoidHom) ePM.injective)
      have hUrank : 3 ≤ rank ↥U := by
        let eMG := Subgroup.equivMapOfInjective A_M M.subtype M.subtype_injective
        have hUpRank : 3 ≤ pRank ↥U p :=
          hA_M_rank.trans
            (pRank_le_of_injective (f := eMG.toMonoidHom) eMG.injective)
        exact hUpRank.trans (pRank_le_rank (G := ↥U) p)
      exact ⟨U, hUab, hUp, h8.2, hUrank⟩
    · have hCFU : IsUniquelyMaximal (S08.cFittingInG M A₀) :=
        S08.cFitting_isUniquelyMaximal_of_not_pGroup hG hM hpF hA₀max hA₀rank hFp
      have hA₀_le_CF : A₀ ≤ Subgroup.centralizer (S08.cFittingInG M A₀ : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        change x ∈ Subgroup.centralizer (A₀ : Set G) ⊓ S08.fittingInG M at hx
        exact (Subgroup.mem_centralizer_iff.mp hx.1 a ha).symm
      have hA₀U : IsUniquelyMaximal A₀ :=
        isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hCFU hA₀_le_CF
          (by omega)
      have hA₀ea : A₀.IsElementaryAbelian p :=
        S08.isMaxElemAbelianIn_isElementaryAbelian hA₀max
      have hA₀ab : IsMulCommutative A₀ := IsMulCommutative.of_comm hA₀ea.comm
      have hA₀p : IsPGroup p A₀ := hA₀ea.isPGroup
      exact ⟨A₀, hA₀ab, hA₀p, hA₀U, hA₀rank⟩
  obtain ⟨U, hUab, hUp, hUU, hUrank⟩ := hWitness
  intro A hAab hAp hArank
  have hAnc : ¬ IsCyclic ↥A := not_isCyclic_of_two_le_rank (A := A) (by omega)
  have hCA_rank : 3 ≤ pRank ↥(Subgroup.centralizer (A : Set G)) p :=
    three_le_pRank_centralizer_of_isMulCommutative_of_isPGroup_of_three_le_rank
      hAab hAp hArank
  exact isUniquelyMaximal_of_abelian_rank_three hG hUab hUp hAp hAnc hUU hUrank hCA_rank

/-- A global `SCN₃(p)` subgroup is abelian in the ambient group. -/
private theorem isMulCommutative_of_mem_scn3Global [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    IsMulCommutative A := by
  obtain ⟨P, hAP, hAscn3⟩ := hA
  exact IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff_of_setLike.mp hAscn3.isSCN.isMulCommutative
      (⟨a, hAP ha⟩ : ↥(P : Subgroup G)) (Subgroup.mem_subgroupOf.mpr ha)
      ⟨b, hAP hb⟩ (Subgroup.mem_subgroupOf.mpr hb))

/-- A global `SCN₃(p)` subgroup is a `p`-subgroup in the ambient group. -/
private theorem isPGroup_of_mem_scn3Global [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    IsPGroup p A := by
  obtain ⟨P, hAP, _hAscn3⟩ := hA
  exact (P.isPGroup').to_le hAP

/-- A global `SCN₃(p)` subgroup has ambient rank at least three. -/
private theorem three_le_rank_of_mem_scn3Global [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    3 ≤ rank ↥A := by
  obtain ⟨P, hAP, hAscn3⟩ := hA
  have h3A : 3 ≤ pRank ↥A p :=
    hAscn3.le_pRank.trans
      (pRank_le_of_injective
        (f := (Subgroup.subgroupOfEquivOfLe hAP).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hAP).injective)
  exact h3A.trans (pRank_le_rank (G := ↥A) p)

/-- The centralizer of a global `SCN₃(p)` subgroup is proper in a minimal odd simple group. -/
private theorem centralizer_lt_top_of_mem_scn3Global [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ S07.scn3Global p G) :
    Subgroup.centralizer (A : Set G) < ⊤ := by
  classical
  have hZbot : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact absurd (isSolvable_of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm) hG.notSolvable
  have hArank : 2 ≤ rank ↥A := (by omega : (2 : ℕ) ≤ 3).trans
    (three_le_rank_of_mem_scn3Global hA)
  have hAne : A ≠ ⊥ := by
    obtain ⟨q, hq, E, _hEea, hEA, hEnc⟩ :=
      exists_isElementaryAbelian_not_isCyclic_le_of_two_le_rank A hArank
    intro hAbot
    have hEbot : E = ⊥ := le_bot_iff.mp (hEA.trans (le_of_eq hAbot))
    haveI : Nontrivial ↥E := Nontrivial.of_not_isCyclic hEnc
    exact ((Subgroup.nontrivial_iff_ne_bot E).mp inferInstance) hEbot
  rw [lt_top_iff_ne_top]
  intro hCtop
  have hAleZ : A ≤ Subgroup.center G :=
    Subgroup.centralizer_eq_top_iff_subset.mp hCtop
  exact hAne (le_bot_iff.mp (hAleZ.trans (le_of_eq hZbot)))

/-- A global `SCN₃(p)` subgroup has at least one maximal subgroup over its centralizer. -/
private theorem exists_maximalSubgroupsContaining_centralizer_of_mem_scn3Global [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ S07.scn3Global p G) :
    ∃ M : Subgroup G, M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) := by
  classical
  have hClt : Subgroup.centralizer (A : Set G) < ⊤ :=
    centralizer_lt_top_of_mem_scn3Global hG hA
  obtain ⟨M, hM, hCM⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.centralizer (A : Set G))).resolve_left hClt.ne
  exact ⟨M, hM, hCM⟩

/-- A global `SCN₃(p)` subgroup is nontrivial. -/
private theorem ne_bot_of_mem_scn3Global [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    A ≠ ⊥ := by
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hArank : 3 ≤ rank ↥A := three_le_rank_of_mem_scn3Global hA
  have h3pRankA : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp hArank
  have hpA : p ∣ Nat.card A :=
    (Nat.mem_primeFactors.mp
      (mem_primeFactors_card_of_pos_pRank (H := ↥A) (p := p) (by omega))).2.1
  intro hAbot
  rw [hAbot, Subgroup.card_bot] at hpA
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hpA)

/-- The prime set of a global `SCN₃(p)` subgroup is exactly `{p}`. -/
private theorem primesOf_eq_singleton_of_mem_scn3Global [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    S07.primesOf A = ({p} : Set ℕ) := by
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hAne : A ≠ ⊥ := ne_bot_of_mem_scn3Global hA
  obtain ⟨n, hn⟩ := hAp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hAne (Subgroup.card_eq_one.mp hn)
  ext q
  simp only [S07.primesOf, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [hn, Nat.primeFactors_prime_pow hn0 (Fact.out : p.Prime), Finset.mem_singleton]

/-- A global `SCN₃(p)` subgroup forces `p ∣ |G|`. -/
private theorem prime_dvd_card_of_mem_scn3Global [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    p ∣ Nat.card G := by
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hArank : 3 ≤ rank ↥A := three_le_rank_of_mem_scn3Global hA
  have h3pRankA : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp hArank
  have hpA : p ∣ Nat.card A :=
    (Nat.mem_primeFactors.mp
      (mem_primeFactors_card_of_pos_pRank (H := ↥A) (p := p) (by omega))).2.1
  exact hpA.trans (Subgroup.card_subgroup_dvd_card A)

/-- A subgroup of a finite `p`-group is subnormal in that `p`-group. -/
private theorem subgroupOf_isSubnormal_of_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] {A R : Subgroup G} (hRp : IsPGroup p R) :
    (A.subgroupOf R).IsSubnormal := by
  haveI : Group.IsNilpotent ↥R := hRp.isNilpotent
  exact OddOrder.Isaacs.Ch02.isSubnormal_of_isNilpotent_finite (A.subgroupOf R)

/-- The Theorem 7.6 → Theorem 7.4 propagation step used in BG Lemma 9.5.

If `A ∈ SCN₃(p)`, `A ≤ R`, and `R` is a proper `p`-subgroup, then for every `q ≠ p`
`O_{p'}(C_G(R))` acts transitively on `ℋ_G^*(R;q)`. This is the formal version of the
line "By Theorems 7.6 and 7.4" in the normalizer part of Lemma 9.5. -/
private theorem conjTransitiveOn_hInvariantStar_of_scn3Global_intermediate [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A R : Subgroup G}
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R) (hRlt : R < ⊤)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) :
    S07.ConjTransitiveOn (opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G)))
      (hInvariantStar ⊤ R {q}) := by
  classical
  have hA0 := hA
  obtain ⟨P, hAP, hAscn3⟩ := hA0
  have hAab : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hAscn2 : IsSCN_n p 2 (A.subgroupOf (P : Subgroup G)) :=
    IsSCN_n.mono (by norm_num) hAscn3
  have hHyp : S07.Hypothesis71 A := S07.hypothesis71_of_scn2 hG hAab hAp P hAP hAscn2
  have hπ : S07.primesOf A = ({p} : Set ℕ) := primesOf_eq_singleton_of_mem_scn3Global hA
  have hqA : q ∈ (S07.primesOf A)ᶜ := by
    rw [hπ]
    simpa [Set.mem_singleton_iff] using hqp
  have hRpi : Subgroup.IsPiSubgroup (S07.primesOf A) R := by
    rw [hπ]
    exact isPiSubgroup_singleton_of_isPGroup hRp
  have hAsub : Subgroup.IsSubnormal (A.subgroupOf R) :=
    subgroupOf_isSubnormal_of_isPGroup hRp
  have htransA : S07.ConjTransitiveOn (S07.kSubgroup A) (hInvariantStar ⊤ A {q}) := by
    have hT := S07.thompsonTransitivity hG (prime_dvd_card_of_mem_scn3Global hA) hA hqp
    simpa [S07.kSubgroup, hπ] using hT
  have hprop := S07.transitivity_propagates hG hHyp hqA R hRlt hRpi hAR hAsub htransA
  simpa [hπ] using hprop.2.1

/-- A conjugation-transitivity bookkeeping step for BG Lemma 9.5.

If `x` normalizes `R`, transitivity gives `k ∈ K` with `Q^k = Q^x`. Once both `K` and
`N_G(Q)` lie in `M`, this forces `x ∈ M`. -/
private theorem mem_of_mem_normalizer_of_conjTransitiveOn
    {K M R Q : Subgroup G} {q : ℕ} [Fact q.Prime] {x : G}
    (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hQ : Q ∈ hInvariantStar ⊤ R {q})
    (htrans : S07.ConjTransitiveOn K (hInvariantStar ⊤ R {q}))
    (hKleM : K ≤ M) (hNQleM : Subgroup.normalizer (Q : Set G) ≤ M) :
    x ∈ M := by
  classical
  have hxR_eq : MulAut.conj x • R = R :=
    conj_smul_eq_self_of_mem_normalizer hxR
  have hxQ : MulAut.conj x • Q ∈ hInvariantStar ⊤ R {q} :=
    conj_smul_mem_hInvariantStar_top_of_normalizer hQ hxR_eq
  obtain ⟨k, hkK, hkQ⟩ := htrans Q hQ (MulAut.conj x • Q) hxQ
  have hknorm : k⁻¹ * x ∈ Subgroup.normalizer (Q : Set G) := by
    apply mem_normalizer_of_conj_smul_eq_self
    calc MulAut.conj (k⁻¹ * x) • Q
        = MulAut.conj k⁻¹ • MulAut.conj x • Q := by
            rw [smul_smul, ← map_mul]
      _ = MulAut.conj k⁻¹ • MulAut.conj k • Q := by rw [← hkQ]
      _ = Q := by
            rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hkM : k ∈ M := hKleM hkK
  have hknormM : k⁻¹ * x ∈ M := hNQleM hknorm
  have hprod : k * (k⁻¹ * x) ∈ M := M.mul_mem hkM hknormM
  simpa [mul_assoc] using hprod

/-- BG Lemma 9.5's normalizer step after the `Q` and `(9.8)` witnesses have been supplied.

This packages the final use of Theorems 7.6 and 7.4: the transitivity bridge puts a
normalizer element of `R` in the fixed maximal subgroup `M`, provided `Q ∈ ℋ_G^*(R;q)` and
`N_G(Q) ≤ M` are already known. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate [Finite G]
    (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R Q : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p)
    (hQ : Q ∈ hInvariantStar ⊤ R {q})
    (hNQleM : Subgroup.normalizer (Q : Set G) ≤ M) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  have htrans :
      S07.ConjTransitiveOn
        (opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G)))
        (hInvariantStar ⊤ R {q}) :=
    conjTransitiveOn_hInvariantStar_of_scn3Global_intermediate hG hA hRp hAR hRlt hqp
  have hKleM :
      opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G)) ≤ M := by
    exact (opiCoreInG_le ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G))).trans
      ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAR)).trans hM.2)
  intro x hxR
  exact mem_of_mem_normalizer_of_conjTransitiveOn hxR hQ htrans hKleM hNQleM

/-- BG Lemma 9.5's L2573-L2589 normalizer step, with the `Q` package as input.

The low-rank and high-rank cases both produce a `Q ∈ ℋ_G^*(R;q)` with `N_G(Q) ≤ M`;
this helper consumes that uniform package and applies the Theorems 7.6/7.4 transitivity
bridge. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p)
    (hQpack :
      ∃ Q : Subgroup G,
        Q ∈ hInvariantStar ⊤ R {q} ∧
          opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  obtain ⟨Q, hQ, _hcoreQ, hNQleM⟩ := hQpack
  exact normalizer_le_maximal_of_scn3Global_intermediate
    hG hM hA hRp hAR hRlt hqp hQ hNQleM

/-- The `Q`-choice in BG Lemma 9.5.

If `R ≤ M`, then `R` normalizes `O_q(M)`, so `O_q(M)` lies in `ℋ_G(R;q)` and can be
extended to a maximal member of `ℋ_G^*(R;q)`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_of_le [Finite G]
    {q : ℕ} [Fact q.Prime] {M R : Subgroup G} (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧ opiCoreInG ({q} : Set ℕ) M ≤ Q := by
  classical
  have hcore : opiCoreInG ({q} : Set ℕ) M ∈ hInvariant ⊤ R {q} := by
    refine ⟨le_top, ?_, isPiSubgroup_opiCoreInG ({q} : Set ℕ) M⟩
    exact hRM.trans (le_normalizer_opiCoreInG ({q} : Set ℕ) M)
  exact exists_le_hInvariantStar hcore

/-- A member of `ℋ_G^*(R;q)` containing a Sylow `q`-subgroup is that Sylow subgroup. -/
private theorem hInvariantStar_eq_sylow_of_sylow_le [Finite G]
    {q : ℕ} [Fact q.Prime] (P : Sylow q G) {R Q : Subgroup G}
    (hQ : Q ∈ hInvariantStar ⊤ R {q}) (hPQ : (P : Subgroup G) ≤ Q) :
    Q = (P : Subgroup G) := by
  have hQp : IsPGroup q Q :=
    isPGroup_of_isPiSubgroup_singleton (hInvariantStar_isPiSubgroup hQ)
  exact P.is_maximal' hQp hPQ

/-- A nontrivial singleton core of a maximal subgroup has normalizer contained in that
maximal subgroup. -/
private theorem normalizer_opiCoreInG_singleton_le_maximal_of_ne_bot [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hOqne : opiCoreInG ({q} : Set ℕ) M ≠ ⊥) :
    Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) M : Set G) ≤ M := by
  haveI : IsSimpleGroup G := hG.simple
  have hMco : IsCoatom M := mem_maximalSubgroups.mp hM
  have hMleN : M ≤ Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) M : Set G) :=
    le_normalizer_opiCoreInG ({q} : Set ℕ) M
  have hNne : Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) M : Set G) ≠ ⊤ := by
    intro hNtop
    have hOq_normal : (opiCoreInG ({q} : Set ℕ) M).Normal :=
      Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases hG.simple.eq_bot_or_eq_top_of_normal (opiCoreInG ({q} : Set ℕ) M)
        inferInstance with hOqbot | hOqtop
    · exact hOqne hOqbot
    · have htop_le_M : ⊤ ≤ M := by
        rw [← hOqtop]
        exact opiCoreInG_le ({q} : Set ℕ) M
      exact hMco.lt_top.ne (eq_top_iff.mpr htop_le_M)
  exact (isCoatom_iff_ge_of_le.mp hMco).2 _ hNne hMleN

/-- If a subgroup is the ambient image of a Sylow `q`-subgroup of `M` and its ambient
normalizer is contained in `M`, then it is a Sylow `q`-subgroup of `G`.

This is the Sylow-normalizer bookkeeping in BG (9.7). -/
private theorem exists_sylow_eq_of_sylow_subgroupOf_and_normalizer_le [Finite G]
    {q : ℕ} [Fact q.Prime] {M O : Subgroup G} (PM : Sylow q ↥M)
    (hPMO : (PM : Subgroup ↥M).map M.subtype = O)
    (hNOM : Subgroup.normalizer (O : Set G) ≤ M) :
    ∃ P : Sylow q G, (P : Subgroup G) = O := by
  classical
  have hOp : IsPGroup q O := by
    rw [← hPMO]
    exact PM.isPGroup'.map M.subtype
  obtain ⟨S, hOS⟩ := hOp.exists_le_sylow
  have hSO : (S : Subgroup G) = O := by
    by_contra hS_ne_O
    have hOltS : O < (S : Subgroup G) :=
      lt_of_le_of_ne hOS (fun h => hS_ne_O h.symm)
    have hOltSN : O < (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G) :=
      S08.lt_inf_normalizer_of_isPGroup_lt S.isPGroup' hOltS
    have hSN_le_M : (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G) ≤ M :=
      inf_le_right.trans hNOM
    let K : Subgroup ↥M :=
      ((S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G)).subgroupOf M
    have hKp : IsPGroup q K := (S.isPGroup'.to_inf_left).comap_subtype
    have hPM_le_K : (PM : Subgroup ↥M) ≤ K := by
      intro x hx
      have hxO : (x : G) ∈ O := by
        rw [← hPMO]
        exact ⟨x, hx, rfl⟩
      change (x : G) ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G)
      exact (le_inf hOS Subgroup.le_normalizer) hxO
    have hK_eq_PM : K = (PM : Subgroup ↥M) := PM.is_maximal' hKp hPM_le_K
    have hSN_eq_O : (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G) = O := by
      calc
        (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G)
            = K.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hSN_le_M).symm
        _ = (PM : Subgroup ↥M).map M.subtype := by rw [hK_eq_PM]
        _ = O := hPMO
    exact (ne_of_lt hOltSN) hSN_eq_O.symm
  exact ⟨S, hSO⟩

/-- The `(9.7)` side of BG Lemma 9.5's `(9.8)` step, abstracted from the source of the
Sylow fact.

If the core `O_q(M)` is a Sylow `q`-subgroup of `G` and its normalizer lies in `M`, then
the `Q` chosen above has `N_G(Q) ≤ M`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_sylow
    [Finite G] {q : ℕ} [Fact q.Prime] {M R : Subgroup G} (P : Sylow q G)
    (hPcore : (P : Subgroup G) = opiCoreInG ({q} : Set ℕ) M) (hRM : R ≤ M)
    (hNPM : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  obtain ⟨Q, hQ, hcoreQ⟩ := exists_hInvariantStar_containing_opiCoreInG_of_le (q := q) hRM
  have hPQ : (P : Subgroup G) ≤ Q := (le_of_eq hPcore).trans hcoreQ
  have hQeq : Q = (P : Subgroup G) := hInvariantStar_eq_sylow_of_sylow_le P hQ hPQ
  refine ⟨Q, hQ, hcoreQ, ?_⟩
  rw [hQeq]
  exact hNPM

/-- Low-rank `(9.7)` package once Theorem 4.20(c) has identified `O_q(M)` as the
ambient image of a Sylow `q`-subgroup of `M`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hOqne : opiCoreInG ({q} : Set ℕ) M ≠ ⊥) (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  have hNcoreM : Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) M : Set G) ≤ M :=
    normalizer_opiCoreInG_singleton_le_maximal_of_ne_bot hG hM hOqne
  obtain ⟨P, hPcore⟩ :=
    exists_sylow_eq_of_sylow_subgroupOf_and_normalizer_le PM hPMcore hNcoreM
  have hNPM : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M := by
    rw [hPcore]
    exact hNcoreM
  exact exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_sylow
    P hPcore hRM hNPM

/-- If a local Sylow `q`-subgroup maps onto `O_q(M)` and `q ∈ π(M)`, then
`O_q(M)` is nontrivial. -/
private theorem opiCoreInG_singleton_ne_bot_of_local_sylow_eq_of_mem_primeFactors
    [Finite G] {q : ℕ} [Fact q.Prime] {M : Subgroup G} (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) :
    opiCoreInG ({q} : Set ℕ) M ≠ ⊥ := by
  classical
  have hq_dvd_M : q ∣ Nat.card ↥M := (Nat.mem_primeFactors.mp hqM).2.1
  have hPMne : (PM : Subgroup ↥M) ≠ ⊥ :=
    OddOrder.Isaacs.Ch07.Sylow.ne_bot_of_dvd_card hq_dvd_M PM
  intro hOqbot
  have hPMmap_bot : (PM : Subgroup ↥M).map M.subtype = ⊥ := by
    rw [hPMcore, hOqbot]
  have hPMbot : (PM : Subgroup ↥M) = ⊥ := by
    apply (Subgroup.map_subtype_inj (H := M)).mp
    simpa [Subgroup.map_bot] using hPMmap_bot
  exact hPMne hPMbot

/-- Low-rank `(9.7)` package when Theorem 4.20(c) has supplied only the local Sylow
equality; nontriviality follows from `q ∈ π(M)`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow_eq
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  exact exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow
    hG hM PM hPMcore
    (opiCoreInG_singleton_ne_bot_of_local_sylow_eq_of_mem_primeFactors PM hPMcore hqM)
    hRM

/-- Convert the local `O_q(M)` notation used by the §4 endpoint into the ambient
`opiCoreInG` notation used in §9. -/
private theorem local_sylow_map_eq_opiCoreInG_of_eq_opCore
    [Finite G] {q : ℕ} [Fact q.Prime] {M : Subgroup G} (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M) = Ch01.opCore q ↥M) :
    (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M := by
  rw [hPMcore, opiCoreInG, OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := ↥M) q]

/-- Low-rank `(9.7)` package with the natural §4-shaped input
`(P_M : Subgroup M) = O_q(M)`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_opCore
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M) = Ch01.opCore q ↥M)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  exact exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow_eq
    hG hM PM (local_sylow_map_eq_opiCoreInG_of_eq_opCore PM hPMcore) hqM hRM

/-- Low-rank `(9.7)` package when §4 has supplied a normal local Sylow subgroup. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_normal_local_sylow
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (PM : Sylow q ↥M)
    (hPMnorm : (PM : Subgroup ↥M).Normal)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  exact exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_opCore
    hG hM PM (Ch01.Sylow.eq_opCore_of_normal PM hPMnorm) hqM hRM

/-- A rank-three `q`-subgroup is nontrivial. -/
private theorem ne_bot_of_isPGroup_of_three_le_rank [Finite G]
    {q : ℕ} [Fact q.Prime] {B : Subgroup G} (hBq : IsPGroup q B)
    (hBrank : 3 ≤ rank ↥B) :
    B ≠ ⊥ := by
  have h3pRankB : 3 ≤ pRank ↥B q :=
    three_le_pRank_of_isPGroup_of_three_le_rank hBq hBrank
  have hq_dvd_B : q ∣ Nat.card B :=
    (Nat.mem_primeFactors.mp
      (mem_primeFactors_card_of_pos_pRank (H := ↥B) (p := q) (by omega))).2.1
  intro hBbot
  rw [hBbot, Subgroup.card_bot] at hq_dvd_B
  exact (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp hq_dvd_B)

/-- If a uniquely maximal subgroup `B` lies in both a fixed maximal subgroup `M` and a
nontrivial `q`-subgroup `Q`, then the normalizer of `Q` lies in `M`.

This is the uniqueness bookkeeping behind BG Lemma 9.5's high-rank `(9.8)` step. -/
private theorem normalizer_le_maximal_of_isUniquelyMaximal_le [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M B Q : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hBU : IsUniquelyMaximal B)
    (hBM : B ≤ M) (hBQ : B ≤ Q) (hQne : Q ≠ ⊥)
    (hQpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) Q) :
    Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  have hQlt : Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hQtop
    have hQp : IsPGroup q Q := isPGroup_of_isPiSubgroup_singleton hQpi
    have hGp : IsPGroup q G :=
      (hQtop ▸ hQp : IsPGroup q ↥(⊤ : Subgroup G)).of_surjective
        (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom
        Subgroup.topEquiv.surjective
    haveI : Group.IsNilpotent G := hGp.isNilpotent
    exact hG.notSolvable inferInstance
  obtain ⟨N, hNco, hQN⟩ := (eq_top_or_exists_le_coatom Q).resolve_left hQlt.ne
  have hN_eq_M : N = M :=
    hBU.eq_of_isCoatom_of_le hNco (hBQ.trans hQN) (mem_maximalSubgroups.mp hM) hBM
  have hQM : Q ≤ M := hQN.trans (le_of_eq hN_eq_M)
  obtain ⟨L, hL, hNQleL⟩ :=
    S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal hG hM hQne hQM
  have hB_le_L : B ≤ L := hBQ.trans (Subgroup.le_normalizer.trans hNQleL)
  have hL_eq_M : L = M :=
    hBU.eq_of_isCoatom_of_le (mem_maximalSubgroups.mp hL) hB_le_L
      (mem_maximalSubgroups.mp hM) hBM
  exact hNQleL.trans (le_of_eq hL_eq_M)

/-- High-rank `(9.8)` bookkeeping once a rank-three subgroup inside `O_q(M)` has been
chosen.

Lemma 9.4 makes the rank-three subgroup uniquely maximal; uniqueness then forces the
normalizer of the chosen `Q ∈ ℋ_G^*(R;q)` into the fixed maximal subgroup `M`. -/
private theorem normalizer_hInvariantStar_le_maximal_of_rank_three_opiCoreInG_witness
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R Q : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q)
    (hQ : Q ∈ hInvariantStar ⊤ R {q}) (hOqQ : opiCoreInG ({q} : Set ℕ) M ≤ Q)
    (hwit :
      ∃ B : Subgroup G,
        IsMulCommutative B ∧ IsPGroup q B ∧ 3 ≤ rank ↥B ∧
          B ≤ opiCoreInG ({q} : Set ℕ) M) :
    Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  obtain ⟨B, hBab, hBq, hBrank, hBcore⟩ := hwit
  have hBU : IsUniquelyMaximal B :=
    (abelian_rank_three_isUniquelyMaximal_of_fitting hG hM h3Fq) B hBab hBq hBrank
  have hBM : B ≤ M := hBcore.trans (opiCoreInG_le ({q} : Set ℕ) M)
  have hBQ : B ≤ Q := hBcore.trans hOqQ
  have hBne : B ≠ ⊥ := ne_bot_of_isPGroup_of_three_le_rank hBq hBrank
  have hQne : Q ≠ ⊥ := by
    intro hQbot
    exact hBne (le_bot_iff.mp (hBQ.trans (le_of_eq hQbot)))
  exact normalizer_le_maximal_of_isUniquelyMaximal_le hG hM hBU hBM hBQ hQne
    (hInvariantStar_isPiSubgroup hQ)

/-- A high `q`-rank Fitting subgroup supplies a rank-three abelian `q`-subgroup inside
`O_q(M)`.

The point is that the elementary abelian witness in `F(M)` lies in `O_q(F(M))` by
nilpotence, and `O_q(F(M)) ≤ O_q(M)`. -/
private theorem exists_rank_three_abelian_le_opiCoreInG_of_three_le_pRank_fittingInG
    [Finite G] {q : ℕ} [Fact q.Prime] {M : Subgroup G}
    (h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q) :
    ∃ B : Subgroup G,
      IsMulCommutative B ∧ IsPGroup q B ∧ 3 ≤ rank ↥B ∧
        B ≤ opiCoreInG ({q} : Set ℕ) M := by
  classical
  obtain ⟨B, hBmax, hBrank⟩ :=
    exists_isMaxElemAbelianIn_rank_three_of_three_le_pRank
      (H := S08.fittingInG M) h3Fq
  have hBea : B.IsElementaryAbelian q :=
    S08.isMaxElemAbelianIn_isElementaryAbelian hBmax
  have hBab : IsMulCommutative B := IsMulCommutative.of_comm hBea.comm
  have hBq : IsPGroup q B := hBea.isPGroup
  have hBF : B ≤ S08.fittingInG M := S08.isMaxElemAbelianIn_le hBmax
  have hBOF : B ≤ opiCoreInG ({q} : Set ℕ) (S08.fittingInG M) :=
    S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
      (S08.fittingInG_isNilpotent M) hBF hBq
  have hBOM : B ≤ opiCoreInG ({q} : Set ℕ) M :=
    hBOF.trans (S08.opiCoreInG_fittingInG_le_opiCoreInG ({q} : Set ℕ) M)
  exact ⟨B, hBab, hBq, hBrank, hBOM⟩

/-- The high-rank side of BG Lemma 9.5's `(9.8)` package.

If `r_q(F(M)) ≥ 3`, the `Q ∈ ℋ_G^*(R;q)` chosen to contain `O_q(M)` has
`N_G(Q) ≤ M`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_high_pRank
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q)
    (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  obtain ⟨Q, hQ, hcoreQ⟩ := exists_hInvariantStar_containing_opiCoreInG_of_le (q := q) hRM
  refine ⟨Q, hQ, hcoreQ, ?_⟩
  exact normalizer_hInvariantStar_le_maximal_of_rank_three_opiCoreInG_witness
    hG hM h3Fq hQ hcoreQ
    (exists_rank_three_abelian_le_opiCoreInG_of_three_le_pRank_fittingInG h3Fq)

/-- Low-rank version of the BG Lemma 9.5 normalizer step, after Thm 4.20(c) has supplied
`O_q(M)` as the ambient image of a Sylow `q`-subgroup of `M`. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_local_sylow
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p) (hRM : R ≤ M) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hOqne : opiCoreInG ({q} : Set ℕ) M ≠ ⊥) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    hG hM hA hRp hAR hRlt hqp
    (exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow
      hG hM.1 PM hPMcore hOqne hRM)

/-- Low-rank normalizer step when Theorem 4.20(c) has supplied the local Sylow equality;
nontriviality follows from `q ∈ π(M)`. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_local_sylow_eq
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p) (hRM : R ≤ M) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    hG hM hA hRp hAR hRlt hqp
    (exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow_eq
      hG hM.1 PM hPMcore hqM hRM)

/-- Low-rank normalizer step with the natural §4-shaped input
`(P_M : Subgroup M) = O_q(M)`. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_local_opCore
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p) (hRM : R ≤ M) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M) = Ch01.opCore q ↥M)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    hG hM hA hRp hAR hRlt hqp
    (exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_opCore
      hG hM.1 PM hPMcore hqM hRM)

/-- Low-rank normalizer step when §4 has supplied a normal local Sylow subgroup. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_normal_local_sylow
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p) (hRM : R ≤ M) (PM : Sylow q ↥M)
    (hPMnorm : (PM : Subgroup ↥M).Normal)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    hG hM hA hRp hAR hRlt hqp
    (exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_normal_local_sylow
      hG hM.1 PM hPMnorm hqM hRM)

/-- Low-rank normalizer step when §4 supplies a positive-length characteristic
Sylow series for the local maximal subgroup. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_characteristicSylowSeries
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hRM : R ≤ M)
    (S : OddOrder.BG.Ch1.S04.CharacteristicSylowSeries ↥M) (hpos : 0 < S.length)
    (hterminal_mem :
      ∀ i : Fin S.length,
        i.succ = Fin.last S.length → (S.step i).q ∈ (Nat.card ↥M).primeFactors)
    (hterminal_ne :
      ∀ i : Fin S.length, i.succ = Fin.last S.length → (S.step i).q ≠ p) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  obtain ⟨i, hi, PM, hPMnorm⟩ :=
    OddOrder.BG.Ch1.S04.CharacteristicSylowSeries.exists_normal_sylow_of_length_pos S hpos
  haveI : Fact (S.step i).q.Prime := (S.step i).q_prime
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_normal_local_sylow
    hG hM hA hRp hAR hRlt (hterminal_ne i hi) hRM PM hPMnorm (hterminal_mem i hi)

/-- In the low-rank Lemma 9.5 branch, the terminal normal local Sylow label
cannot be the ambient `SCN₃` prime. -/
private theorem normal_sylow_label_ne_of_scn3Global_of_pRank_fittingInG_le_two
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {A M : Subgroup G}
    (hA : A ∈ S07.scn3Global p G) (hAM : A ≤ M)
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2)
    (PM : Sylow q ↥M) (hPMnorm : (PM : Subgroup ↥M).Normal) :
    q ≠ p := by
  classical
  intro hqp
  subst q
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hArank : 3 ≤ rank ↥A := three_le_rank_of_mem_scn3Global hA
  have h3A : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp hArank
  let AM : Subgroup ↥M := A.subgroupOf M
  have hAMp : IsPGroup p AM :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAM).symm
  obtain ⟨P, hAMP⟩ := hAMp.exists_le_sylow
  haveI : Unique (Sylow p ↥M) := Sylow.unique_of_normal PM hPMnorm
  have hAM_PM : AM ≤ (PM : Subgroup ↥M) := by
    have hP_eq : P = PM := Subsingleton.elim P PM
    rwa [← hP_eq]
  have hA_PM_map : A ≤ (PM : Subgroup ↥M).map M.subtype := by
    calc
      A = AM.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hAM).symm
      _ ≤ (PM : Subgroup ↥M).map M.subtype := Subgroup.map_mono hAM_PM
  have hPMcore : (PM : Subgroup ↥M) = Ch01.opCore p ↥M :=
    Ch01.Sylow.eq_opCore_of_normal PM hPMnorm
  have hPMfit : (PM : Subgroup ↥M).map M.subtype ≤ S08.fittingInG M := by
    rw [hPMcore, ← OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := ↥M) p]
    change opiCoreInG ({p} : Set ℕ) M ≤ S08.fittingInG M
    exact S08.opiCoreInG_singleton_le_fittingInG M
  have hAF : A ≤ S08.fittingInG M := hA_PM_map.trans hPMfit
  have h3F : 3 ≤ pRank ↥(S08.fittingInG M) p :=
    h3A.trans
      (pRank_le_of_injective (f := Subgroup.inclusion hAF)
        (Subgroup.inclusion_injective hAF))
  omega

/-- Low-rank normalizer step when §4 supplies a positive-length characteristic
Sylow series and Lemma 9.5 has already established `r_p(F(M)) ≤ 2`. -/
private theorem normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_lowRank
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hRM : R ≤ M)
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2)
    (S : OddOrder.BG.Ch1.S04.CharacteristicSylowSeries ↥M) (hpos : 0 < S.length)
    (hterminal_mem :
      ∀ i : Fin S.length,
        i.succ = Fin.last S.length → (S.step i).q ∈ (Nat.card ↥M).primeFactors) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  have hAab : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hA_le_C : A ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (isMulCommutative_iff.mp hAab ⟨y, hy⟩ ⟨x, hx⟩)
  have hAM : A ≤ M := hA_le_C.trans hM.2
  refine normalizer_le_maximal_of_scn3Global_intermediate_of_characteristicSylowSeries
    hG hM hA hRp hAR hRlt hRM S hpos hterminal_mem ?_
  intro i hi
  obtain ⟨PM, hPMnorm⟩ :=
    OddOrder.BG.Ch1.S04.CharacteristicSylowSeries.exists_normal_sylow_of_terminal_step S i hi
  haveI : Fact (S.step i).q.Prime := (S.step i).q_prime
  exact normal_sylow_label_ne_of_scn3Global_of_pRank_fittingInG_le_two
    hA hAM hFp PM hPMnorm

/-- High-rank version of the BG Lemma 9.5 normalizer step, using Lemma 9.4 through the
rank-three witness inside `O_q(M)`. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_high_pRank
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p) (hRM : R ≤ M)
    (h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    hG hM hA hRp hAR hRlt hqp
    (exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_high_pRank
      hG hM.1 h3Fq hRM)

/-- If the overall rank is at least three but the fixed `p`-rank is at most two,
then some other prime has rank at least three. -/
private theorem exists_pRank_ge_three_ne_of_rank_ge_three_of_pRank_le_two
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hrank : 3 ≤ rank H) (hp : pRank H p ≤ 2) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ 3 ≤ pRank H q := by
  obtain ⟨q, hq, h3q⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := H) (n := 3) (by norm_num) hrank
  refine ⟨q, hq, ?_, h3q⟩
  intro hqp
  subst q
  omega

/-- BG Lemma 9.5 rank-case normalizer adapter.

The low-rank branch consumes the §4 characteristic Sylow series package, while the
high-rank branch chooses a prime `q ≠ p` with `r_q(F(M)) ≥ 3` and applies Lemma 9.4. -/
private theorem normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_rankCases
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hRM : R ≤ M)
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2)
    (S : OddOrder.BG.Ch1.S04.CharacteristicSylowSeries ↥M) (hpos : 0 < S.length)
    (hterminal_mem :
      ∀ i : Fin S.length,
        i.succ = Fin.last S.length → (S.step i).q ∈ (Nat.card ↥M).primeFactors) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  by_cases hrank : rank ↥(S08.fittingInG M) ≤ 2
  · exact normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_lowRank
      hG hM hA hRp hAR hRlt hRM hFp S hpos hterminal_mem
  · have h3rank : 3 ≤ rank ↥(S08.fittingInG M) := by omega
    obtain ⟨q, hq, hqp, h3Fq⟩ :=
      exists_pRank_ge_three_ne_of_rank_ge_three_of_pRank_le_two
        (H := ↥(S08.fittingInG M)) (p := p) h3rank hFp
    haveI : Fact q.Prime := ⟨hq⟩
    exact normalizer_le_maximal_of_scn3Global_intermediate_of_high_pRank
      hG hM hA hRp hAR hRlt hqp hRM h3Fq

/-- BG Lemma 9.5 normalizer step specialized to `R = A`.

After the rank-case normalizer adapter has been supplied with the §4 characteristic
Sylow series package, the first application gives `N_G(A) ≤ M`. -/
private theorem normalizer_scn3_self_le_maximal_of_rankCases
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G)
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2)
    (S : OddOrder.BG.Ch1.S04.CharacteristicSylowSeries ↥M) (hpos : 0 < S.length)
    (hterminal_mem :
      ∀ i : Fin S.length,
        i.succ = Fin.last S.length → (S.step i).q ∈ (Nat.card ↥M).primeFactors) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  classical
  have hAab : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hA_le_C : A ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (isMulCommutative_iff.mp hAab ⟨y, hy⟩ ⟨x, hx⟩)
  have hAM : A ≤ M := hA_le_C.trans hM.2
  have hAlt : A < ⊤ :=
    lt_of_le_of_lt hA_le_C (centralizer_lt_top_of_mem_scn3Global hG hA)
  exact normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_rankCases
    hG hM hA (isPGroup_of_mem_scn3Global hA) le_rfl hAlt hAM hFp S hpos
    hterminal_mem

/-- BG Lemma 9.5 normalizer step specialized to a `p`-subgroup of `N_G(A)`.

The `R = A` instance first puts every chosen `P ≤ N_G(A)` inside `M`; the rank-case
adapter can then be applied with `R = P` to obtain `N_G(P) ≤ M`. -/
private theorem normalizer_scn3_sylowNormalizer_le_maximal_of_rankCases
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M P : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hPp : IsPGroup p P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2)
    (S : OddOrder.BG.Ch1.S04.CharacteristicSylowSeries ↥M) (hpos : 0 < S.length)
    (hterminal_mem :
      ∀ i : Fin S.length,
        i.succ = Fin.last S.length → (S.step i).q ∈ (Nat.card ↥M).primeFactors) :
    P ≤ M ∧ Subgroup.normalizer (P : Set G) ≤ M := by
  classical
  have hNAleM : Subgroup.normalizer (A : Set G) ≤ M :=
    normalizer_scn3_self_le_maximal_of_rankCases hG hM hA hFp S hpos hterminal_mem
  have hPM : P ≤ M := hPnormA.trans hNAleM
  have hMlt : M < ⊤ := (mem_maximalSubgroups.mp hM.1).lt_top
  have hPlt : P < ⊤ := lt_of_le_of_lt hPM hMlt
  exact ⟨hPM,
    normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_rankCases
      hG hM hA hPp hAP hPlt hPM hFp S hpos hterminal_mem⟩

/-- If an `SCN₃(p)` subgroup is a counterexample to uniqueness, then every maximal
subgroup has `pRank F(M) ≤ 2`.

This is the first reduction in BG Lemma 9.5: otherwise Lemma 9.4 would put the
rank-three abelian `p`-subgroup `A` itself in `𝒰`. -/
private theorem pRank_fittingInG_le_two_of_not_scn3_isUniquelyMaximal [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hA : A ∈ S07.scn3Global p G)
    (hAnot : ¬ IsUniquelyMaximal A) :
    pRank ↥(S08.fittingInG M) p ≤ 2 := by
  classical
  by_contra hnot
  have h3F : 3 ≤ pRank ↥(S08.fittingInG M) p := by omega
  have hAab : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hArank : 3 ≤ rank ↥A := three_le_rank_of_mem_scn3Global hA
  exact hAnot
    ((abelian_rank_three_isUniquelyMaximal_of_fitting hG hM h3F) A hAab hAp hArank)

/-- The opening choice in BG Lemma 9.5, bundled with the rank cut (9.6).

For a counterexample `A ∈ SCN₃(p)` with `A ∉ 𝒰`, choose `M ∈ 𝓜(C_G(A))`; then Lemma 9.4
implies `r_p(F(M)) ≤ 2`. -/
private theorem exists_maximal_centralizer_and_pRank_fittingInG_le_two_of_not_scn3
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A) :
    ∃ M : Subgroup G,
      M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) ∧
        pRank ↥(S08.fittingInG M) p ≤ 2 := by
  classical
  obtain ⟨M, hMcont⟩ := exists_maximalSubgroupsContaining_centralizer_of_mem_scn3Global hG hA
  have hM : M ∈ maximalSubgroups G := hMcont.1
  exact ⟨M, hMcont, pRank_fittingInG_le_two_of_not_scn3_isUniquelyMaximal hG hM hA hAnot⟩

/-- Counterexample version of the `R = A` normalizer step in BG Lemma 9.5.

The rank cut `(9.6)` is derived internally from `A ∉ 𝒰`. -/
private theorem normalizer_scn3_self_le_maximal_of_not_scn3
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (S : OddOrder.BG.Ch1.S04.CharacteristicSylowSeries ↥M) (hpos : 0 < S.length)
    (hterminal_mem :
      ∀ i : Fin S.length,
        i.succ = Fin.last S.length → (S.step i).q ∈ (Nat.card ↥M).primeFactors) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  have hFp : pRank ↥(S08.fittingInG M) p ≤ 2 :=
    pRank_fittingInG_le_two_of_not_scn3_isUniquelyMaximal hG hM.1 hA hAnot
  exact normalizer_scn3_self_le_maximal_of_rankCases hG hM hA hFp S hpos
    hterminal_mem

/-- Counterexample version of the `R = P` normalizer step in BG Lemma 9.5.

Once `P` is a `p`-subgroup between `A` and `N_G(A)`, the rank cut `(9.6)` and the
`R = A` instance put `P` inside `M`, and the rank-case adapter gives `N_G(P) ≤ M`. -/
private theorem normalizer_scn3_pSubgroup_le_maximal_of_not_scn3
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M P : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hPp : IsPGroup p P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (S : OddOrder.BG.Ch1.S04.CharacteristicSylowSeries ↥M) (hpos : 0 < S.length)
    (hterminal_mem :
      ∀ i : Fin S.length,
        i.succ = Fin.last S.length → (S.step i).q ∈ (Nat.card ↥M).primeFactors) :
    P ≤ M ∧ Subgroup.normalizer (P : Set G) ≤ M := by
  have hFp : pRank ↥(S08.fittingInG M) p ≤ 2 :=
    pRank_fittingInG_le_two_of_not_scn3_isUniquelyMaximal hG hM.1 hA hAnot
  exact normalizer_scn3_sylowNormalizer_le_maximal_of_rankCases
    hG hM hA hPp hAP hPnormA hFp S hpos hterminal_mem

/-- Choose an ambient `p`-subgroup between a global `SCN₃(p)` subgroup and its normalizer.

This is the subgroup-level form of the BG choice of a Sylow `p`-subgroup of `N_G(A)`. -/
private theorem exists_pSubgroup_between_scn3_and_normalizer [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    ∃ P : Subgroup G,
      IsPGroup p P ∧ A ≤ P ∧ P ≤ Subgroup.normalizer (A : Set G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  let AN : Subgroup ↥N := A.subgroupOf N
  have hANp : IsPGroup p AN :=
    (isPGroup_of_mem_scn3Global hA).of_equiv (Subgroup.subgroupOfEquivOfLe hAN).symm
  obtain ⟨PN, hANPN⟩ := hANp.exists_le_sylow
  let P : Subgroup G := (PN : Subgroup ↥N).map N.subtype
  have hPp : IsPGroup p P := PN.isPGroup'.map N.subtype
  have hAP : A ≤ P := by
    calc
      A = AN.map N.subtype := (Subgroup.map_subgroupOf_eq_of_le hAN).symm
      _ ≤ (PN : Subgroup ↥N).map N.subtype := Subgroup.map_mono hANPN
  have hPN : P ≤ N := by
    dsimp [P]
    exact Subgroup.map_subtype_le (PN : Subgroup ↥N)
  exact ⟨P, hPp, hAP, hPN⟩

/-- BG Lemma 9.5 opening normalizer package for a chosen maximal subgroup over `C_G(A)`.

Given the §4 characteristic Sylow series package for `M`, a counterexample `A ∉ 𝒰`
supplies a `p`-subgroup `P` with `A ≤ P ≤ N_G(A)`, `P ≤ M`, and `N_G(P) ≤ M`. -/
private theorem exists_pSubgroup_normalizer_package_of_not_scn3
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (S : OddOrder.BG.Ch1.S04.CharacteristicSylowSeries ↥M) (hpos : 0 < S.length)
    (hterminal_mem :
      ∀ i : Fin S.length,
        i.succ = Fin.last S.length → (S.step i).q ∈ (Nat.card ↥M).primeFactors) :
    ∃ P : Subgroup G,
      IsPGroup p P ∧ A ≤ P ∧ P ≤ Subgroup.normalizer (A : Set G) ∧
        P ≤ M ∧ Subgroup.normalizer (P : Set G) ≤ M := by
  obtain ⟨P, hPp, hAP, hPnormA⟩ := exists_pSubgroup_between_scn3_and_normalizer hA
  have hpack : P ≤ M ∧ Subgroup.normalizer (P : Set G) ≤ M :=
    normalizer_scn3_pSubgroup_le_maximal_of_not_scn3
      hG hM hA hAnot hPp hAP hPnormA S hpos hterminal_mem
  exact ⟨P, hPp, hAP, hPnormA, hpack.1, hpack.2⟩

/-- BG Lemma 9.5 opening normalizer package, consuming the §4.20(c) downstream
characteristic Sylow series package directly. -/
private theorem exists_pSubgroup_normalizer_package_of_not_scn3_of_sylowSeriesPackage
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (SP : OddOrder.BG.Ch1.S04.CharacteristicSylowSeriesPackage ↥M) :
    ∃ P : Subgroup G,
      IsPGroup p P ∧ A ≤ P ∧ P ≤ Subgroup.normalizer (A : Set G) ∧
        P ≤ M ∧ Subgroup.normalizer (P : Set G) ≤ M :=
  exists_pSubgroup_normalizer_package_of_not_scn3 hG hM hA hAnot
    SP.series SP.length_pos SP.terminal_mem

/-- BG Lemma 9.5's Proposition 1.16 extraction step.

If `P0` does not centralize `D`, and a noncyclic abelian subgroup `A` normalizes `D`
coprimely, then among the cocyclic centralizers generating `D` there is one not centralized
by `P0`. This is the formal version of the line "Take `B ⊆ Ω₁(A)` such that
`Ω₁(A)/B` is cyclic and `P₀` does not centralize `C_D(B)`." -/
private theorem exists_cocyclic_not_le_centralizer_inf_centralizer_of_not_le_centralizer
    [Finite G] {A D P0 : Subgroup G} [IsMulCommutative ↥A]
    (hAD : A ≤ Subgroup.normalizer D)
    (hCop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥D))
    (hAnc : ¬ IsCyclic ↥A)
    (hP0D : ¬ P0 ≤ Subgroup.centralizer (D : Set G)) :
    ∃ B : Subgroup G,
      B ≤ A ∧ (∃ a ∈ A, B ⊔ Subgroup.zpowers a = A) ∧
        ¬ P0 ≤ Subgroup.centralizer
          ((D ⊓ Subgroup.centralizer (B : Set G)) : Set G) := by
  classical
  by_contra hnone
  have hAll :
      ∀ B : Subgroup G,
        B ≤ A → (∃ a ∈ A, B ⊔ Subgroup.zpowers a = A) →
          P0 ≤ Subgroup.centralizer
            ((D ⊓ Subgroup.centralizer (B : Set G)) : Set G) := by
    intro B hBA hcyc
    by_contra hnot
    exact hnone ⟨B, hBA, hcyc, hnot⟩
  have hDinv : Ch03.IsAInvariant (S07.conjAction A) D :=
    S07.isAInvariant_conjAction_iff.mpr hAD
  have htop :=
    OddOrder.BG.Ch1.S01.cocyclicFixedByClosure_eq_top_of_not_isCyclic
      hDinv.restrict hCop hAnc
  exact hP0D (by
    intro x hxP0
    rw [Subgroup.mem_centralizer_iff]
    intro d hdD
    let CxD : Subgroup ↥D :=
      (D ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf D
    have hclosure_le :
        OddOrder.BG.Ch1.S01.cocyclicFixedByClosure hDinv.restrict ≤ CxD := by
      rw [OddOrder.BG.Ch1.S01.cocyclicFixedByClosure, Subgroup.closure_le]
      rintro z ⟨Yb, ⟨a, hcycYb⟩, hfix⟩
      change (z : G) ∈ D ⊓ Subgroup.centralizer ({x} : Set G)
      set Y : Subgroup G := Yb.map A.subtype with hYdef
      have hYleA : Y ≤ A := by
        rw [hYdef]
        exact Subgroup.map_subtype_le Yb
      have hYcyc : ∃ a' ∈ A, Y ⊔ Subgroup.zpowers a' = A := by
        refine ⟨(a : G), a.2, ?_⟩
        have hzp : Subgroup.zpowers (a : G) = (Subgroup.zpowers a).map A.subtype :=
          (MonoidHom.map_zpowers A.subtype a).symm
        rw [hYdef, hzp, ← Subgroup.map_sup, hcycYb, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      have hzY : (z : G) ∈ D ⊓ Subgroup.centralizer (Y : Set G) := by
        refine ⟨z.2, ?_⟩
        change (z : G) ∈ Subgroup.centralizer (Y : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hyY
        rw [hYdef, Subgroup.coe_map, Set.mem_image] at hyY
        obtain ⟨yb, hyb, rfl⟩ := hyY
        have hval := congrArg (fun w : ↥D => (w : G)) (hfix yb hyb)
        change ((hDinv.restrict yb) z : G) = (z : G) at hval
        rw [Ch03.IsAInvariant.restrict_apply_val] at hval
        simp only [S07.conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype,
          MulAut.conj_apply] at hval
        exact mul_inv_eq_iff_eq_mul.mp hval
      refine ⟨z.2, ?_⟩
      change (z : G) ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      have hx_cent := (hAll Y hYleA hYcyc) hxP0
      exact (Subgroup.mem_centralizer_iff.mp hx_cent (z : G) hzY).symm
    have hdCx : (⟨d, hdD⟩ : ↥D) ∈ CxD := by
      apply hclosure_le
      rw [htop]
      exact Subgroup.mem_top _
    have hdc : d ∈ Subgroup.centralizer ({x} : Set G) := by
      simpa [CxD, Subgroup.mem_subgroupOf] using hdCx
    exact (Subgroup.mem_centralizer_iff.mp hdc x (Set.mem_singleton x)).symm)

/-- A cocyclic subgroup `Y` (`Y ⊔ ⟨b⟩ = B`) of an elementary abelian `p`-group `B`
of rank at least three is noncyclic. -/
private theorem not_isCyclic_of_cocyclic_elementary_rank_three [Finite G] {p : ℕ}
    (hp2 : 2 ≤ p) {B Y : Subgroup G}
    (hB_ea : B.IsElementaryAbelian p) (hlog : 3 ≤ Nat.log p (Nat.card ↥B))
    (hYB : Y ≤ B) {b : G} (hb : b ∈ B) (hsup : Y ⊔ Subgroup.zpowers b = B) :
    ¬ IsCyclic ↥Y := by
  classical
  haveI : IsMulCommutative ↥B := IsMulCommutative.of_comm hB_ea.1
  set Y' : Subgroup ↥B := Y.subgroupOf B with hY'
  set K : Subgroup ↥B := (Subgroup.zpowers b).subgroupOf B with hK
  haveI : Y'.Normal := Subgroup.normal_of_isMulCommutative _
  have hzple : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hb
  have hsup' : Y' ⊔ K = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_sup, hY', hK, Subgroup.map_subgroupOf_eq_of_le hYB,
      Subgroup.map_subgroupOf_eq_of_le hzple, hsup, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hKle : Nat.card ↥K ≤ p := by
    rw [hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzple).toEquiv, Nat.card_zpowers]
    refine Nat.le_of_dvd (by omega : 0 < p) (orderOf_dvd_of_pow_eq_one ?_)
    have hbp := congrArg Subtype.val (hB_ea.2 (⟨b, hb⟩ : ↥B))
    simpa using hbp
  have hKmap : K.map (QuotientGroup.mk' Y') = ⊤ := by
    have h1 : (Y' ⊔ K).map (QuotientGroup.mk' Y') = ⊤ := by
      rw [hsup', Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Y')]
    rwa [Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff Y').mpr (le_of_eq (QuotientGroup.ker_mk' Y').symm),
      bot_sup_eq] at h1
  have hquot_le : Nat.card (↥B ⧸ Y') ≤ Nat.card ↥K :=
    Nat.card_le_card_of_surjective ((QuotientGroup.mk' Y').comp K.subtype) (by
      intro x
      obtain ⟨k, hk, hkx⟩ := hKmap ▸ Subgroup.mem_top x
      exact ⟨⟨k, hk⟩, hkx⟩)
  have hcardB : Nat.card ↥B ≤ Nat.card ↥K * Nat.card ↥Y := by
    have hY'card : Nat.card ↥Y' = Nat.card ↥Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYB).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Y', hY'card]
    exact Nat.mul_le_mul_right _ hquot_le
  intro hcyc
  have hY_ea : Y.IsElementaryAbelian p := by
    refine ⟨fun x y => Subtype.ext ?_, fun x => Subtype.ext ?_⟩
    · change (x : G) * (y : G) = (y : G) * (x : G)
      exact congrArg (Subtype.val : ↥B → G)
        (hB_ea.1 ⟨(x : G), hYB x.2⟩ ⟨(y : G), hYB y.2⟩)
    · change (x : G) ^ p = 1
      exact congrArg (Subtype.val : ↥B → G)
        (hB_ea.2 (⟨(x : G), hYB x.2⟩ : ↥B))
  have hYle : Nat.card ↥Y ≤ p := by
    have hdvd : Monoid.exponent ↥Y ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      exact hY_ea.2
    rw [← hcyc.exponent_eq_card]
    exact Nat.le_of_dvd (by omega : 0 < p) hdvd
  have hp3 : p ^ 3 ≤ Nat.card ↥B :=
    (Nat.le_log_iff_pow_le (by omega : 1 < p) Nat.card_pos.ne').mp hlog
  have h1 : Nat.card ↥B ≤ p ^ 2 := by
    rw [pow_two]
    exact le_trans hcardB (Nat.mul_le_mul hKle hYle)
  have h2 : p ^ 2 < p ^ 3 :=
    Nat.pow_lt_pow_right (by omega : 1 < p) (by norm_num)
  omega

/-- If `A` has `pRank ≥ 3`, then its abelian `Ω₁(A)` has logarithmic size at least three. -/
private theorem three_le_log_card_omega1OfAbelian_of_three_le_pRank [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3A : 3 ≤ pRank A p) :
    3 ≤ Nat.log p
      (Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)) := by
  have hp3_dvd : p ^ 3 ∣
      Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) :=
    OddOrder.GroupTheory.pow_dvd_card_omega1OfAbelian_of_pos_le_pRank
      (G := G) (H := A) (p := p) (hH := hAcomm_set) (n := 3) (by norm_num) h3A
  have hp3_le : p ^ 3 ≤
      Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) :=
    Nat.le_of_dvd Nat.card_pos hp3_dvd
  exact (Nat.le_log_iff_pow_le (Fact.out : p.Prime).one_lt Nat.card_pos.ne').mpr hp3_le

/-- `Ω₁(A)` is noncyclic when `A` has `pRank ≥ 3`. -/
private theorem not_isCyclic_omega1OfAbelian_of_three_le_pRank [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3A : 3 ≤ pRank A p) :
    ¬ IsCyclic ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) := by
  exact not_isCyclic_of_isElementaryAbelian_of_two_le_log_card
    (OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
      (G := G) (H := A) (p := p) (hH := hAcomm_set))
    (by
      have hlog := three_le_log_card_omega1OfAbelian_of_three_le_pRank
        (G := G) (p := p) hAcomm_set h3A
      omega)

/-- A cocyclic subgroup of `Ω₁(A)` is noncyclic when `pRank A ≥ 3`. -/
private theorem not_isCyclic_of_cocyclic_omega1OfAbelian_of_three_le_pRank [Finite G]
    {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3A : 3 ≤ pRank A p)
    (hBΩ : B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)
    {a : G} (ha : a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)
    (hsup : B ⊔ Subgroup.zpowers a =
      OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) :
    ¬ IsCyclic ↥B := by
  exact not_isCyclic_of_cocyclic_elementary_rank_three
    (G := G) (p := p) (hp2 := (Fact.out : p.Prime).two_le)
    (B := OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) (Y := B)
    (OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
      (G := G) (H := A) (p := p) (hH := hAcomm_set))
    (three_le_log_card_omega1OfAbelian_of_three_le_pRank
      (G := G) (p := p) hAcomm_set h3A)
    hBΩ ha hsup

/-- BG Lemma 9.5's Prop 1.16 extraction specialized to `Ω₁(A)` under `pRank A ≥ 3`.

The output packages the cocyclic subgroup `B ≤ Ω₁(A)` with the extra facts needed for the
next step of the Lemma 9.5 contradiction: `B ≤ A`, `B` is noncyclic, and `P0` still does
not centralize `D ∩ C_G(B)`. -/
private theorem exists_noncyclic_cocyclic_omega1OfAbelian_not_le_centralizer_inf
    [Finite G] {p : ℕ} [Fact p.Prime] {A D P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3A : 3 ≤ pRank A p)
    (hΩD : OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ≤ Subgroup.normalizer D)
    (hCop : Nat.Coprime
      (Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)) (Nat.card ↥D))
    (hP0D : ¬ P0 ≤ Subgroup.centralizer (D : Set G)) :
    ∃ B : Subgroup G,
      B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ∧
      B ≤ A ∧ ¬ IsCyclic ↥B ∧
      (∃ a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set,
        B ⊔ Subgroup.zpowers a = OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) ∧
      ¬ P0 ≤ Subgroup.centralizer
        ((D ⊓ Subgroup.centralizer (B : Set G)) : Set G) := by
  classical
  let ΩA : Subgroup G := OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set
  have hΩea : ΩA.IsElementaryAbelian p := by
    simpa [ΩA] using
      (OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
        (G := G) (H := A) (p := p) (hH := hAcomm_set))
  haveI : IsMulCommutative ↥ΩA := IsMulCommutative.of_comm hΩea.1
  have hΩAnc : ¬ IsCyclic ↥ΩA := by
    simpa [ΩA] using
      (not_isCyclic_omega1OfAbelian_of_three_le_pRank
        (G := G) (p := p) (A := A) hAcomm_set h3A)
  obtain ⟨B, hBΩ, hcycpack, hnot⟩ :=
    exists_cocyclic_not_le_centralizer_inf_centralizer_of_not_le_centralizer
      (A := ΩA) (D := D) (P0 := P0) (by simpa [ΩA] using hΩD)
      (by simpa [ΩA] using hCop) hΩAnc hP0D
  rcases hcycpack with ⟨a, haΩ, hsup⟩
  have hBΩ_raw : B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set := by
    simpa [ΩA] using hBΩ
  have haΩ_raw : a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set := by
    simpa [ΩA] using haΩ
  have hsup_raw : B ⊔ Subgroup.zpowers a =
      OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set := by
    simpa [ΩA] using hsup
  refine ⟨B, hBΩ_raw, ?_, ?_, ⟨a, haΩ_raw, hsup_raw⟩, hnot⟩
  · exact hBΩ_raw.trans (OddOrder.GroupTheory.omega1OfAbelian_le (G := G) (H := A)
      (p := p) (hH := hAcomm_set))
  · exact not_isCyclic_of_cocyclic_omega1OfAbelian_of_three_le_pRank
      (G := G) (p := p) (A := A) (B := B) hAcomm_set h3A hBΩ_raw haΩ_raw hsup_raw


/-- Lemma 9.5's Prop. 1.16 extraction with `D = O_{p'}(F(M))`.

For `M ∈ ℳ(C_G(A))` and `A ∈ SCN₃(p)`, the subgroup `Ω₁(A)` normalizes
`O_{p'}(F(M))`: `A ≤ C_G(A) ≤ M`, `M` normalizes `F(M)`, and the ambient
`p'`-core is characteristic in `F(M)`. Since `Ω₁(A)` is a `p`-group and
`O_{p'}(F(M))` is a `p'`-subgroup, the action is coprime. This packages the
exact input needed for the BG L2590--L2613 contradiction block. -/
private theorem exists_cocyclic_omega1_not_le_cent_inf_opiCoreFitting
    [Finite G] {p : ℕ} [Fact p.Prime] {A M P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G)
    (hP0D : ¬ P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G)) :
    ∃ B : Subgroup G,
      B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ∧
      B ≤ A ∧ ¬ IsCyclic ↥B ∧
      (∃ a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set,
        B ⊔ Subgroup.zpowers a =
          OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) ∧
      ¬ P0 ≤ Subgroup.centralizer
        (((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ⊓
            Subgroup.centralizer (B : Set G)) : Set G) := by
  classical
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  have h3A : 3 ≤ pRank A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank
      (isPGroup_of_mem_scn3Global hA) (three_le_rank_of_mem_scn3Global hA)
  haveI hAcomm_inst : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hA_le_M : A ≤ M := by
    exact (Subgroup.le_centralizer A).trans hM.2
  have hM_norm_F : M ≤ Subgroup.normalizer (S08.fittingInG M : Set G) := by
    intro x hxM
    exact S08.mem_normalizer_fittingInG_of_mem hxM
  have hA_norm_F : A ≤ Subgroup.normalizer (S08.fittingInG M : Set G) :=
    hA_le_M.trans hM_norm_F
  have hOmegaD : OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ≤
      Subgroup.normalizer D := by
    exact (OddOrder.GroupTheory.omega1OfAbelian_le (G := G) (H := A)
      (p := p) (hH := hAcomm_set)).trans
        (le_normalizer_opiCoreInG_of_le_normalizer ({p} : Set ℕ)ᶜ hA_norm_F)
  have hOmegapi : Subgroup.IsPiSubgroup ({p} : Set ℕ)
      (OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) :=
    isPiSubgroup_singleton_of_isPGroup
      (OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
        (G := G) (H := A) (p := p) (hH := hAcomm_set)).isPGroup
  have hDpic : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ D := by
    simpa [D] using
      (isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M))
  have hCop : Nat.Coprime
      (Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)) (Nat.card ↥D) :=
    coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl hOmegapi hDpic
  simpa [D] using
    (exists_noncyclic_cocyclic_omega1OfAbelian_not_le_centralizer_inf
      (G := G) (p := p) (A := A) (D := D) (P0 := P0)
      hAcomm_set h3A hOmegaD hCop (by simpa [D] using hP0D))

/-- **BG Lemma 9.5** (mmd L2559): `p` prime, `A ∈ SCN₃(p)` ⇒ `A ∈ 𝒰`。

Proof gate: mmd L2579 uses Thm 7.6 and Thm 7.4; L2605 uses Cor 4.19; L2615 uses
Thm 4.20. The `SCN₃(p)` input is the right interface, so no §5 narrow or Thm 4.16
assumption should be introduced here. -/
theorem scn3_isUniquelyMaximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    IsUniquelyMaximal A := by
  sorry

/-- A local `SCN₃(P)` subgroup of a Sylow subgroup, viewed in `G`, is a global
`SCN₃(p)` subgroup. -/
private theorem scn3Global_of_scn3_sylow [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {A : Subgroup ↥(P : Subgroup G)}
    (hA : IsSCN₃ p A) :
    A.map (P : Subgroup G).subtype ∈ S07.scn3Global p G := by
  classical
  have hAP : A.map (P : Subgroup G).subtype ≤ (P : Subgroup G) :=
    Subgroup.map_subtype_le A
  refine ⟨P, hAP, ?_⟩
  have htarget :
      (A.map (P : Subgroup G).subtype).subgroupOf (P : Subgroup G) = A := by
    apply (Subgroup.map_subtype_inj (H := (P : Subgroup G))).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hAP]
  rwa [htarget]

/-- If `K` has rank at least two, then `C_G(K)` is proper. -/
private theorem centralizer_lt_top_of_two_le_rank [Finite G] (hG : IsMinimalSimpleOdd G)
    {K : Subgroup G} (hr : 2 ≤ rank ↥K) :
    Subgroup.centralizer (K : Set G) < ⊤ := by
  classical
  have hZbot : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact absurd (isSolvable_of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm) hG.notSolvable
  have hKne : K ≠ ⊥ := by
    obtain ⟨p, hp, A, _hAea, hAK, hAnc⟩ :=
      exists_isElementaryAbelian_not_isCyclic_le_of_two_le_rank K hr
    intro hKbot
    have hA_bot : A = ⊥ := le_bot_iff.mp (hAK.trans (le_of_eq hKbot))
    haveI : Nontrivial ↥A := Nontrivial.of_not_isCyclic hAnc
    exact ((Subgroup.nontrivial_iff_ne_bot A).mp inferInstance) hA_bot
  rw [lt_top_iff_ne_top]
  intro hCtop
  have hKleZ : K ≤ Subgroup.center G :=
    Subgroup.centralizer_eq_top_iff_subset.mp hCtop
  have hKbot : K = ⊥ := by
    exact le_bot_iff.mp (hKleZ.trans (le_of_eq hZbot))
  exact hKne hKbot

/-- Proper form of BG Theorem 9.6 for the branch `r(K) ≥ 3`. -/
private theorem isUniquelyMaximal_of_three_le_rank_of_lt_top [Finite G]
    (hG : IsMinimalSimpleOdd G) {K : Subgroup G} (hKlt : K < ⊤)
    (hr3 : 3 ≤ rank ↥K) :
    IsUniquelyMaximal K := by
  classical
  obtain ⟨p, hp, hpRankK⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := ↥K) (n := 3) (by norm_num) hr3
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B₀, hB₀ea, hB₀log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥K) (p := p) (n := 3) (by norm_num) hpRankK
  let B : Subgroup G := B₀.map K.subtype
  have hBea : B.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.map K.subtype_injective hB₀ea
  have hBK : B ≤ K := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hBlog : 3 ≤ Nat.log p (Nat.card B) := by
    rw [show B = B₀.map K.subtype from rfl,
      Subgroup.card_map_of_injective K.subtype_injective]
    exact hB₀log
  have hBnc : ¬ IsCyclic ↥B :=
    not_isCyclic_of_isElementaryAbelian_of_two_le_log_card hBea (by omega)
  have hBp : IsPGroup p B := hBea.isPGroup
  have hp_dvd_B : p ∣ Nat.card B := by
    obtain ⟨n, hn⟩ := hBp.exists_card_eq
    have hnpos : 0 < n := by
      by_contra hn0
      have hn_zero : n = 0 := by omega
      rw [hn_zero, pow_zero] at hn
      rw [hn] at hBlog
      norm_num at hBlog
    rw [hn]
    exact dvd_pow_self p hnpos.ne'
  have hp_odd : Odd p :=
    hG.odd.of_dvd_nat (hp_dvd_B.trans (Subgroup.card_subgroup_dvd_card B))
  obtain ⟨P, hBP⟩ := hBp.exists_le_sylow
  have h3P : 3 ≤ pRank ↥(P : Subgroup G) p := by
    let Bsub : Subgroup ↥(P : Subgroup G) := B.subgroupOf (P : Subgroup G)
    have hBsub_ea : Bsub.IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBP).symm hBea
    have hBsub_log : 3 ≤ Nat.log p (Nat.card Bsub) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv]
      exact hBlog
    exact hBsub_log.trans (le_pRank Bsub hBsub_ea)
  obtain ⟨A₀, hA₀scn⟩ :=
    OddOrder.BG.Ch1.S05.scn3_nonempty_of_three_le_pRank
      (R := ↥(P : Subgroup G)) hp_odd P.isPGroup' h3P
  let A : Subgroup G := A₀.map (P : Subgroup G).subtype
  have hAglobal : A ∈ S07.scn3Global p G := by
    change A₀.map (P : Subgroup G).subtype ∈ S07.scn3Global p G
    exact scn3Global_of_scn3_sylow P hA₀scn
  have hAU : IsUniquelyMaximal A :=
    scn3_isUniquelyMaximal hG hAglobal
  have hAab : IsMulCommutative A := by
    haveI : IsMulCommutative A₀ := hA₀scn.isSCN.isMulCommutative
    change IsMulCommutative (A₀.map (P : Subgroup G).subtype)
    infer_instance
  have hAp : IsPGroup p A := by
    change IsPGroup p (A₀.map (P : Subgroup G).subtype)
    exact (P.isPGroup'.to_subgroup A₀).map (P : Subgroup G).subtype
  have hmA : 3 ≤ rank ↥A := by
    have h3pRankA : 3 ≤ pRank ↥A p := by
      have hmono :
          pRank A₀ p ≤ pRank ↥(A₀.map (P : Subgroup G).subtype) p :=
        pRank_le_of_injective
          (f := (Subgroup.equivMapOfInjective A₀ (P : Subgroup G).subtype
            (P : Subgroup G).subtype_injective).toMonoidHom)
          (Subgroup.equivMapOfInjective A₀ (P : Subgroup G).subtype
            (P : Subgroup G).subtype_injective).injective
      exact hA₀scn.le_pRank.trans hmono
    exact h3pRankA.trans (pRank_le_rank (G := ↥A) p)
  have hB_le_CB : B ≤ Subgroup.centralizer (B : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (congrArg Subtype.val (hBea.comm ⟨b, hb⟩ ⟨c, hc⟩)).symm
  have hrB : 3 ≤ pRank ↥(Subgroup.centralizer (B : Set G)) p := by
    let Bsub : Subgroup ↥(Subgroup.centralizer (B : Set G)) :=
      B.subgroupOf (Subgroup.centralizer (B : Set G))
    have hBsub_ea : Bsub.IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hB_le_CB).symm hBea
    have hBsub_log : 3 ≤ Nat.log p (Nat.card Bsub) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_CB).toEquiv]
      exact hBlog
    exact hBsub_log.trans (le_pRank Bsub hBsub_ea)
  have hBU : IsUniquelyMaximal B :=
    isUniquelyMaximal_of_abelian_rank_three hG hAab hAp hBp hBnc hAU hmA hrB
  exact hBU.of_le_of_lt_top hBK hKlt

/-- **BG Theorem 9.6 (The Uniqueness Theorem)** (mmd L2627): `K < G`, `r(K) ≥ 2`、
`r(K) ≥ 3` または `r(C_G(K)) ≥ 3` ⇒ `K ∈ 𝒰`。線形チェーン 9.1→9.5 の終結。

Proof gate: mmd L2629 applies BG Lem 5.1 to obtain an `SCN₃(P)` subgroup inside a
Sylow `p`-subgroup containing an elementary abelian subgroup of rank 3. This is the
direct §5 dependency for §9 and should not be replaced by Peterfalvi-style type
classification hypotheses. Lean carries `K < ⊤` explicitly because `K ∈ 𝒰` includes
properness by definition. -/
theorem uniquenessTheorem [Finite G] (hG : IsMinimalSimpleOdd G)
    {K : Subgroup G} (hKlt : K < ⊤) (hr2 : 2 ≤ rank ↥K)
    (hr3 : 3 ≤ rank ↥K ∨ 3 ≤ rank ↥(Subgroup.centralizer (K : Set G))) :
    IsUniquelyMaximal K := by
  rcases hr3 with h3K | h3C
  · exact isUniquelyMaximal_of_three_le_rank_of_lt_top hG hKlt h3K
  · let C : Subgroup G := Subgroup.centralizer (K : Set G)
    have hClt : C < ⊤ := centralizer_lt_top_of_two_le_rank hG hr2
    have hCU : IsUniquelyMaximal C :=
      isUniquelyMaximal_of_three_le_rank_of_lt_top hG hClt h3C
    have hKleCC : K ≤ Subgroup.centralizer (C : Set G) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (Subgroup.mem_centralizer_iff.mp hc k hk).symm
    exact isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hCU hKleCC hr2

/-- If an elementary abelian subgroup of order `p^2` is not maximal among elementary abelian
`p`-subgroups, then its centralizer has rank at least three. This is the rank bridge behind
BG Theorem 9.6's "in particular" clause. -/
private theorem three_le_rank_centralizer_of_mem_e2_not_maximal [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA2 : A ∈ elemAbelianOfRank G p 2)
    (hAns : ¬ IsMaximalElementaryAbelian p A) :
    3 ≤ rank ↥(Subgroup.centralizer (A : Set G)) := by
  classical
  have hAea : A.IsElementaryAbelian p := hA2.1
  have hAcard : Nat.card A = p ^ 2 := hA2.2
  have hnot_max :
      ¬ ∀ F : Subgroup G, F.IsElementaryAbelian p → A ≤ F → F = A := by
    intro hmax
    exact hAns ⟨hAea, hmax⟩
  push Not at hnot_max
  obtain ⟨F, hFea, hAF, hFne⟩ := hnot_max
  have hAlt : A < F := lt_of_le_of_ne hAF (fun h => hFne h.symm)
  have hAcard_lt_Fcard : Nat.card A < Nat.card F :=
    Set.Finite.card_lt_card (Set.toFinite (F : Set G)) (hAlt : (A : Set G) ⊂ (F : Set G))
  have hp2_lt_Fcard : p ^ 2 < Nat.card F := by
    simpa [hAcard] using hAcard_lt_Fcard
  obtain ⟨k, hFcard_pow⟩ := IsPGroup.iff_card.mp hFea.isPGroup
  have htwo_lt_k : 2 < k := by
    have hpow_lt : p ^ 2 < p ^ k := by
      simpa [hFcard_pow] using hp2_lt_Fcard
    exact (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mp hpow_lt
  have hp3_le_Fcard : p ^ 3 ≤ Nat.card F := by
    rw [hFcard_pow]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  have hFC : F ≤ C := by
    intro f hf
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (hFea.comm ⟨a, hAF ha⟩ ⟨f, hf⟩)
  let Fsub : Subgroup C := F.subgroupOf C
  have hFsub_elem : Fsub.IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFC).symm hFea
  have hFsub_card : Nat.card Fsub = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv
  have hlog_ge : 3 ≤ Nat.log p (Nat.card Fsub) := by
    rw [hFsub_card]
    exact Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt hp3_le_Fcard
  have h3pRank : 3 ≤ pRank C p := hlog_ge.trans (le_pRank Fsub hFsub_elem)
  exact h3pRank.trans (pRank_le_rank (G := ↥C) p)

/-- **BG Theorem 9.6 系** (mmd L2627 "In particular"): `A ∈ ℰ²(G) − ℰ*(G)` (位数 `p²` の
elem-ab で極大でない) なら `A ∈ 𝒰`。 -/
theorem isUniquelyMaximal_of_mem_e2_not_maximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA2 : A ∈ elemAbelianOfRank G p 2)
    (hAns : ¬ IsMaximalElementaryAbelian p A) :
    IsUniquelyMaximal A := by
  have hAea : A.IsElementaryAbelian p := hA2.1
  have h2pRank : 2 ≤ pRank ↥A p := by
    have hlog_le : Nat.log p (Nat.card A) ≤ pRank ↥A p := hAea.log_card_le_pRank
    have hlog : Nat.log p (Nat.card A) = 2 := by
      rw [hA2.2, Nat.log_pow (Fact.out : p.Prime).one_lt]
    exact (le_of_eq hlog.symm).trans hlog_le
  have hr2 : 2 ≤ rank ↥A := h2pRank.trans (pRank_le_rank (G := ↥A) p)
  have hAlt : A < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hAtop
    have hcomm : ∀ a b : G, a * b = b * a := by
      intro a b
      exact congrArg Subtype.val
        (hAea.comm (⟨a, hAtop ▸ Subgroup.mem_top a⟩ : A)
          (⟨b, hAtop ▸ Subgroup.mem_top b⟩ : A))
    exact hG.notSolvable (isSolvable_of_comm hcomm)
  exact uniquenessTheorem hG hAlt hr2
    (Or.inr (three_le_rank_centralizer_of_mem_e2_not_maximal hA2 hAns))

end OddOrder.BG.Ch2.S09
