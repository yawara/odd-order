/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.Ch2_Uniqueness.S07_Transitivity
import OddOrder.BG.Ch2_Uniqueness.S08_FittingOfMaximal
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.GroupTheory.AInvariantPiSubgroups
import OddOrder.GroupTheory.PRank
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

/-- **BG Corollary 9.3** (mmd L2545): `p` prime, `A` abelian `p`-部分群, `B` noncyclic
`p`-部分群、`A ∈ 𝒰`, `m(A) ≥ 3`, `r_p(C_G(B)) ≥ 3` ⇒ `B ∈ 𝒰`。 -/
theorem isUniquelyMaximal_of_abelian_rank_three [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A B : Subgroup G} (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    (hBp : IsPGroup p B) (hBnc : ¬ IsCyclic ↥B) (hAU : IsUniquelyMaximal A)
    (hmA : 3 ≤ rank ↥A) (hrB : 3 ≤ pRank ↥(Subgroup.centralizer (B : Set G)) p) :
    IsUniquelyMaximal B := by
  sorry

/-- **BG Lemma 9.4** (mmd L2555): `p` prime, `M ∈ ℳ`, `r_p(F(M)) ≥ 3` ⇒ `𝒰` は rank `≥ 3` の
すべての abelian `p`-群を含む。 -/
theorem abelian_rank_three_isUniquelyMaximal_of_fitting [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hr : 3 ≤ pRank ↥(S08.fittingInG M) p) :
    ∀ A : Subgroup G, IsMulCommutative A → IsPGroup p A → 3 ≤ rank ↥A → IsUniquelyMaximal A := by
  sorry

/-- **BG Lemma 9.5** (mmd L2559): `p` prime, `A ∈ SCN₃(p)` ⇒ `A ∈ 𝒰`。

Proof gate: mmd L2579 uses Thm 7.6 and Thm 7.4; L2605 uses Cor 4.19; L2615 uses
Thm 4.20. The `SCN₃(p)` input is the right interface, so no §5 narrow or Thm 4.16
assumption should be introduced here. -/
theorem scn3_isUniquelyMaximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    IsUniquelyMaximal A := by
  sorry

/-- **BG Theorem 9.6 (The Uniqueness Theorem)** (mmd L2627): `K ⊆ G`, `r(K) ≥ 2`、
`r(K) ≥ 3` または `r(C_G(K)) ≥ 3` ⇒ `K ∈ 𝒰`。線形チェーン 9.1→9.5 の終結。

Proof gate: mmd L2629 applies BG Lem 5.1 to obtain an `SCN₃(P)` subgroup inside a
Sylow `p`-subgroup containing an elementary abelian subgroup of rank 3. This is the
direct §5 dependency for §9 and should not be replaced by Peterfalvi-style type
classification hypotheses. -/
theorem uniquenessTheorem [Finite G] (hG : IsMinimalSimpleOdd G)
    {K : Subgroup G} (hr2 : 2 ≤ rank ↥K)
    (hr3 : 3 ≤ rank ↥K ∨ 3 ≤ rank ↥(Subgroup.centralizer (K : Set G))) :
    IsUniquelyMaximal K := by
  sorry

/-- **BG Theorem 9.6 系** (mmd L2627 "In particular"): `A ∈ ℰ²(G) − ℰ*(G)` (位数 `p²` の
elem-ab で極大でない) なら `A ∈ 𝒰`。 -/
theorem isUniquelyMaximal_of_mem_e2_not_maximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA2 : A ∈ elemAbelianOfRank G p 2)
    (hAns : ¬ IsMaximalElementaryAbelian p A) :
    IsUniquelyMaximal A := by
  sorry

end OddOrder.BG.Ch2.S09
