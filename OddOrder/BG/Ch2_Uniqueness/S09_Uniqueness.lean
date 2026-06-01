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

faithful statement + `sorry`。proof は §7 (Thm 7.4/7.6) + §8 (Thm 8.1) + §6 Thm 6.2 + §5 Lem 5.1
+ §4 (Thm 4.20, Cor 4.19) + Prop 1.16 に依存 (foundation-first)。
-/

namespace OddOrder.BG.Ch2.S09

open OddOrder.GroupTheory
open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-- **BG Theorem 9.1** (mmd L2492): `p` prime, `M ∈ ℳ`, `B ∈ ℰ_p(M)` noncyclic で、
(a) 任意の `b ∈ B^#` で `C_G(b) ⊆ M`、または (b) `⟨ℋ_G(B;p')⟩ ⊆ M`、のいずれかなら `B ∈ 𝒰`。 -/
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
  sorry

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

/-- **BG Lemma 9.5** (mmd L2559): `p` prime, `A ∈ SCN₃(p)` ⇒ `A ∈ 𝒰`。 -/
theorem scn3_isUniquelyMaximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    IsUniquelyMaximal A := by
  sorry

/-- **BG Theorem 9.6 (The Uniqueness Theorem)** (mmd L2627): `K ⊆ G`, `r(K) ≥ 2`、
`r(K) ≥ 3` または `r(C_G(K)) ≥ 3` ⇒ `K ∈ 𝒰`。線形チェーン 9.1→9.5 の終結。 -/
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
