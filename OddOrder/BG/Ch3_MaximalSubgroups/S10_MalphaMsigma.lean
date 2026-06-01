/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.Ch1_Preliminary.PLength
import OddOrder.BG.Ch2_Uniqueness.S07_Transitivity
import OddOrder.BG.Ch2_Uniqueness.S08_FittingOfMaximal
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.GroupTheory.PRank
import OddOrder.GroupTheory.NarrowPGroup
import OddOrder.GroupTheory.CentralProduct
import OddOrder.GroupTheory.IsExtraspecial
import OddOrder.GroupTheory.OmegaSubgroup
import OddOrder.GroupTheory.ElementaryAbelianFamily
import OddOrder.Isaacs.Ch05_Transfer.Main

/-!
# BG §10: The Subgroups `M_α` and `M_σ`

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter III §10 (pp. 66-76), mmd `references/bg/local-analysis.mmd`
L2637-2912, **14 結果** (Thm 10.1/10.2/10.6 + Cor 10.7/10.9 + Lem 10.3/10.4/10.5/10.8/10.12/10.13
+ Prop 10.10/10.11/10.14)。

§10 は Uniqueness Theorem (§9) の内部構造への帰結。maximal subgroup `M` の **prime 集合**
`σ(M)/α(M)/β(M)` と対応する **Hall 部分群** `M_σ/M_α/M_β` を定義し (本ファイルの定義層)、`M_σ` が
`G` の Hall 部分群で `M/M_σ` の rank ≤ 2 (Thm 10.2)、`M` は全 `p` で p-length one (Thm 10.6) 等を示す。
Ch3 (§11–§13) と Ch4 全体がこの定義層に依存する。

## 定義 (BG → repo, mmd L2643-2647)

- `idealPrime p G` (p が *ideal*): `r_p(G) ≥ 3` かつ 全 Sylow `p` で `ℰ²(P)∩ℰ*(P) = ∅`。
- `alpha M` = `α(M) = {p ∈ π(M) | r_p(M) ≥ 3}`; `beta M` = `{p ∈ α(M) | p ideal}`;
  `sigma M` = `{p ∈ π(M) | ∃ Sylow_p P of M, N_G(P) ⊆ M}`。
- `Malpha/Mbeta/Msigma M` = `O_{α/β/σ(M)}(M)` (`Ch2.S07.opiCoreInG`);
  `Fsigma/Fsigma' M` = `O_{σ(M)/σ'}(F(M))`。
- `r_p` = `pRank ↥· p`; `r` = `rank ↥·`; `M'` = `Ch2.S07.derivedInG M`;
  `F(M)` = `Ch2.S08.fittingInG M`。
- 固定 G は `(hG : IsMinimalSimpleOdd G)` を明示 thread。

## このコミットの範囲

**定義層 (idealPrime/α/β/σ/M_α/M_β/M_σ/F_σ/F_σ') + Thm 10.6** を faithful に配置。残り 13 結果
(10.1/10.2/10.3/10.4/10.5/10.7–10.14; 多くが多部分・一部 PDF 回収要) は後続。proof は §9 Uniqueness
+ §7 Transitivity + §6 Lem 6.3/6.6 + §4 Thm 4.18/4.20 + Thm 3.6 に依存 (foundation-first)。
-/

namespace OddOrder.BG.Ch3.S10

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## §10 定義層 (mmd L2643-2647) -/

/-- **BG ideal prime** (mmd L2643): `p` が *ideal* とは、`r_p(G) ≥ 3` かつ 全シロー `p`-部分群 `P`
で `ℰ²(P) ∩ ℰ*(P) = ∅` (位数 `p²` の極大 elem-ab 部分群が無い) こと。Thm 5.3 により「`G` の
Sylow `p` が narrow でない」と同値だが、定義としては BG の literal 形を採る。 -/
def idealPrime (p : ℕ) (G : Type*) [Group G] : Prop :=
  3 ≤ pRank G p ∧
    ∀ P : Sylow p G, ¬ ∃ A : Subgroup ↥(P : Subgroup G),
      Nat.card ↥A = p ^ 2 ∧ IsMaximalElementaryAbelian p A

/-- **BG `α(M)`** (mmd L2647): `{p ∈ π(M) | r_p(M) ≥ 3}`。 -/
def alpha (M : Subgroup G) : Set ℕ :=
  {p | p ∈ (Nat.card ↥M).primeFactors ∧ 3 ≤ pRank ↥M p}

/-- **BG `β(M)`** (mmd L2647): `{p ∈ α(M) | p ideal}`。 -/
def beta (M : Subgroup G) : Set ℕ :=
  {p | p ∈ alpha M ∧ idealPrime p G}

/-- **BG `σ(M)`** (mmd L2647): `{p ∈ π(M) | あるシロー p-部分群 P of M で N_G(P) ⊆ M}`。 -/
def sigma (M : Subgroup G) : Set ℕ :=
  {p | p ∈ (Nat.card ↥M).primeFactors ∧
    ∃ P : Sylow p ↥M, Subgroup.normalizer ((P : Subgroup ↥M).map M.subtype) ≤ M}

/-- **BG `M_α = O_{α(M)}(M)`**。 -/
noncomputable def Malpha (M : Subgroup G) : Subgroup G := Ch2.S07.opiCoreInG (alpha M) M

/-- **BG `M_β = O_{β(M)}(M)`**。 -/
noncomputable def Mbeta (M : Subgroup G) : Subgroup G := Ch2.S07.opiCoreInG (beta M) M

/-- **BG `M_σ = O_{σ(M)}(M)`**。 -/
noncomputable def Msigma (M : Subgroup G) : Subgroup G := Ch2.S07.opiCoreInG (sigma M) M

/-- **BG `F_σ(M) = O_{σ(M)}(F(M))`**。 -/
noncomputable def Fsigma (M : Subgroup G) : Subgroup G :=
  Ch2.S07.opiCoreInG (sigma M) (Ch2.S08.fittingInG M)

/-- **BG `F_{σ'}(M) = O_{σ(M)'}(F(M))`**。 -/
noncomputable def Fsigma' (M : Subgroup G) : Subgroup G :=
  Ch2.S07.opiCoreInG (sigma M)ᶜ (Ch2.S08.fittingInG M)

/-! ## Theorem 10.6 — proper subgroup は p-length one (mmd L2779) -/

/-- **BG Theorem 10.6** (mmd L2779): `p` prime、`H` を `G` の真部分群とすると、`H` は `p`-length
one を持つ。`M ∈ ℳ(H)` を取り `M` で示す: `r_p(M) ≤ 2` は Thm 4.18、`≥ 3` は Thm 10.2 +
Lem 6.3/10.4 + Thm 3.6。 -/
theorem proper_hasPLengthOne [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) (hH : H < ⊤) :
    Ch1.hasPLengthOne p ↥H := by
  sorry

/-! ## Theorem 10.1 — σ(M)-prime の fusion control (mmd L2657) -/

/-- **BG Theorem 10.1** (mmd L2657): `M ∈ ℳ`, `p ∈ σ(M)`, `X` を `G` の非自明 `p`-部分群とする。
(a) `X, X^g ⊆ M ⇒ g = cm` (`c∈C_G(X)`, `m∈M`); (b) `C_G(X)` は `{M^g | X⊆M^g}` 上推移的;
(c) `X⊆M ⇒ N_G(X)=N_M(X)C_G(X)`; (d) `X∈Syl_p(M), X^g⊆M ⇒ g∈M`; (e) `C_G(X)⊆M, X^g⊆M ⇒ g∈M`。
共役 `X^g` は `MulAut.conj g • X`、(c) の積分解は要素形で述べる。 -/
theorem fusion_control_of_mem_sigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime] (hp : p ∈ sigma M)
    {X : Subgroup G} (hXne : X ≠ ⊥) (hXp : IsPGroup p X) :
    (X ≤ M → ∀ g : G, MulAut.conj g • X ≤ M →
      ∃ c ∈ Subgroup.centralizer (X : Set G), ∃ m ∈ M, g = c * m) ∧
    (∀ g₁ g₂ : G, X ≤ MulAut.conj g₁ • M → X ≤ MulAut.conj g₂ • M →
      ∃ c ∈ Subgroup.centralizer (X : Set G),
        MulAut.conj c • (MulAut.conj g₁ • M) = MulAut.conj g₂ • M) ∧
    (X ≤ M → ∀ n ∈ Subgroup.normalizer X,
      ∃ a ∈ Subgroup.normalizer X ⊓ M, ∃ c ∈ Subgroup.centralizer (X : Set G), n = a * c) ∧
    ((∃ P : Sylow p ↥M, X = (P : Subgroup ↥M).map M.subtype) →
      ∀ g : G, MulAut.conj g • X ≤ M → g ∈ M) ∧
    (Subgroup.centralizer (X : Set G) ≤ M → ∀ g : G, MulAut.conj g • X ≤ M → g ∈ M) := by
  sorry

/-! ## Theorem 10.2 — M_σ/M_α の Hall 構造 (mmd L2680 付近) -/

/-- **BG Theorem 10.2**: `M ∈ ℳ` のとき `M_σ`, `M_α` は `M` および `G` の Hall 部分群で、
`M_α ⊆ M_σ ⊆ M'`、`M_σ ≠ 1`。(原典はさらに `r(M/M_α) ≤ 2` と `M'/M_α` nilpotent を含む —
quotient 型の `Normal` instance 整備後に追加予定。) -/
theorem isHall_Msigma_Malpha [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Ch03.IsHallSubgroup (sigma M) (Msigma M) ∧
    Ch03.IsHallSubgroup (alpha M) (Malpha M) ∧
    Malpha M ≤ Msigma M ∧ Msigma M ≤ Ch2.S07.derivedInG M ∧
    Msigma M ≠ ⊥ := by
  sorry

/-! ## Corollary 10.7 — Sylow `p`-部分群の構造 (mmd L2787) -/

/-- **BG Corollary 10.7** (mmd L2787): `p` prime, `P ∈ Syl_p(G)`。
(a) `V` を `N_G(P)` 内の `P` の補群 (`P⊓V=1`, `P⊔V=N_G(P)`) とすると `P=[P,V]⊆N_G(P)'`;
(b) `r(P)≤2` ⇒ `P` abelian、または `P` は位数 `p³` exp `p` の nonabelian `P₁` と cyclic `P₂`
  (`Ω₁(P₂)=Z(P₁)`) の central product;
(c) `Q⊆P`, `Q^x⊆P` ⇒ `Q^x=Q^y` (`y∈N_G(P)`);
(d) 任意の `Q≤P` で `N_P(Q)` (= `N_G(Q)⊓P`) は `N_G(Q)` の Sylow `p`-部分群;
(e) `R` `p`-部分群, `Q⊆P∩R`, `Q⊴N_G(P)` (= `N_G(P)≤N_G(Q)`) ⇒ `Q⊴N_G(R)`。 -/
theorem sylow_structure [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) :
    (∀ V : Subgroup G, V ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) →
      (P : Subgroup G) ⊓ V = ⊥ →
      (P : Subgroup G) ⊔ V = Subgroup.normalizer ((P : Subgroup G) : Set G) →
      (P : Subgroup G) = ⁅(P : Subgroup G), V⁆ ∧
        (P : Subgroup G) ≤ Ch2.S07.derivedInG (Subgroup.normalizer ((P : Subgroup G) : Set G))) ∧
    (rank ↥(P : Subgroup G) ≤ 2 →
      IsMulCommutative (P : Subgroup G) ∨
      ∃ P₁ P₂ : Subgroup G, P₁ ≤ (P : Subgroup G) ∧ P₂ ≤ (P : Subgroup G) ∧
        IsExpPExtraspecial p ↥P₁ ∧ Nat.card ↥P₁ = p ^ 3 ∧ IsCyclic ↥P₂ ∧
        (Omega ↥P₂ p 1).map P₂.subtype = (Subgroup.center ↥P₁).map P₁.subtype ∧
        IsCentralProduct (P : Subgroup G) P₁ P₂) ∧
    (∀ Q : Subgroup G, Q ≤ (P : Subgroup G) → ∀ x : G, MulAut.conj x • Q ≤ (P : Subgroup G) →
      ∃ y ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), MulAut.conj x • Q = MulAut.conj y • Q) ∧
    (∀ Q : Subgroup G, Q ≤ (P : Subgroup G) →
      ∃ S : Sylow p ↥(Subgroup.normalizer (Q : Set G)),
        (S : Subgroup ↥(Subgroup.normalizer (Q : Set G))).map
            (Subgroup.normalizer (Q : Set G)).subtype =
          Subgroup.normalizer (Q : Set G) ⊓ (P : Subgroup G)) ∧
    (∀ R Q : Subgroup G, IsPGroup p ↥R → Q ≤ (P : Subgroup G) ⊓ R →
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ Subgroup.normalizer (Q : Set G) →
      Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Q : Set G)) := by
  sorry

/-! ## Lemma 10.8 — `M_β` の Hall 性 (mmd L2810) -/

/-- **BG Lemma 10.8** (mmd L2810): `M ∈ ℳ`。
(a) `M_β` は `M` および `G` の Hall 部分群;
(b) `M'` と `M_σ` は nilpotent な Hall `β(M)'`-部分群を持つ;
(c) `p ∈ π(M)−β(M)` ⇒ `M'` と `M_σ` は normal `p`-complement を持つ (`M_β` を含む)。
(原典 (c) はさらに「`p` は `|M/O_{p'}(M)|` の最大素因子」を含む — quotient 型整備後に追加予定。) -/
theorem isHall_Mbeta [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Ch03.IsHallSubgroup (beta M) (Mbeta M) ∧
    (∃ W : Subgroup G, W ≤ Ch2.S07.derivedInG M ∧
      Ch03.IsHallSubgroup (beta M)ᶜ (W.subgroupOf (Ch2.S07.derivedInG M)) ∧
      Group.IsNilpotent ↥W) ∧
    (∃ W : Subgroup G, W ≤ Msigma M ∧
      Ch03.IsHallSubgroup (beta M)ᶜ (W.subgroupOf (Msigma M)) ∧ Group.IsNilpotent ↥W) ∧
    (∀ p : ℕ, p.Prime → p ∈ (Nat.card ↥M).primeFactors → p ∉ beta M →
      Ch05.HasNormalPComplement p ↥(Ch2.S07.derivedInG M) ∧
      Ch05.HasNormalPComplement p ↥(Msigma M)) := by
  sorry

/-! ## Lemma 10.3 / 10.5 — centralizer と normalizer (mmd gap, PDF p.87 回収) -/

/-- **BG Lemma 10.3** (mmd MISSING_PAGE, PDF p.87): `M ∈ ℳ`, `X` を `M` の `α(M)'`-部分群とし
`r(C_{M_α}(X)) ≥ 2` なら `C_M(X) ∈ 𝒰`。 -/
theorem centralizer_isUniquelyMaximal_of_two_le_rank [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {X : Subgroup G} (hXM : X ≤ M)
    (hXpi : Subgroup.IsPiSubgroup (alpha M)ᶜ X)
    (hr : 2 ≤ rank ↥(Subgroup.centralizer (X : Set G) ⊓ Malpha M)) :
    IsUniquelyMaximal (Subgroup.centralizer (X : Set G) ⊓ M) := by
  sorry

/-- **BG Lemma 10.5** (mmd MISSING_PAGE, PDF p.87): `p ∈ σ(M)'`, `X ∈ ℰ_p¹(G)`,
`N_G(X) ⊆ M` なら `r_p(M) = 2`、`p` は ideal でなく、`X ⊆ A` となる `A ∈ ℰ_p²(G)` が存在する。 -/
theorem pRank_eq_two_of_normalizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime] (hp : p ∉ sigma M)
    {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1)
    (hN : Subgroup.normalizer (X : Set G) ≤ M) :
    pRank ↥M p = 2 ∧ ¬ idealPrime p G ∧ ∃ A ∈ elemAbelianOfRank G p 2, X ≤ A := by
  sorry

/-! ## Lemma 10.4 — α(M) の判定 (mmd MISSING_PAGE, PDF p.87) -/

/-- **BG Lemma 10.4 (a)(c)** (mmd MISSING_PAGE, PDF p.87): `M ∈ ℳ`。
(a) `p ∣ |M/M'|` ⇒ `p ∉ α(M)`; (c) `p ∈ α(M)`, `r_p(M) = 2` ⇒ `p` は ideal でなく、`M` の位数 `p²`
elem-ab はすべて `G` の極大 elem-ab。
(原典 (b): `p∈α(M), M_α≠1` ⇒ `∃ x∈Ω₁(Z(P))#: ℳ(C_G(x))={M} ∧ C_{M_α}(x) Z-group` —
`Ω₁(Z(P))` の入れ子 encoding は後続。`IsZGroup`/`maximalSubgroupsContaining` は整備済。) -/
theorem alpha_criterion [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    (∀ p : ℕ, p.Prime → p ∣ (commutator ↥M).index → p ∉ alpha M) ∧
    (∀ p : ℕ, p.Prime → p ∈ alpha M → pRank ↥M p = 2 →
      ¬ idealPrime p G ∧
      ∀ A : Subgroup G, A ≤ M → A ∈ elemAbelianOfRank G p 2 →
        IsMaximalElementaryAbelian p A) := by
  sorry

/-! ## Proposition 10.11 — σ(M)'-部分群の rank (mmd L2856) -/

/-- **BG Proposition 10.11 (a)(b)(c)** (mmd L2856): `M ∈ ℳ`, `K` を `M` の `σ(M)'`-部分群とする。
(a) `K ∉ 𝒰`; (b) `r(C_K(M_σ)) ≤ 1`; (c) `C_K(M_σ) ∩ M'` は cyclic で `M` に normal。
(原典 (d) は `[K,P]` の作用条件 — 後続。) -/
theorem sigma_complement_rank_le_one [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {K : Subgroup G} (hKM : K ≤ M)
    (hKpi : Subgroup.IsPiSubgroup (sigma M)ᶜ K) :
    ¬ IsUniquelyMaximal K ∧
    rank ↥(Subgroup.centralizer (Msigma M : Set G) ⊓ K) ≤ 1 ∧
    (IsCyclic ↥(Subgroup.centralizer (Msigma M : Set G) ⊓ K ⊓ Ch2.S07.derivedInG M) ∧
      M ≤ Subgroup.normalizer
        ((Subgroup.centralizer (Msigma M : Set G) ⊓ K ⊓ Ch2.S07.derivedInG M : Subgroup G) :
          Set G)) := by
  sorry

/-! ## Lemma 10.12 — 非共役 maximal の σ-disjointness (mmd L2885) -/

/-- **BG Lemma 10.12** (mmd L2885): `M, H ∈ ℳ` が `G` で非共役なら、
(a) `M_α ⊓ H_σ = 1` かつ `α(M) ∩ σ(H) = ∅`; (b) `M_σ` が nilpotent なら `M_σ ⊓ H_σ = 1` かつ
`σ(M) ∩ σ(H) = ∅`。 -/
theorem disjoint_of_not_conj [Finite G] (hG : IsMinimalSimpleOdd G)
    {M H : Subgroup G} (hM : M ∈ maximalSubgroups G) (hH : H ∈ maximalSubgroups G)
    (hnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    (Malpha M ⊓ Msigma H = ⊥ ∧ alpha M ∩ sigma H = ∅) ∧
    (Group.IsNilpotent ↥(Msigma M) →
      Msigma M ⊓ Msigma H = ⊥ ∧ sigma M ∩ sigma H = ∅) := by
  sorry

/-! ## Proposition 10.14 — β(G)-prime の global 構造 (mmd L2900 付近) -/

/-- **BG Proposition 10.14 (a)(b)(c)** (mmd L2900 付近): `p` ideal (`p ∈ β(G)`), `P ∈ Syl_p(G)`。
(a) `ℰ_p²(G) ∩ ℰ_p*(G) = ∅`; (b) `p`-部分群 `R` で `r(R) ≥ 2` なら `R ∈ 𝒰`;
(c) 任意の `X ≤ P` で `N_P(X) ∈ 𝒰`。(原典 (d): nonid `β(M)`-部分群 `Y` ⇒ `N_G(Y)⊆M` — 後続。) -/
theorem beta_global_structure [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (hp : idealPrime p G) (P : Sylow p G) :
    (¬ ∃ A : Subgroup G, A ∈ elemAbelianOfRank G p 2 ∧ IsMaximalElementaryAbelian p A) ∧
    (∀ R : Subgroup G, IsPGroup p ↥R → 2 ≤ rank ↥R → IsUniquelyMaximal R) ∧
    (∀ X : Subgroup G, X ≤ (P : Subgroup G) →
      IsUniquelyMaximal (Subgroup.normalizer (X : Set G) ⊓ (P : Subgroup G))) := by
  sorry

end OddOrder.BG.Ch3.S10
