/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.Ch1_Preliminary.PLength
import OddOrder.BG.Ch1_Preliminary.S04_PGroupsSmallRank
import OddOrder.BG.Ch2_Uniqueness.S07_Transitivity
import OddOrder.BG.Ch2_Uniqueness.S08_FittingOfMaximal
import OddOrder.BG.Ch2_Uniqueness.S09_Uniqueness
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
- `Malpha/Mbeta/Msigma M` = `O_{α/β/σ(M)}(M)` (`opiCoreInG`);
  `Fsigma/Fsigma' M` = `O_{σ(M)/σ'}(F(M))`。
- `r_p` = `pRank ↥· p`; `r` = `rank ↥·`; `M'` = `derivedInG M`;
  `F(M)` = `Ch2.S08.fittingInG M`。
- 固定 G は `(hG : IsMinimalSimpleOdd G)` を明示 thread。

## 現在の scaffold 範囲

定義層 (idealPrime/α/β/σ/M_α/M_β/M_σ/F_σ/F_σ') と、BG 10.1--10.14
の statement skeleton を配置済み。Lemma 10.13 は `Ω₁(Z(P))` と `ℰ¹(A)` の ambient subgroup
encoding を本ファイル内に置く。proof は別フェーズで、既存の `sorry` はこの節の interface
を後続 §11--§16 に先に渡すためのもの。

## Lane C proof-gate notes

- `idealPrime` は BG §10 の literal 定義を保つ (mmd L2643)。Theorem 5.3 との narrow
  equivalence (mmd L1838/L2643) は proof gate であり、追加仮定や structure field にはしない。
- Lemma 10.13 は mmd の missing page (PDF p.79) から statement を回収済み。`Z₀=Ω₁(Z(P))`
  は `omega1CenterInG P p` として ambient `G` の subgroup に map し、`X∈ℰ¹(A)` は
  `elemAbelianOfRankIn p 1 A X` で表す。
- Corollary 10.7(b) は Corollary 10.7(a) と BG Theorem 4.16 に依存する
  (mmd L2799; Theorem 4.16 statement L1636)。rank-two Sylow 構造はここで proving する。
- Lemma 10.8(c) は Theorem 10.6 の p-length one と BG Theorem 5.6 を使う
  (mmd L2817; Theorem 5.6 statement L1945)。`p ∉ beta M` から narrow 側へ降りる gate。
- Proposition 10.10(a) uses §7 Proposition 7.5/Theorems 7.3--7.4 (mmd L2852),
  (b) uses Corollary 10.7 plus Lemma 6.5, and (c) uses BG Theorem 5.5(a) (mmd L2854).
  These are exact upstream interfaces, not hypotheses to hide in the downstream §12--§16 spine.

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
noncomputable def Malpha (M : Subgroup G) : Subgroup G := opiCoreInG (alpha M) M

/-- **BG `M_β = O_{β(M)}(M)`**。 -/
noncomputable def Mbeta (M : Subgroup G) : Subgroup G := opiCoreInG (beta M) M

/-- **BG `M_σ = O_{σ(M)}(M)`**。 -/
noncomputable def Msigma (M : Subgroup G) : Subgroup G := opiCoreInG (sigma M) M

/-- **BG `F_σ(M) = O_{σ(M)}(F(M))`**。 -/
noncomputable def Fsigma (M : Subgroup G) : Subgroup G :=
  opiCoreInG (sigma M) (Ch2.S08.fittingInG M)

/-- **BG `F_{σ'}(M) = O_{σ(M)'}(F(M))`**。 -/
noncomputable def Fsigma' (M : Subgroup G) : Subgroup G :=
  opiCoreInG (sigma M)ᶜ (Ch2.S08.fittingInG M)

/-! ## Lemma 10.13 用の局所記法 -/

/-- `X ∈ ℰ_p^n(H)` encoded in the ambient group `G`: `X` is elementary abelian of
rank `n` in `G` and lies in `H`. BG Lemma 10.13 uses this mainly as `X ∈ ℰ¹(A)`. -/
def elemAbelianOfRankIn (p n : ℕ) (H X : Subgroup G) : Prop :=
  X ∈ elemAbelianOfRank G p n ∧ X ≤ H

/-- `Ω₁(Z(P))` for a subgroup `P ≤ G`, mapped back to the ambient group `G`.

The center of `P` is abelian, so this uses the set-form `omega1OfAbelian` rather than the
generated subgroup `Omega`. This is the `Z₀` notation in BG Lemma 10.13. -/
def omega1CenterInG (P : Subgroup G) (p : ℕ) : Subgroup G :=
  (omega1OfAbelian ↥P (Subgroup.center ↥P) p
    (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm)).map P.subtype

/-! ### Basic API for the §10 definitions -/

@[simp] theorem mem_idealPrime_iff (p : ℕ) (G : Type*) [Group G] :
    idealPrime p G ↔
      3 ≤ pRank G p ∧
        ∀ P : Sylow p G, ¬ ∃ A : Subgroup ↥(P : Subgroup G),
          Nat.card ↥A = p ^ 2 ∧ IsMaximalElementaryAbelian p A :=
  Iff.rfl

@[simp] theorem mem_alpha_iff (M : Subgroup G) (p : ℕ) :
    p ∈ alpha M ↔ p ∈ (Nat.card ↥M).primeFactors ∧ 3 ≤ pRank ↥M p :=
  Iff.rfl

@[simp] theorem mem_beta_iff (M : Subgroup G) (p : ℕ) :
    p ∈ beta M ↔ p ∈ alpha M ∧ idealPrime p G :=
  Iff.rfl

@[simp] theorem mem_sigma_iff (M : Subgroup G) (p : ℕ) :
    p ∈ sigma M ↔
      p ∈ (Nat.card ↥M).primeFactors ∧
        ∃ P : Sylow p ↥M, Subgroup.normalizer ((P : Subgroup ↥M).map M.subtype) ≤ M :=
  Iff.rfl

theorem alpha_subset_primeFactors (M : Subgroup G) :
    alpha M ⊆ (Nat.card ↥M).primeFactors :=
  fun _ hp => hp.1

theorem beta_subset_alpha (M : Subgroup G) :
    beta M ⊆ alpha M :=
  fun _ hp => hp.1

theorem beta_subset_primeFactors (M : Subgroup G) :
    beta M ⊆ (Nat.card ↥M).primeFactors :=
  (beta_subset_alpha M).trans (alpha_subset_primeFactors M)

theorem Malpha_le (M : Subgroup G) : Malpha M ≤ M :=
  Subgroup.map_subtype_le _

theorem Mbeta_le (M : Subgroup G) : Mbeta M ≤ M :=
  Subgroup.map_subtype_le _

theorem Msigma_le (M : Subgroup G) : Msigma M ≤ M :=
  Subgroup.map_subtype_le _

theorem Fsigma_le_fitting (M : Subgroup G) : Fsigma M ≤ Ch2.S08.fittingInG M :=
  Subgroup.map_subtype_le _

theorem Fsigma'_le_fitting (M : Subgroup G) : Fsigma' M ≤ Ch2.S08.fittingInG M :=
  Subgroup.map_subtype_le _

@[simp] theorem Malpha_subgroupOf (M : Subgroup G) :
    (Malpha M).subgroupOf M = Ch03.oPiCore (alpha M) ↥M := by
  rw [Subgroup.subgroupOf, Malpha, OddOrder.GroupTheory.opiCoreInG,
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

@[simp] theorem Mbeta_subgroupOf (M : Subgroup G) :
    (Mbeta M).subgroupOf M = Ch03.oPiCore (beta M) ↥M := by
  rw [Subgroup.subgroupOf, Mbeta, OddOrder.GroupTheory.opiCoreInG,
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

@[simp] theorem Msigma_subgroupOf (M : Subgroup G) :
    (Msigma M).subgroupOf M = Ch03.oPiCore (sigma M) ↥M := by
  rw [Subgroup.subgroupOf, Msigma, OddOrder.GroupTheory.opiCoreInG,
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

theorem Malpha_isPiGroup [Finite G] (M : Subgroup G) :
    Ch03.Subgroup.IsPiGroup (alpha M) (Malpha M) := by
  intro r hr
  have hcard : Nat.card ↥(Malpha M) = Nat.card ↥(Ch03.oPiCore (alpha M) ↥M) := by
    rw [Malpha, OddOrder.GroupTheory.opiCoreInG,
      Subgroup.card_map_of_injective M.subtype_injective]
  rw [hcard] at hr
  exact Ch03.oPiCore.isPiGroup (alpha M) r hr

theorem Mbeta_isPiGroup [Finite G] (M : Subgroup G) :
    Ch03.Subgroup.IsPiGroup (beta M) (Mbeta M) := by
  intro r hr
  have hcard : Nat.card ↥(Mbeta M) = Nat.card ↥(Ch03.oPiCore (beta M) ↥M) := by
    rw [Mbeta, OddOrder.GroupTheory.opiCoreInG,
      Subgroup.card_map_of_injective M.subtype_injective]
  rw [hcard] at hr
  exact Ch03.oPiCore.isPiGroup (beta M) r hr

theorem Msigma_isPiGroup [Finite G] (M : Subgroup G) :
    Ch03.Subgroup.IsPiGroup (sigma M) (Msigma M) := by
  intro r hr
  have hcard : Nat.card ↥(Msigma M) = Nat.card ↥(Ch03.oPiCore (sigma M) ↥M) := by
    rw [Msigma, OddOrder.GroupTheory.opiCoreInG,
      Subgroup.card_map_of_injective M.subtype_injective]
  rw [hcard] at hr
  exact Ch03.oPiCore.isPiGroup (sigma M) r hr

@[simp] theorem mem_elemAbelianOfRankIn_iff (p n : ℕ) (H X : Subgroup G) :
    elemAbelianOfRankIn p n H X ↔ X ∈ elemAbelianOfRank G p n ∧ X ≤ H :=
  Iff.rfl

theorem elemAbelianOfRankIn.le {p n : ℕ} {H X : Subgroup G}
    (hX : elemAbelianOfRankIn p n H X) : X ≤ H :=
  hX.2

theorem elemAbelianOfRankIn.mem_elemAbelianOfRank {p n : ℕ} {H X : Subgroup G}
    (hX : elemAbelianOfRankIn p n H X) : X ∈ elemAbelianOfRank G p n :=
  hX.1

theorem omega1CenterInG_le (P : Subgroup G) (p : ℕ) :
    omega1CenterInG P p ≤ P :=
  Subgroup.map_subtype_le _

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

/-! ## Theorem 10.2 — M_σ/M_α の Hall 構造 (mmd L2713) -/

/-- **BG Theorem 10.2** (mmd L2713): `M ∈ ℳ` のとき `M_σ`, `M_α` は `M` および `G` の Hall 部分群で、
`M_α ⊆ M_σ ⊆ M'`、`M_σ ≠ 1`。(原典はさらに `r(M/M_α) ≤ 2` と `M'/M_α` nilpotent を含む —
quotient 型の `Normal` instance 整備後に追加予定。) -/
theorem isHall_Msigma_Malpha [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Ch03.IsHallSubgroup (sigma M) (Msigma M) ∧
    Ch03.IsHallSubgroup (alpha M) (Malpha M) ∧
    Malpha M ≤ Msigma M ∧ Msigma M ≤ derivedInG M ∧
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
        (P : Subgroup G) ≤ derivedInG (Subgroup.normalizer ((P : Subgroup G) : Set G))) ∧
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
    (∃ W : Subgroup G, W ≤ derivedInG M ∧
      Ch03.IsHallSubgroup (beta M)ᶜ (W.subgroupOf (derivedInG M)) ∧
      Group.IsNilpotent ↥W) ∧
    (∃ W : Subgroup G, W ≤ Msigma M ∧
      Ch03.IsHallSubgroup (beta M)ᶜ (W.subgroupOf (Msigma M)) ∧ Group.IsNilpotent ↥W) ∧
    (∀ p : ℕ, p.Prime → p ∈ (Nat.card ↥M).primeFactors → p ∉ beta M →
      Ch05.HasNormalPComplement p ↥(derivedInG M) ∧
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
(原典 (d) は `sigma_complement_commutator_cyclic_normal` として別 theorem に露出。) -/
theorem sigma_complement_rank_le_one [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {K : Subgroup G} (hKM : K ≤ M)
    (hKpi : Subgroup.IsPiSubgroup (sigma M)ᶜ K) :
    ¬ IsUniquelyMaximal K ∧
    rank ↥(Subgroup.centralizer (Msigma M : Set G) ⊓ K) ≤ 1 ∧
    (IsCyclic ↥(Subgroup.centralizer (Msigma M : Set G) ⊓ K ⊓ derivedInG M) ∧
      M ≤ Subgroup.normalizer
        ((Subgroup.centralizer (Msigma M : Set G) ⊓ K ⊓ derivedInG M : Subgroup G) :
          Set G)) := by
  sorry

/-! ## Proposition 10.11(d) — commutators with `σ(M)'`-subgroups (mmd L2856) -/

/-- **BG Proposition 10.11(d)** (mmd L2856): `M ∈ ℳ`, `K` を `M` の `σ(M)'`-部分群とする。
`p ∈ σ(M)'`, `P ∈ ℰ_p¹(N_M(K))`, `C_{M_σ}(P)=1`, かつ `K` が abelian `p'`-group なら、
`[K,P]` は `M_σ` を中心化し、cyclic normal subgroup of `M` である。

This is exposed separately because later §12/§13 arguments need the commutator conclusion,
while Proposition 10.11(a)(b)(c) provides only the rank and cyclic-normal centralizer gate. -/
theorem sigma_complement_commutator_cyclic_normal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {K : Subgroup G} (hKM : K ≤ M)
    (hKpi : Subgroup.IsPiSubgroup (sigma M)ᶜ K) {p : ℕ} [Fact p.Prime]
    (hp : p ∉ sigma M) {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1)
    (hPN : P ≤ Subgroup.normalizer (K : Set G) ⊓ M)
    (hCP : Msigma M ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hKab : IsMulCommutative ↥K) (hKp' : Subgroup.IsPiSubgroup (({p} : Set ℕ)ᶜ) K) :
    ⁅K, P⁆ ≤ Subgroup.centralizer ((Msigma M : Subgroup G) : Set G) ∧
    IsCyclic ↥(⁅K, P⁆ : Subgroup G) ∧
    M ≤ Subgroup.normalizer ((⁅K, P⁆ : Subgroup G) : Set G) := by
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

/-! ## Proposition 10.14 — β(G)-prime の global 構造 (mmd L2894) -/

/-- **Cyclic uniqueness by order**: in a finite cyclic group, two subgroups of equal
cardinality coincide. (Each order-`d` subgroup equals the unique order-`d` kernel
`(powMonoidHom d).ker`; this is the order-`d` generalisation of the order-`p` argument in
`OddOrder.BG.Ch1_Preliminary.S04`.) Used in Prop 10.14(c): a subgroup of the cyclic `N_P(X)`
is characteristic. -/
private theorem cyclic_subgroup_eq_of_card_eq {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {K L : Subgroup C} (h : Nat.card K = Nat.card L) : K = L := by
  letI : CommGroup C := IsCyclic.commGroup
  -- Each order-`d` subgroup `M` equals the unique order-`d` kernel `(powMonoidHom d).ker`.
  have key : ∀ {M : Subgroup C} {d : ℕ}, Nat.card M = d → M = (powMonoidHom d : C →* C).ker := by
    intro M d hM
    have hM_le : M ≤ (powMonoidHom d : C →* C).ker := by
      intro g hg
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have hg1 : (⟨g, hg⟩ : M) ^ Nat.card M = 1 := pow_card_eq_one'
      have := congrArg (Subtype.val) hg1
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one, hM] at this
    have hd_dvd : d ∣ Nat.card C := hM ▸ M.card_subgroup_dvd_card
    have hker_card : Nat.card (powMonoidHom d : C →* C).ker = d := by
      rw [IsCyclic.card_powMonoidHom_ker (G := C) d, Nat.gcd_eq_right hd_dvd]
    exact Subgroup.eq_of_le_of_card_ge hM_le (by rw [hker_card, hM])
  exact (key (d := Nat.card K) rfl).trans (key (d := Nat.card K) h.symm).symm

/-- **Monotonicity of `𝒰` under inclusion within a proper subgroup** (the fiddly lemma of
Prop 10.14(b)): if `A ∈ 𝒰`, `A ≤ R`, and `R` is proper, then `R ∈ 𝒰`. The unique maximal
`M ⊇ A` is the unique maximal `⊇ R`: any coatom `⊇ R` also `⊇ A`, hence equals it; and `R`
proper lies in some coatom (`IsCoatomic`). -/
private theorem isUniquelyMaximal_of_le [Finite G] {A R : Subgroup G}
    (hA : IsUniquelyMaximal A) (hAR : A ≤ R) (hR : R < ⊤) : IsUniquelyMaximal R := by
  obtain ⟨_, M, ⟨hMc, _⟩, hMu⟩ := hA
  refine ⟨hR, M, ?_, ?_⟩
  · -- `M` is a coatom containing `R`: it contains some coatom `⊇ R`, which `⊇ A`, hence `= M`.
    obtain ⟨N, hNc, hRN⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom R).resolve_left hR.ne
    have hNeqM : N = M := hMu N ⟨hNc, hAR.trans hRN⟩
    exact ⟨hNeqM ▸ hNc, hNeqM ▸ hRN⟩
  · -- Uniqueness: any coatom `⊇ R` also `⊇ A`, so equals `M`.
    intro N hN
    exact hMu N ⟨hN.1, hAR.trans hN.2⟩

/-- A finite cyclic group has `rank ≤ 1`: any elementary abelian `q`-subgroup `A` is cyclic
(subgroup of cyclic), so its exponent equals its order and divides `q`, whence `|A| ≤ q` and
`log_q |A| ≤ 1`. Contrapositive used in Prop 10.14(b): `2 ≤ rank ↥R ⇒ R` noncyclic. -/
private theorem rank_le_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] :
    rank C ≤ 1 := by
  rw [rank_le_iff]
  intro q
  rw [pRank_le_iff]
  intro A hA
  -- `A` is cyclic, elementary abelian `q`, so `|A| = exponent A ∣ q`, hence `|A| ≤ q`.
  haveI : IsCyclic ↥A := Subgroup.isCyclic A
  have hexp : Monoid.exponent ↥A ∣ q :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => hA.pow_eq_one g)
  rw [IsCyclic.exponent_eq_card (α := ↥A)] at hexp
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · -- `q = 0`: `|A| ∣ 0` is no info, but `Nat.log 0 _ = 0`.
    subst hq0; rw [Nat.log_zero_left]; exact Nat.zero_le _
  · have hcard_le : Nat.card ↥A ≤ q := Nat.le_of_dvd hqpos hexp
    calc Nat.log q (Nat.card ↥A) ≤ Nat.log q q := Nat.log_mono_right hcard_le
      _ ≤ 1 := by
        rcases Nat.lt_or_ge q 2 with hq1 | hq2
        · -- `0 < q < 2` forces `q = 1`, where `Nat.log 1 1 = 0`.
          interval_cases q
          simp
        · rw [Nat.log_eq_one_iff'.mpr ⟨le_refl q, by nlinarith⟩]

/-- The `p`-rank is realised inside any Sylow `p`-subgroup: `pRank G p ≤ pRank ↥P p`.
Every elementary abelian `p`-subgroup `A ≤ G` is conjugate into `P` (Sylow conjugacy),
and conjugation preserves elementary-abelianness and order. Used in Prop 10.14(c) to get
`3 ≤ pRank G p ≤ rank ↥P` from `idealPrime`. -/
private theorem pRank_le_pRank_sylow [Finite G] [Fact p.Prime] (P : Sylow p G) :
    pRank G p ≤ pRank ↥(P : Subgroup G) p := by
  rw [pRank_le_iff]
  intro A hA
  -- `A` is a `p`-group, so `A ≤ Q'` for some Sylow `Q'`, and `Q'` is conjugate to `P`.
  obtain ⟨Q', hAQ'⟩ := hA.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q' P
  have hgcoe : MulAut.conj g • (Q' : Subgroup G) = (P : Subgroup G) := by
    rw [← Sylow.coe_subgroup_smul]
    exact congrArg (fun S : Sylow p G => (S : Subgroup G)) hg
  -- `A' := conj g • A ≤ conj g • Q' = P`, elementary abelian of order `|A|`.
  set A' : Subgroup G := A.map (MulAut.conj g).toMonoidHom with hA'_def
  have hA'_le : A' ≤ (P : Subgroup G) := by
    rw [hA'_def]
    rintro y ⟨x, hx, rfl⟩
    rw [← hgcoe]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) Q' (hAQ' hx)
  have hA'_elem : A'.IsElementaryAbelian p :=
    hA.map (MulAut.conj g).injective
  have hA'_card : Nat.card ↥A' = Nat.card ↥A := by
    rw [hA'_def, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  -- Transfer `A'` into `↥P` and bound its `log_p`-rank.
  have hA'P_elem : (A'.subgroupOf (P : Subgroup G)).IsElementaryAbelian p := by
    apply Subgroup.IsElementaryAbelian.of_map (f := (P : Subgroup G).subtype)
      (P : Subgroup G).subtype_injective
    rwa [Subgroup.map_subgroupOf_eq_of_le hA'_le]
  have hA'P_card : Nat.card ↥(A'.subgroupOf (P : Subgroup G)) = Nat.card ↥A := by
    rw [← hA'_card, ← Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hA'_le]
  calc Nat.log p (Nat.card ↥A) = Nat.log p (Nat.card ↥(A'.subgroupOf (P : Subgroup G))) := by
        rw [hA'P_card]
    _ ≤ pRank ↥(P : Subgroup G) p := le_pRank _ hA'P_elem

/-- **BG Proposition 10.14 (a)(b)(c)** (mmd L2894): `p` ideal (`p ∈ β(G)`), `P ∈ Syl_p(G)`。
(a) `ℰ_p²(G) ∩ ℰ_p*(G) = ∅`; (b) `p`-部分群 `R` で `r(R) ≥ 2` なら `R ∈ 𝒰`;
(c) 任意の `X ≤ P` で `N_P(X) ∈ 𝒰`。(原典 (d) は
`normalizer_le_of_nontrivial_beta_subgroup` として別 theorem に露出。)

Proof: (a) `A ∈ ℰ²(G) ∩ ℰ*(G)` ⇒ `A ≤ Q` for some Sylow `Q` (`exists_le_sylow`), `A.subgroupOf Q`
maximal-elem-ab of order `p²` in `↥Q`, contradicting `idealPrime`. (b) `2 ≤ rank ↥R` ⇒ `R`
noncyclic ⇒ `A ∈ ℰ²(R)` (S04), not maximal by (a), so `A ∈ 𝒰` by §9's
`isUniquelyMaximal_of_mem_e2_not_maximal` (Uniqueness Theorem — cited), lifted to `R` by
`isUniquelyMaximal_of_le`. (c) `Q = N_P(X)`: if `r(Q) ≥ 2` use (b); else `Q` cyclic, `X char Q`
(cyclic uniqueness), `N_P(Q) ⊆ N_P(X) = Q`, so `Q = P` by the nilpotent normalizer condition,
contradicting `3 ≤ pRank G p ≤ rank ↥P`. -/
theorem beta_global_structure [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (hp : idealPrime p G) (P : Sylow p G) :
    (¬ ∃ A : Subgroup G, A ∈ elemAbelianOfRank G p 2 ∧ IsMaximalElementaryAbelian p A) ∧
    (∀ R : Subgroup G, IsPGroup p ↥R → 2 ≤ rank ↥R → IsUniquelyMaximal R) ∧
    (∀ X : Subgroup G, X ≤ (P : Subgroup G) →
      IsUniquelyMaximal (Subgroup.normalizer (X : Set G) ⊓ (P : Subgroup G))) := by
  obtain ⟨hpRank3, hpIdeal⟩ := hp
  have hp_prime : p.Prime := Fact.out
  -- `p ∣ |G|` (from `pRank G p ≥ 3 > 0`), hence `p` is odd.
  have hp_odd : Odd p := by
    -- `¬ pRank G p ≤ 0` gives an elem-ab `A` with `1 ≤ log_p |A|`, so `p ≤ |A|`.
    have hnle : ¬ pRank G p ≤ 0 := by omega
    rw [pRank_le_iff] at hnle
    simp only [not_forall, not_le] at hnle
    obtain ⟨A, hA_elem, hAlog⟩ := hnle
    have hp_le_A : p ≤ Nat.card ↥A := by
      have h1 : 1 ≤ Nat.log p (Nat.card ↥A) := by omega
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ Nat.card ↥A := Nat.pow_le_of_le_log Nat.card_pos.ne' h1
    have hp_dvd_A : p ∣ Nat.card ↥A := by
      obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := p)).mp hA_elem.isPGroup
      have hjpos : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · rw [hj, hj0, pow_zero] at hp_le_A
          exact absurd hp_le_A (by have := hp_prime.one_lt; omega)
        · exact hjpos
      rw [hj]; exact dvd_pow_self p (by omega : j ≠ 0)
    have hp_dvd_G : p ∣ Nat.card G := hp_dvd_A.trans A.card_subgroup_dvd_card
    exact hG.odd.of_dvd_nat hp_dvd_G
  -- ===== Part (a) =====
  have partA : ¬ ∃ A : Subgroup G,
      A ∈ elemAbelianOfRank G p 2 ∧ IsMaximalElementaryAbelian p A := by
    rintro ⟨A, hA2, hAmax⟩
    rw [mem_elemAbelianOfRank] at hA2
    obtain ⟨hA_elem, hA_card⟩ := hA2
    -- `A` is a `p`-group, land it in a Sylow `Q`.
    obtain ⟨Q, hAQ⟩ := hA_elem.isPGroup.exists_le_sylow
    -- `A.subgroupOf Q` has order `p²` and is maximal-elem-ab in `↥Q`, contradicting `idealPrime`.
    refine hpIdeal Q ⟨A.subgroupOf (Q : Subgroup G), ?_, ?_⟩
    · rw [← Subgroup.card_map_of_injective (Q : Subgroup G).subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hAQ, hA_card]
    · refine ⟨?_, ?_⟩
      · apply Subgroup.IsElementaryAbelian.of_map (f := (Q : Subgroup G).subtype)
          (Q : Subgroup G).subtype_injective
        rwa [Subgroup.map_subgroupOf_eq_of_le hAQ]
      · intro F' hF'_elem hF'_ge
        -- map `F' ≤ ↥Q` to `G`; it is elem-ab, ⊇ `A`, so `= A` by `G`-maximality.
        have hF_elem : (F'.map (Q : Subgroup G).subtype).IsElementaryAbelian p :=
          hF'_elem.map (Q : Subgroup G).subtype_injective
        have hAF : A ≤ F'.map (Q : Subgroup G).subtype := by
          calc A = (A.subgroupOf (Q : Subgroup G)).map (Q : Subgroup G).subtype :=
                (Subgroup.map_subgroupOf_eq_of_le hAQ).symm
            _ ≤ F'.map (Q : Subgroup G).subtype := Subgroup.map_mono hF'_ge
        have hFeqA : F'.map (Q : Subgroup G).subtype = A := hAmax.2 _ hF_elem hAF
        -- inject back: `F' = A.subgroupOf Q`.
        have := hFeqA.trans (Subgroup.map_subgroupOf_eq_of_le hAQ).symm
        exact Subgroup.map_injective (Q : Subgroup G).subtype_injective this
  -- ===== Part (b) =====
  have partB : ∀ R : Subgroup G, IsPGroup p ↥R → 2 ≤ rank ↥R → IsUniquelyMaximal R := by
    intro R hR_pg hR_rank
    -- `2 ≤ rank ↥R` ⇒ `R` noncyclic ⇒ `R` has `E ∈ ℰ²(↥R)` (S04).
    have hR_nc : ¬ IsCyclic ↥R := by
      intro hRc
      haveI := hRc
      have : rank ↥R ≤ 1 := rank_le_one_of_isCyclic (C := ↥R)
      omega
    obtain ⟨E, hE_elem, hE_card⟩ :=
      OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
        hR_pg hp_odd hR_nc
    -- map `E ≤ ↥R` to `A ≤ R` in `G`.
    set A : Subgroup G := E.map R.subtype with hA_def
    have hAR : A ≤ R := Subgroup.map_subtype_le E
    have hA_elem : A.IsElementaryAbelian p :=
      hE_elem.map R.subtype_injective
    have hA_card : Nat.card ↥A = p ^ 2 := by
      rw [hA_def, Subgroup.card_map_of_injective R.subtype_injective, hE_card]
    have hA2 : A ∈ elemAbelianOfRank G p 2 := by
      rw [mem_elemAbelianOfRank]; exact ⟨hA_elem, hA_card⟩
    -- By (a), `A` is not maximal-elem-ab, so `A ∈ 𝒰` (§9 Uniqueness Theorem corollary).
    have hAns : ¬ IsMaximalElementaryAbelian p A := fun hAmax => partA ⟨A, hA2, hAmax⟩
    have hAU : IsUniquelyMaximal A :=
      OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_mem_e2_not_maximal hG hA2 hAns
    -- `R` is proper (`R = ⊤` ⇒ `G` is a solvable `p`-group, contradiction), so lift `A ∈ 𝒰`.
    have hR_lt : R < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro hRtop
      have hGpg : IsPGroup p G :=
        hR_pg.of_equiv (hRtop ▸ Subgroup.topEquiv : (↥R : Type _) ≃* G)
      haveI : Group.IsNilpotent G := hGpg.isNilpotent
      exact hG.notSolvable inferInstance
    exact isUniquelyMaximal_of_le hAU hAR hR_lt
  -- ===== Part (c) =====
  refine ⟨partA, partB, ?_⟩
  intro X hXP
  set Q : Subgroup G := Subgroup.normalizer (X : Set G) ⊓ (P : Subgroup G) with hQ_def
  -- `Q ≤ P`, so `Q` is a `p`-group.
  have hQP : Q ≤ (P : Subgroup G) := inf_le_right
  have hQ_pg : IsPGroup p ↥Q :=
    P.2.of_injective (Subgroup.inclusion hQP) (Subgroup.inclusion_injective hQP)
  by_cases hrank : 2 ≤ rank ↥Q
  · exact partB Q hQ_pg hrank
  · -- `rank ↥Q ≤ 1`; derive a contradiction (`Q = P` but `rank ↥P ≥ 3`).
    exfalso
    -- `Q` is cyclic: else it has an `E_{p²}`, forcing `rank ↥Q ≥ 2`.
    have hQ_cyclic : IsCyclic ↥Q := by
      by_contra hQnc
      obtain ⟨E, hE_elem, hE_card⟩ :=
        OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
          hQ_pg hp_odd hQnc
      have : 2 ≤ pRank ↥Q p := pow_le_card_of_le_pRank E hE_elem hE_card
      have : 2 ≤ rank ↥Q := le_trans this (pRank_le_rank p)
      omega
    -- `X ≤ Q` (`X` normalizes itself and `X ≤ P`).
    have hXQ : X ≤ Q := by
      rw [hQ_def, le_inf_iff]
      exact ⟨Subgroup.le_normalizer, hXP⟩
    -- `N_G(Q) ⊓ P ≤ Q`: any `g ∈ P` normalizing `Q` normalizes the characteristic `X`.
    have hself : Subgroup.normalizer (Q : Set G) ⊓ (P : Subgroup G) ≤ Q := by
      rintro g ⟨hgN, hgP⟩
      rw [hQ_def, Subgroup.mem_inf]
      refine ⟨?_, hgP⟩
      -- `g` normalizes `Q`: `∀ n, n ∈ Q ↔ g n g⁻¹ ∈ Q`.
      have hgN' : ∀ n, n ∈ (Q : Set G) ↔ g * n * g⁻¹ ∈ (Q : Set G) :=
        Subgroup.mem_set_normalizer_iff.mp hgN
      -- `X' = gXg⁻¹` is a subgroup of `Q` of order `|X|`, so `X' = X` (cyclic uniqueness in `↥Q`).
      set X' : Subgroup G := X.map (MulAut.conj g).toMonoidHom with hX'_def
      have hX'Q : X' ≤ Q := by
        rw [hX'_def]
        rintro y ⟨x, hx, rfl⟩
        have hxQ : (x : G) ∈ (Q : Set G) := hXQ hx
        have : g * x * g⁻¹ ∈ (Q : Set G) := (hgN' x).mp hxQ
        simpa [MulAut.conj_apply] using this
      have hX'_card : Nat.card ↥X' = Nat.card ↥X := by
        rw [hX'_def, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      -- Inside `↥Q`: the two `subgroupOf`s have equal card, hence are equal.
      have hsubOf_card : Nat.card ↥(X'.subgroupOf Q) = Nat.card ↥(X.subgroupOf Q) := by
        rw [← Subgroup.card_map_of_injective Q.subtype_injective,
          Subgroup.map_subgroupOf_eq_of_le hX'Q,
          ← Subgroup.card_map_of_injective Q.subtype_injective,
          Subgroup.map_subgroupOf_eq_of_le hXQ, hX'_card]
      have hsubOf_eq : X'.subgroupOf Q = X.subgroupOf Q :=
        cyclic_subgroup_eq_of_card_eq (C := ↥Q) hsubOf_card
      -- Map back along `Q.subtype`: `X' = X`.
      have hX'eqX : X' = X := by
        have hmap : (X'.subgroupOf Q).map Q.subtype = (X.subgroupOf Q).map Q.subtype :=
          congrArg (Subgroup.map Q.subtype) hsubOf_eq
        rwa [Subgroup.map_subgroupOf_eq_of_le hX'Q,
          Subgroup.map_subgroupOf_eq_of_le hXQ] at hmap
      -- `X.map (conj g) = X` gives `g h g⁻¹ ∈ X ↔ h ∈ X`.
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have : g * h * g⁻¹ ∈ X' := by
          rw [hX'_def, Subgroup.mem_map]
          exact ⟨h, hh, by simp [MulAut.conj_apply]⟩
        rwa [hX'eqX] at this
      · intro hh
        rw [← hX'eqX, hX'_def, Subgroup.mem_map] at hh
        obtain ⟨x, hx, hxeq⟩ := hh
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxeq
        -- `g * x * g⁻¹ = g * h * g⁻¹` ⇒ `x = h`.
        have hxh : x = h := by
          have h1 : g * x = g * h := mul_right_cancel hxeq
          exact mul_left_cancel h1
        rwa [← hxh]
    -- `Q = P` by the nilpotent normalizer condition.
    have hQeqP : Q = (P : Subgroup G) := by
      by_contra hQne
      have hQlt : Q < (P : Subgroup G) := lt_of_le_of_ne hQP hQne
      haveI : Group.IsNilpotent ↥(P : Subgroup G) := P.2.isNilpotent
      have hNC : NormalizerCondition ↥(P : Subgroup G) :=
        normalizerCondition_of_isNilpotent (G := ↥(P : Subgroup G))
      have hQsub_lt : Q.subgroupOf (P : Subgroup G) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop
        rw [Subgroup.subgroupOf_eq_top] at htop
        exact hQne (le_antisymm hQP htop)
      obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt (hNC _ hQsub_lt)
      rw [← Subgroup.subgroupOf_normalizer_eq hQP, Subgroup.mem_subgroupOf] at ht_norm
      rw [Subgroup.mem_subgroupOf] at ht_not
      -- `↑t ∈ N_G(Q) ⊓ P ≤ Q`, so `↑t ∈ Q`, contradicting `t ∉ Q.subgroupOf P`.
      exact ht_not (hself ⟨ht_norm, t.2⟩)
    -- But `rank ↥P ≥ 3 > 1 ≥ rank ↥Q = rank ↥P`.
    have hPrank : 3 ≤ rank ↥(P : Subgroup G) :=
      le_trans (le_trans hpRank3 (pRank_le_pRank_sylow P)) (pRank_le_rank p)
    rw [hQeqP] at hrank
    omega

/-! ## Proposition 10.14(d) — nontrivial `β(M)`-subgroup normalizers (mmd L2894) -/

/-- **BG Proposition 10.14(d)** (mmd L2894): `M ∈ ℳ` とし、`Y` を `M` の非自明
`β(M)`-部分群とする。このとき `N_G(Y) ⊆ M`。

This is the §13-facing clause used in Lemma 13.8 and Theorem 13.10. The proof is still a
§10 proof gate: BG chooses a prime `q ∈ π(F(Y))`, reduces to `q ∈ β(M)`, applies
Proposition 10.14(c) to `O_q(Y)`, and then obtains the ambient normalizer containment.
It is intentionally exposed as a theorem, not hoisted into any downstream setup field. -/
theorem normalizer_le_of_nontrivial_beta_subgroup [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {Y : Subgroup G} (hYM : Y ≤ M)
    (hYne : Y ≠ ⊥) (hYβ : Subgroup.IsPiSubgroup (beta M) Y) :
    Subgroup.normalizer (Y : Set G) ≤ M := by
  sorry

/-! ## Corollary 10.9 — β(M)'-部分群の centralization (mmd L2826) -/

/-- **BG Corollary 10.9 (a)(1)(2)** (mmd L2826): `M ∈ ℳ`, `p, q ∈ β(M)'` distinct, `X` を `M` の
`q`-部分群で `X ⊆ M'` または `p < q` とする。(1) `X` は `M_σ` の Sylow `p`-部分群を中心化する;
(2) `p ∈ α(M)` なら `C_M(X) ∈ 𝒰`。原典 (a)(3)/(b) は
`beta_complement_normalizer_derived_contains_sylow` と
`beta_factorization_of_sylow_normalizer_in_intersection` として別 theorem に露出。 -/
theorem beta_complement_centralizes [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hpβ : p ∉ beta M) (hqβ : q ∉ beta M)
    {X : Subgroup G} (hXM : X ≤ M) (hXq : IsPGroup q ↥X)
    (hcase : X ≤ derivedInG M ∨ p < q) :
    (∃ S : Sylow p ↥(Msigma M),
      X ≤ Subgroup.centralizer
        (((S : Subgroup ↥(Msigma M)).map (Msigma M).subtype : Subgroup G) : Set G)) ∧
    (p ∈ alpha M → IsUniquelyMaximal (Subgroup.centralizer (X : Set G) ⊓ M)) := by
  sorry

/-! ## Corollary 10.9(a)(3)/(b) — β(M)'-normalizer gates (mmd L2826) -/

/-- **BG Corollary 10.9(a)(3)** (mmd L2826): in the setup of Corollary 10.9(a), if `X` is a
Sylow `q`-subgroup of `M'`, then `N_M(X)'` contains a Sylow `p`-subgroup of `M'`.

Here `X` is represented as a Sylow subgroup of `↥(M')`, mapped back to the ambient group `G`,
and `N_M(X)` is encoded as `N_G(X) ∩ M`. -/
theorem beta_complement_normalizer_derived_contains_sylow [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hpβ : p ∉ beta M) (hqβ : q ∉ beta M)
    (X : Sylow q ↥(derivedInG M)) :
    ∃ S : Sylow p ↥(derivedInG M),
      ((S : Subgroup ↥(derivedInG M)).map (derivedInG M).subtype : Subgroup G) ≤
        derivedInG
          (Subgroup.normalizer
              (((X : Subgroup ↥(derivedInG M)).map (derivedInG M).subtype : Subgroup G) :
                Set G) ⊓
            M) := by
  sorry

/-- **BG Corollary 10.9(b)** (mmd L2826): if `H ∈ ℳ - {M}` and `N_G(S) ⊆ H ∩ M` for some
Sylow subgroup `S` of `G`, then `M = (H ∩ M)M_β` and `α(M)=β(M)`.

The product is encoded as subgroup join, matching the existing convention for normal-factor
statements in §12. -/
theorem beta_factorization_of_sylow_normalizer_in_intersection [Finite G]
    (hG : IsMinimalSimpleOdd G) {M H : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hH : H ∈ maximalSubgroups G) (hHM : H ≠ M)
    {q : ℕ} [Fact q.Prime] (S : Sylow q G)
    (hN : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ H ⊓ M) :
    M = (H ⊓ M) ⊔ Mbeta M ∧ alpha M = beta M := by
  sorry

/-! ## Proposition 10.10 — N_G(P) の分解 (mmd L2844) -/

/-- **BG Proposition 10.10 (a)(b)(c)** (mmd L2844): `p ≠ q`, `A ∈ ℰ_p²(G)∩ℰ_p*(G)`,
`Q ∈ ℋ_G*(A;q)`, `q ∈ π(C_G(A))`。すると `A ⊆ P` となるある `P ∈ Syl_p(G)` で、
(a) `N_G(P) = O_{p'}(C_G(P))·(N_G(P)∩N_G(Q))`; (b) `P ⊆ N_G(Q)'`;
(c) `Q` が cyclic または `ℰ²(Q)∩ℰ*(Q) ≠ ∅` なら `P` は `Q` を中心化する。 -/
theorem normalizer_factorization [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAmax : IsMaximalElementaryAbelian p A)
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ A {q})
    (hqc : q ∈ (Nat.card ↥(Subgroup.centralizer (A : Set G))).primeFactors) :
    ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧
      (∀ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G),
        ∃ c ∈ opiCoreInG {p}ᶜ (Subgroup.centralizer ((P : Subgroup G) : Set G)),
          ∃ m ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
            Subgroup.normalizer (Q : Set G), n = c * m) ∧
      (P : Subgroup G) ≤ derivedInG (Subgroup.normalizer (Q : Set G)) ∧
      ((IsCyclic ↥Q ∨ ∃ B : Subgroup ↥Q, Nat.card ↥B = q ^ 2 ∧ IsMaximalElementaryAbelian q B) →
        (P : Subgroup G) ≤ Subgroup.centralizer (Q : Set G)) := by
  sorry

/-! ## Lemma 10.13 — `Ω₁(Z(P))` と rank-two elementary abelian subgroup (PDF p.79) -/

/-- **BG Lemma 10.13** (mmd MISSING_PAGE, PDF p.79): `p ∈ π(G)`,
`A ∈ ℰ_p²(G) ∩ ℰ_p*(G)`, and `P` is a nonabelian `p`-subgroup of `G` containing
`A`. Let `Z₀ = Ω₁(Z(P))` and let `A₀ ∈ ℰ¹(A)` with `A₀ ≠ Z₀`. Then
(a) `Z₀ ∈ ℰ¹(A)`; (b) `C_P(A) = A₀ × Z` for a cyclic subgroup `Z` containing
`Z₀`; and (c) `N_P(A)` acts transitively by conjugation on `ℰ¹(A) - {Z₀}`.

Here `Z₀` is `omega1CenterInG P p`, `C_P(A)` is
`Subgroup.centralizer (A : Set G) ⊓ P`, and the internal product in (b) is encoded by
trivial intersection plus equality with the join, following the existing `IsNarrow` convention. -/
theorem nonabelian_pSubgroup_rankTwo_elemAbelian_structure [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (hpG : p ∈ (Nat.card G).primeFactors)
    {A P A₀ : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2)
    (hAmax : IsMaximalElementaryAbelian p A) (hPp : IsPGroup p ↥P)
    (hPnonab : ¬ IsMulCommutative ↥P) (hAP : A ≤ P)
    (hA₀ : elemAbelianOfRankIn p 1 A A₀) (hA₀ne : A₀ ≠ omega1CenterInG P p) :
    elemAbelianOfRankIn p 1 A (omega1CenterInG P p) ∧
    (∃ Z : Subgroup G, Z ≤ P ∧ IsCyclic ↥Z ∧ omega1CenterInG P p ≤ Z ∧
      A₀ ⊓ Z = ⊥ ∧ Subgroup.centralizer (A : Set G) ⊓ P = A₀ ⊔ Z) ∧
    (∀ X Y : Subgroup G, elemAbelianOfRankIn p 1 A X → X ≠ omega1CenterInG P p →
      elemAbelianOfRankIn p 1 A Y → Y ≠ omega1CenterInG P p →
        ∃ n ∈ Subgroup.normalizer (A : Set G) ⊓ P, MulAut.conj n • X = Y) := by
  sorry

end OddOrder.BG.Ch3.S10
