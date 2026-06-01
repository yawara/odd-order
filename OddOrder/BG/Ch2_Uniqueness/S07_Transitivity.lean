/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.Ch1_Preliminary.PLength
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.GroupTheory.AInvariantPiSubgroups
import OddOrder.GroupTheory.SCN
import OddOrder.GroupTheory.PRank
import OddOrder.Isaacs.Ch03_SplitExtensions.Main
import Mathlib.GroupTheory.IsSubnormal
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# BG §7: The Transitivity Theorem

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter II §7 (pp. 55-60), mmd `references/bg/local-analysis.mmd`
L2131-2314, **6 結果** (Lem 7.1 + Thm 7.2/7.3/7.4/7.6 + Prop 7.5).

§7 で **最小反例 G を本書全体で fix** (`IsMinimalSimpleOdd G`, `Ch2_Uniqueness/Setup`)。中核は
**Hypothesis 7.1** と、その下で `K = O_{π'}(C_G(A))` が `ℋ_G*(A;q)` 上 conjugation で推移的に作用する
ための十分条件群。終結果 **Thm 7.6 (Thompson Transitivity)** は §8–§16 で最頻出。

## 記法 (BG → repo)

- `ℳ`/`ℳ(H)`/`𝒰` = `GroupTheory.MaximalSubgroup`; `ℋ_H(A;π)`/`ℋ*` = `GroupTheory.AInvariantPiSubgroups`。
- `ℋ_G*(A;q)` (H = G) = `hInvariantStar ⊤ A {q}`。
- `π(A)` = `primesOf A`; `π'` = `(primesOf A)ᶜ`。`O_π(H)` を `G` 内に戻したもの = `opiCoreInG π H`。
- `K = O_{π'}(C_G(A))` = `kSubgroup A`。`m(Z(A))` = `rank ↥(Subgroup.center ↥A)`。
- `K が S 上推移的に conjugation 作用` = `ConjTransitiveOn K S` (`∃ k∈K, conj k • Q₁ = Q₂`)。
- `SCN₃(p)` global = `scn3Global p` (`∃ Sylow P, A ≤ P ∧ A ∈ SCN₃(P)`; SCN は ↥P 相対)。
- 固定 G は `(hG : IsMinimalSimpleOdd G)` を各定理に明示的に通す (Peterfalvi Hypothesis 流儀)。

## proof は後続

全 6 結果は faithful statement + `sorry`。proof は Prop 1.16 (coprime action generation, §1),
Lem 6.5/6.6 (§6), Thm 6.7, SCN/p-stability に依存 (foundation-first scaffold)。
-/

namespace OddOrder.BG.Ch2.S07

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## §7 記法のための helper 定義 -/

/-- `π(A)`: `|A|` の素因子集合。 -/
def primesOf (A : Subgroup G) : Set ℕ := {q | q ∈ (Nat.card ↥A).primeFactors}

/-- `O_π(H)` を `G` 内の部分群として実現したもの (= `(O_π(↥H)).map H.subtype`)。BG の
`O_{π'}(X)` / `O_{π'}(C_G(P))` を `Subgroup G` として扱うための橋。 -/
def opiCoreInG (π : Set ℕ) (H : Subgroup G) : Subgroup G :=
  (Ch03.oPiCore π ↥H).map H.subtype

/-- `K = O_{π'}(C_G(A))` (Hypothesis 7.1 の `K`)。 -/
def kSubgroup (A : Subgroup G) : Subgroup G :=
  opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (A : Set G))

/-- `H′` (`H` の derived subgroup) を `G` 内の部分群として実現したもの。Thm 7.4(d) の
`N_G(P)′ ⊆ N_G(Q)′` を述べるため。 -/
def derivedInG (H : Subgroup G) : Subgroup G :=
  (commutator ↥H).map H.subtype

/-- `K` が部分群の集合 `S` 上 conjugation で **推移的に作用**する: 任意の `Q₁,Q₂ ∈ S` に対し
ある `k ∈ K` で `Q₁^k = Q₂` (`MulAut.conj k • Q₁ = Q₂`)。 -/
def ConjTransitiveOn (K : Subgroup G) (S : Set (Subgroup G)) : Prop :=
  ∀ Q₁ ∈ S, ∀ Q₂ ∈ S, ∃ k ∈ K, MulAut.conj k • Q₁ = Q₂

/-- **`SCN₃(p)` global** (BG §7 L2137): あるシロー `p`-部分群 `P` で `A ∈ SCN₃(P)`
(↥P 内で `IsSCN₃`) となる `A ≤ G`。 -/
def scn3Global (p : ℕ) (G : Type*) [Group G] : Set (Subgroup G) :=
  {A | ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧ IsSCN₃ p (A.subgroupOf (P : Subgroup G))}

/-! ## Hypothesis 7.1 -/

/-- **BG Hypothesis 7.1** (mmd L2141): `A` についての固定設定。`π = π(A)`,
`K = O_{π'}(C_G(A))` (`kSubgroup A`) を伴い:

1. `A` は `G` の非自明な真部分群、
2. `A` を含む任意の真部分群 `X` について `⟨ℋ_X(A;π')⟩ = O_{π'}(X)`
   (`sSup (hInvariant X A π') = opiCoreInG π' X`)。 -/
structure Hypothesis71 (A : Subgroup G) : Prop where
  /-- `A ≠ 1`. -/
  ne_bot : A ≠ ⊥
  /-- `A` は `G` の真部分群。 -/
  proper : A < ⊤
  /-- (2): `A ⊆ X < G` なら `⟨ℋ_X(A;π')⟩ = O_{π'}(X)`。 -/
  generated_eq : ∀ X : Subgroup G, A ≤ X → X < ⊤ →
    sSup (hInvariant X A (primesOf A)ᶜ) = opiCoreInG (primesOf A)ᶜ X

/-! ## Lemma 7.1 — 推移性の基底補題 -/

/-- **BG Lemma 7.1** (Inductive Lemma, mmd L2147): Hypothesis 7.1 のもと、`q ∈ π'`,
`Q₁, Q₂ ∈ ℋ_G*(A;q)`、`A ⊆ H < G` で `H ∩ Q₁ ≠ 1`, `H ∩ Q₂ ≠ 1` となる真部分群 `H` が
あれば、`Q₂ = Q₁^k` (`k ∈ K`)。`|G|_q / |Q₁∩Q₂|` の帰納が核。 -/
theorem inductiveLemma [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar ⊤ A {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ A {q})
    (H : Subgroup G) (hHproper : H < ⊤) (hAH : A ≤ H)
    (hHQ₁ : H ⊓ Q₁ ≠ ⊥) (hHQ₂ : H ⊓ Q₂ ≠ ⊥) :
    ∃ k ∈ kSubgroup A, MulAut.conj k • Q₁ = Q₂ := by
  sorry

/-! ## Theorem 7.2 / 7.3 — 推移性の rank 条件 -/

/-- **BG Theorem 7.2** (mmd L2177): Hypothesis 7.1, `q ∈ π'`, `m(Z(A)) ≥ 3` ⇒ `K` は
`ℋ_G*(A;q)` 上推移的。Prop 1.16 で `Q₁ = ⟨C_{Q₁}(C)⟩` に分解し Lem 7.1 を適用。 -/
theorem transitive_of_three_le_rank_center [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (hm : 3 ≤ rank ↥(Subgroup.center ↥A)) :
    ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q}) := by
  sorry

/-- **BG Theorem 7.3** (mmd L2187): Hypothesis 7.1, `q ∈ π'`, `m(Z(A)) ≥ 2` かつ
`q ∈ π(C_G(A))` ⇒ `K` は `ℋ_G*(A;q)` 上推移的。`R ⊇ Sylow_q(C_G(A))` 経由で Lem 7.1 を連鎖。 -/
theorem transitive_of_two_le_rank_center_of_dvd [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (hm : 2 ≤ rank ↥(Subgroup.center ↥A))
    (hqc : q ∈ (Nat.card ↥(Subgroup.centralizer (A : Set G))).primeFactors) :
    ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q}) := by
  sorry

/-! ## Theorem 7.4 — 推移性の伝播 -/

/-- **BG Theorem 7.4** (Propagation, mmd L2197): Hypothesis 7.1, `q ∈ π'`, `P` は `A` を
subnormal に含む真 `π`-部分群、`K` は `ℋ_G*(A;q)` 上推移的とする。すると:

* (a) `C_K(P) = O_{π'}(C_G(P))`,
* (b) `O_{π'}(C_G(P))` は `ℋ_G*(P;q)` 上推移的,
* (c) `ℋ_G*(P;q) ⊆ ℋ_G*(A;q)`,
* (d) 各 `Q ∈ ℋ_G*(P;q)` で `P ∩ N_G(P)′ ⊆ N_G(Q)′` かつ
  `N_G(P) = O_{π'}(C_G(P))·(N_G(P) ∩ N_G(Q))`。

`|P:A|` の帰納 + composition series 還元。 -/
theorem transitivity_propagates [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (P : Subgroup G) (hPproper : P < ⊤) (hPpi : Subgroup.IsPiSubgroup (primesOf A) P)
    (hAP : A ≤ P) (hAsub : Subgroup.IsSubnormal (A.subgroupOf P))
    (htrans : ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q})) :
    Subgroup.centralizer (P : Set G) ⊓ kSubgroup A =
        opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)) ∧
    ConjTransitiveOn (opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)))
        (hInvariantStar ⊤ P {q}) ∧
    hInvariantStar ⊤ P {q} ⊆ hInvariantStar ⊤ A {q} ∧
    (∀ Q ∈ hInvariantStar ⊤ P {q},
      P ⊓ derivedInG (Subgroup.normalizer P) ≤ derivedInG (Subgroup.normalizer Q) ∧
      ∀ n : G, n ∈ Subgroup.normalizer P →
        ∃ c ∈ opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)),
          ∃ m ∈ Subgroup.normalizer P ⊓ Subgroup.normalizer Q, n = c * m) := by
  sorry

/-! ## Proposition 7.5 — Hypothesis 7.1 の十分条件 -/

/-- **BG Proposition 7.5** (mmd L2252): `p ∈ π(G)`, `A` abelian `p`-部分群で、
(1) `A = {x ∈ C_G(A) : x^p = 1}` かつ `G` の全真部分群が `p`-length one、または
(2) ある Sylow `p`-部分群 `P` で `A ∈ SCN₂(P)`、
のいずれかなら `A` は Hypothesis 7.1 を満たす。 -/
theorem hypothesis71_of_scn2_or_pLengthOne [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] (hp_mem : p ∣ Nat.card G)
    (A : Subgroup G) (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    (hcase :
      ((A : Set G) = {x : G | x ∈ Subgroup.centralizer (A : Set G) ∧ x ^ p = 1} ∧
        (∀ M : Subgroup G, M < ⊤ → Ch1.hasPLengthOne p M)) ∨
      (∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧
        IsSCN_n p 2 (A.subgroupOf (P : Subgroup G)))) :
    Hypothesis71 A := by
  sorry

/-! ## Theorem 7.6 — Thompson Transitivity Theorem -/

/-- **BG Theorem 7.6** (Thompson Transitivity Theorem, mmd L2311): `p ∈ π(G)`,
`A ∈ SCN₃(p)`, `q ∈ p'` ⇒ `O_{p'}(C_G(A))` は `ℋ_G*(A;q)` 上推移的に作用する。
§8–§16 で最頻出。証明は Prop 7.5(2) + Thm 7.2。 -/
theorem thompsonTransitivity [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] (hp_mem : p ∣ Nat.card G)
    {A : Subgroup G} (hA : A ∈ scn3Global p G) {q : ℕ} [Fact q.Prime] (hq : q ≠ p) :
    ConjTransitiveOn (opiCoreInG {p}ᶜ (Subgroup.centralizer (A : Set G)))
      (hInvariantStar ⊤ A {q}) := by
  sorry

end OddOrder.BG.Ch2.S07
