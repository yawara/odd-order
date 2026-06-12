/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem1212b

/-!
# BG §12: Theorem 12.12 — three-case assembly

**スコープ**: BG Theorem 12.12 (mmd L3336-3373) の最終組立。仮定は「すべての
`(τ₁(M) ∪ τ₃(M))`-元 `e ∈ E#` で `C_{M_σ}(e) = 1`」(`hreg`)。結論 `FrobFactConclusion M E`:
(a) `E` は abelian normal `A₀` を含み `∀ x ∈ M_σ#, C_E(x) ⊆ A₀`;
(b) `E` は `E` と同 exponent の `E₀` を含み `E₀ M_σ` は kernel `M_σ` の Frobenius 群。

**証明の 3 ケース** (BG L3341-3344):

* **Case 1** (`τ₂(M) = ∅`, BG: `E = E₁E₃`): すべての `e ∈ E#` の素因数が `τ₁ ∪ τ₃` に入る
  ので `hreg` は無条件化し、`A₀ = 1`, `E₀ = E` で `frobFact_of_regular_all` が直ちに与える。
* **Case 2** (`τ₂(M) ≠ ∅`, 非可換 Sylow `p`): `frobFact_of_nonabelianSylow` (Theorem 12.7 経由)。
* **Case 3** (`τ₂(M) ≠ ∅`, すべての Sylow が可換): `frobFact_of_abelianSylow` (Lemma 12.8 +
  per-prime cyclic `Z_p` 構成の集約; **本ファイルの主たる残務**)。

ケース分けは「`|E|` を割る `τ₂`-素数で非可換 Sylow をもつものが存在するか」で行う。`τ₂(M)` の
素数はすべて `|E|` を割る (`p ∉ σ(M)` ゆえ `p ∤ |M_σ|`、かつ `pRank_M = 2` から `p ∣ |M|`) ので、
素数性は `Nat.prime_of_mem_primeFactors` で自動的に得られる。
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.Isaacs.Ch06
open scoped Pointwise
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- **BG Theorem 12.12, Case 3** (mmd L3344-3373): in the abelian-Sylow regime, with `τ₂(M)`
nonempty, the conclusion `FrobFactConclusion M E` holds. Here `A₀ = E₂` (abelian normal Hall
`τ₂`-subgroup of `E`, by Lemma 12.8(a)), and `E₀ = E₁E₃ · ∏_{p ∈ τ₂} Z_p`, where each `Z_p` is a
cyclic normal subgroup of `E` of the same exponent as a Sylow `p`-subgroup `S_p ≤ E` and acting
regularly on `M_σ` (`exists_cyclic_Enormal_regular_of_abelianSylow`).

`habel` provides that every Sylow `p`-subgroup of `G` (for `p ∈ τ₂(M)` dividing `|E|`) is abelian;
`hτ2` witnesses the nonemptiness of `τ₂(M) ∩ π(E)`.

**TODO** (Lane F): the `τ₂`-product aggregation `E₀` together with `exp(E₀) = exp(E)` and the
regularity of `E₀` (via `inf_centralizer_eq_bot_of_forall_prime_order`, reducing to prime-order
elements: those of `τ₁ ∪ τ₃`-order use `hreg`, those of `τ₂`-order lie in the relevant `Z_p`). -/
theorem frobFact_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hτ2 : ∃ p ∈ (Nat.card ↥E).primeFactors, p ∈ tau2 M)
    (habel : ∀ q, q ∈ (Nat.card ↥E).primeFactors → q ∈ tau2 M →
      ∀ S : Sylow q G, IsMulCommutative ↥(S : Subgroup G))
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    FrobFactConclusion M E := by
  sorry

/-- **BG Theorem 12.12** (mmd L3336): suppose `C_{M_σ}(e) = 1` for every
`(τ₁(M) ∪ τ₃(M))`-element `e ∈ E#`. Then
(a) `E` contains an abelian normal subgroup `A₀` with `C_E(x) ⊆ A₀` for all `x ∈ M_σ#`, and
(b) `E` contains a subgroup `E₀` of the same exponent as `E` such that `E₀ M_σ` is a Frobenius
group with Frobenius kernel `M_σ`.

(Scaffold moved here from `S12_E.lean`.) Proof by the three-case split described in the file
header. The case selector is whether some `τ₂(M)`-prime dividing `|E|` has a nonabelian Sylow
`p`-subgroup in `G`. -/
theorem frobenius_factorization_of_regular [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    FrobFactConclusion M E := by
  by_cases hnonab : ∃ p ∈ (Nat.card ↥E).primeFactors, p ∈ tau2 M ∧
      ∃ S : Sylow p G, ¬ IsMulCommutative ↥(S : Subgroup G)
  · -- **Case 2**: a `τ₂`-prime with a nonabelian Sylow.
    obtain ⟨p, hpE, hp, hS⟩ := hnonab
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpE⟩
    obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hp
    exact frobFact_of_nonabelianSylow hG h hp hA hAE hS hreg
  · -- No `τ₂`-prime has a nonabelian Sylow: all relevant Sylows are abelian.
    have habel : ∀ q, q ∈ (Nat.card ↥E).primeFactors → q ∈ tau2 M →
        ∀ S : Sylow q G, IsMulCommutative ↥(S : Subgroup G) := by
      intro q hqE hq S
      by_contra hc
      exact hnonab ⟨q, hqE, hq, S, hc⟩
    by_cases hτ2 : ∃ p ∈ (Nat.card ↥E).primeFactors, p ∈ tau2 M
    · -- **Case 3**: `τ₂(M) ≠ ∅`, abelian Sylows.
      exact frobFact_of_abelianSylow hG h hτ2 habel hreg
    · -- **Case 1**: no `τ₂`-prime divides `|E|`, so `E = E₁E₃` and `hreg` is unconditional.
      refine frobFact_of_regular_all hG h (h.E_ne_bot hG) ?_
      intro e heE hene
      refine hreg e heE hene ?_
      intro r hr
      obtain ⟨hrp, hrd, _⟩ := Nat.mem_primeFactors.mp hr
      have hrE : r ∈ (Nat.card ↥E).primeFactors := by
        exact Nat.mem_primeFactors.mpr ⟨hrp, hrd.trans (E.orderOf_dvd_natCard heE), Nat.card_pos.ne'⟩
      have hru : r ∈ tau1 M ∪ tau2 M ∪ tau3 M :=
        h.mem_tau_union_of_mem_primeFactors hG hrE
      have hrnτ2 : r ∉ tau2 M := fun hr2 => hτ2 ⟨r, hrE, hr2⟩
      rcases hru with (h1 | h2) | h3
      · exact Or.inl h1
      · exact absurd h2 hrnτ2
      · exact Or.inr h3

end OddOrder.BG.Ch3.S12
