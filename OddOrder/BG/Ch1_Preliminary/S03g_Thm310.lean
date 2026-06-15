import OddOrder.Isaacs.Ch06_FrobeniusActions.Main
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup

/-!
# BG §3E: Proposition 3.9 and Theorem 3.10

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter I §3, §3E (mmd `references/bg/local-analysis.mmd` L1263-1357).

§3 の最後のブロック (§3E "Regular actions and nilpotent targets")。BG §3 全 10 結果のうち
3.1-3.7 は形式化済 (S03_FrobeniusActions / S03b-S03f)、本ファイルで残りの **Prop 3.9 + Thm 3.10**
を回収する。Prop 14.2(g) (`OddOrder.BG.Ch4.S14.typeP_structure` の case-τ₁ (g)) が Theorem 3.10(a)
(`|K|` 素数) を要求する (issue 2007)。

## Gorenstein 引用の対応

BG の証明が引く Gorenstein 結果は Isaacs/repo の既形式化で埋まる:
* **G 5.3.14** (`p`-group が `q`-group に regular 作用 ⟹ cyclic) = Isaacs Ch06
  (`Isaacs.Ch06.subgroups_card_prime_unique_of_frobeniusAction_sylow` +
  `false_of_frobeniusAction_actorSubgroup_isElementaryAbelian_card_prime_sq_of_finite_target`)
  + `isCyclic_of_subgroups_card_prime_unique_of_odd` ⟹ **Prop 3.9** (下記、完全証明)。
* **G 6.4.1** (P. Hall: solvable ⟹ Hall `π`-subgroup) = Isaacs Ch03。
* **Clifford (G 3.4.1) / G 3.4.3** (Thm 3.10 Case 2) =
  `OddOrder.GroupTheory.RepresentationTheory.CliffordConjugateChar` (§3B Thm 3.4/3.5 で使用)。
-/

namespace OddOrder.BG.Ch1.S03

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch06

variable {R H : Type*}

/-- **BG Proposition 3.9** (mmd L1263): if `p` is an odd prime, `R` is a finite `p`-group acting
in a Frobenius (fixed-point-free) manner on a nontrivial finite group `H`, then `R` is cyclic.

This is the abstract form of BG's statement "`R` a `p`-group acting regularly on a `p'`-group `H`
⟹ `R` cyclic": "regular" is exactly `IsFrobeniusAction R H` (no nonidentity element of `R` fixes a
nonidentity element of `H`), and the `p'`-hypothesis on `H` is unnecessary for the conclusion.

Proof: if `R` had two distinct subgroups of order `p`, it would contain an elementary abelian
`p²`-subgroup `E` (Isaacs 6.11 infra), and the Frobenius action of `E` on `H` is impossible
(`false_of_frobeniusAction_actorSubgroup_isElementaryAbelian_card_prime_sq_of_finite_target`).
Hence `R` has a unique subgroup of order `p`, so `R` is cyclic (Isaacs 6.11, odd branch). -/
theorem isCyclic_of_isPGroup_of_isFrobeniusAction
    [Group R] [Finite R] [Group H] [Finite H] [Nontrivial H]
    [MulDistribMulAction R H] {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    (hR : IsPGroup p R) (hFrob : IsFrobeniusAction R H) : IsCyclic R := by
  refine isCyclic_of_subgroups_card_prime_unique_of_odd hR hp_odd ?_
  intro K L hK hL
  by_contra hne
  obtain ⟨E, hE_elem, hE_card⟩ :=
    hR.exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_ne hK hL hne
  exact false_of_frobeniusAction_actorSubgroup_isElementaryAbelian_card_prime_sq_of_finite_target
    hFrob E Fact.out hE_elem hE_card

end OddOrder.BG.Ch1.S03
