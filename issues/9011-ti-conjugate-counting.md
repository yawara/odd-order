---
id: 9011
slug: ti-conjugate-counting
title: "TI-subset conjugate counting: |A^G| = [G:L]·|A| + class-invariant sum transport (shared GroupTheory infra)"
created: 2026-07-05
---

> **hub renumber (2026-07-05 監視 tick)**: 本 issue は lane b が 9010 で採番したが、同番号は
> lane c の `9010-frobenius-induced-degree-sum.md` が先に main 合流済み (SEQUENCE.9000 の並行
> 消費レース)。hub が **9011 に renumber** し SEQUENCE.9000 を 9011 に更新。lane b は次回
> `git merge main` でリネームを取り込むこと (b 側 worktree の 9010-ti ファイルは main の
> rename に置換される; 衝突したら 9011 側を正とする)。

# TI-subset conjugate counting: |A^G| = [G:L]·|A| + class-invariant sum transport (shared GroupTheory infra)

**Claim (lane b, 2026-07-05)** — shared-infra claim-before-build。

## 背景

Pf (13.9.a)/(13.10.1-3) の 4 producer (`S15_SAndT_Setup.analyticEstimate_*`, issue 3002
residual = consumer wiring) は全て「TI-subset の共役族の counting / class-function 和の
transport」を共通上流に持つ:

- (13.10.3) disjoint-cover counting: `|（H#)^G| = [G:S]·|H#|`, `|(Q#)^G| = [G:T]·|Q#|`
- (13.10.1)/(13.10.2) Parseval split: `Σ_{x∈(H#)^G} ‖φ(x)‖² = [G:S]·Σ_{x∈H#} ‖φ(x)‖²`
  (φ class function)

`OddOrder/GroupTheory/TISubset.lean` の `mem_of_conj_mem_conj` /
`conj_disjoint_of_ratio_not_mem` は docstring でこの counting を予告済みだが本体が無い。
`ConjClassSet.lean` にも card/sum API は無い (検索済: S04 Dade 側にも同形無し)。

## スコープ縮小 (claim 時検索の結果, 2026-07-05)

- **card 版は既存**: `OddOrder.BG.Ch4.S14.ncard_conjClassSet_of_isTISubset`
  (S14_TypePCounting.lean:6200, `|A^G| = |A|·[G:L]`) — S12/S16 が既に cite。
- **測度版も既存**: `OddOrder.Peterfalvi.S16.orbit_normSq_term` (`|A^G|/|G| = |A|/|L|`)。
- **新規に要るのは weighted 和 transport のみ** (class-invariant f)。

## やること

- [x] class-invariant `f : G → M` (`∀ g x, f (g·x·g⁻¹) = f x`, `M` AddCommMonoid) の
      和 transport: `∑_{x ∈ (Set.toFinite (conjClassSet A)).toFinset} f x
      = L.index • ∑_{a ∈ (Set.toFinite A).toFinset} f a` ([Finite G]) —
      `OddOrder/GroupTheory/TISubsetCounting.lean` `IsTISubset.sum_conjClassSet`。
      仮定は ncard 版と同形 (`IsTISubset A L` + `∀ l ∈ L, MulAut.conj l • A = A`)。

## 完了条件

✅ `IsTISubset.sum_conjClassSet` build green (2026-07-05)。S15 producer wiring (issue 3002
residual) から cite 可能。将来の hub 整理候補: BG S14 の ncard 版 + S16 orbit_normSq_term を
本 leaf へ hoist (今回は非破壊のため見送り、consumer 更新を伴うため)。

## 参照

- issues/3002-grid-property-carrier-enrichment.md (residual = consumer wiring)
- `OddOrder/Peterfalvi/S15_SAndT_Setup.lean` `analyticCounting_disjointCover` ほか 4 producer
- `OddOrder/GroupTheory/TISubset.lean:86-110` (予告 docstring)
- Pf §13 (13.9)-(13.10) = `references/peterfalvi/04.15_pp_75_86_The_Subgroups_S_and_T.mmd`

## 拡張 (07-05 loop it.38, lane b)

同クラスタとして TI-induce 値公式 2 本を追加 (issue 2034 の (13.2.e) τ=Ind 接続用):
- `IsTISubset.induce_apply_of_mem_conj`: A-supported α の Ind_L^G は飽和上で α(a)
  (非零 summand = coset yL ちょうど、|L| 個 → 正規化で collapse)
- `IsTISubset.induce_apply_of_not_mem_conjClassSet`: 飽和外で 0
