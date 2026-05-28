---
id: 42
slug: peterfalvi-s09-rho-and-7-1-7-3
title: "Peterfalvi (7.1)-(7.3): ρ map / A^τ / 積分不等式"
created: 2026-05-28
---

# Peterfalvi (7.1)-(7.3): ρ map / A^τ / 積分不等式

## 背景

`issues/0041-peterfalvi-s09-card-g0-lower-bound.md` の最初のサブ issue。
(7.1)-(7.3) は (7.10) 証明の **最下層インフラ**:

- (7.1) は Hypothesis: Dade isometry `τ` と reverse map `ρ` の設定。
- (7.2.a) は `α ∈ CF(L,A) ⇒ α^{τρ} = α` (τ の左逆として ρ)。
- (7.2.b) は `‖χ^ρ‖² ≤ ‖χ‖²` (orthogonal projection 性, (2.6)/(2.7) 使用)。
- (7.3) は積分不等式 `|G|⁻¹ Σ_{A^τ} \|χ\|² ≥ ‖χ^ρ‖²` ((7.2.b) の系)。

## やること

- [x] `OddOrder.Peterfalvi.S09` に `ρ` map (Peterfalvi `χ^ρ(a) = |H(a)|⁻¹ Σ_{x∈H(a)} χ(ax)`) の定義を入れた
      (`Hypothesis71.chiRho : (Hypothesis71 G A L) → ClassFunction G ℂ → L → ℂ`). raw function level (まだ class function に promote していない).
- [x] `A^τ` 集合は `S04.Hypothesis.dadeSupport` として既存 (`⋃ Group.conjugatesOfSet (hCoset a)`).
- [x] `Hypothesis71` structure (Hypothesis (2.2) + DadeMap τ + IsDadeMap) を define。
- [x] (7.2.a) を proof: `chiRho_dadeImage_eq`. `IsDadeMap.map_eq_of_mem_hCoset` で各 summand が `α a` に等しいことから
      `|H(a)|⁻¹ · |H(a)| · α a = α a`. sorry-free.
- [-] (7.2.b) は inner-product infra (`chiRho` の class function 化 + `‖·‖²` 用の normalized inner product) が必要 →
      **本 issue では deferred**, follow-on issue で実施。
- [-] (7.3) も同じ理由で **deferred**, follow-on issue で実施。
- [x] build pass: `lake build OddOrder.Peterfalvi.S09_NonexistenceCertain` 緑、`lake build OddOrder` 全体緑。
- [ ] (follow-on) `chiRho` を `SupportedClassFunctions ℂ A L` に promote する (HConjInvariant 仮定追加 → 既存 `S04.HConjInvariant` 利用)。
- [ ] (follow-on) (7.2.b), (7.3) の statement + proof。

## 完了条件

- (7.2.a) が sorry-free。
- (7.1) Hypothesis structure + (7.2) lemma stmt + (7.3) stmt が定義される。
- lake build 通る。

## 参照

- parent: `issues/0041-peterfalvi-s09-card-g0-lower-bound.md`
- file: `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean`
- file: `OddOrder/Peterfalvi/S07_Coherence.lean` (zSupportedSpan, IntegralCharacterMap)
- mmd: `references/peterfalvi/04.9_pp_38_43_Non-existence_of_a_Certain_Type_of_Group_of_Odd_Order.mmd` L1-34
