---
id: 133
slug: open-scoped-classical-statement-dependent
title: "lint: open scoped Classical 11 件は statement が decidability に依存 — statement 設計は owner 判断"
created: 2026-07-20
---

# lint: `open scoped Classical` 11 件は statement が decidability に依存

## 実測 (2026-07-20 hub、全 14 ファイルを 1 つずつ外して leaf build)

`linter.style.openClassical` の警告 14 件を、**1 ファイルずつ `open scoped Classical` を外して
leaf build する**方法で判定した (上流を常に無傷に保つので判定が独立する)。

| 判定 | 件数 | ファイル (エラー数) |
|---|---|---|
| **除去可 = 証明だけの依存** | **3** | `S08_CaseBEnumeration` / `S08_CaseAWeightedEndgame` / `S09_BetaDecompOrthogonality` |
| **statement 依存** | **11** | `S04_InduceConjFinset` (16) / `S08_Theorem63` (15) / `S08_CaseBWeightedEndgame` (13) / `S08_CoherenceWeighted` (12) / `InflationInduction` (10) / `S09_CertificateDischarge` (9) / `SemilinearField` (7) / `S09_Building78C` (3) / `MobiusAssembly` (3) / `S08_CaseBAnchoredSeed` (2) / `NonInflatedDegreeSqInterval` (1) |

除去可の 3 件は本 issue 起票と同じ commit で解消済。**残る 11 件が本 issue の対象**。

## statement 依存の中身 (典型 3 パターン)

いずれも「`Classical` が無いと**定理の文が書けない**」形で、証明に `classical` を足しても直らない:

1. **`Finset.univ.filter` の述語** — `NonInflatedDegreeSqInterval:74`:
   ```
   DecidablePred fun χ ↦ ↑N ⊆ characterKernel χ ∧ ¬↑K ⊆ characterKernel χ
   ```
   `∑ χ ∈ Finset.univ.filter (fun χ => …)` が statement にある。
2. **statement 中の `if x ∈ S then … else …`** — `MobiusAssembly:414`:
   `Decidable (↑b' ∈ hyp.nLStabilizerIn B)`。
3. **`Fintype ↥(…)` の合成** — `MobiusAssembly:294`: `Fintype ↥(hyp.nLStabilizerIn B)`。

## なぜ hub が独断で直さないか

- linter が求める修正は「**decidability を statement に明示する**」= `[DecidablePred …]` /
  `[Fintype …]` を仮説に足すこと。これは**呼び出し側の API を変える**。
- 該当 11 ファイルは全て **lane a (Peterfalvi/S\*) または lane c (Appendices)** の territory。
  statement 改変は hub の機械的 call-site 追従の範囲外。
- 代替案の「`open scoped Classical in` を宣言ごとに付ける」は **warning 数がむしろ増える**
  (ファイル 1 件 → 宣言 N 件)。`set_option linter.style.openClassical false` で黙らせるのは
  「decidability を隠している」という指摘自体を消すだけなので採らない。

## owner への提案 (どれを採るかは owner 判断)

- **(A) 仮説に明示**: `[DecidablePred P]` を足す。呼び出し側は `Classical.decPred _` を渡す
  か、文脈に実インスタンスがあればそれが刺さる (有限群なので多くは後者で済む見込み)。
- **(B) 述語を Finset レベルへ移す**: `Finset.univ.filter P` の代わりに、既に Finset として
  構成済みの対象 (例 `hyp.aOrbitFinset`) を使うよう statement を書き換える。
- **(C) `Set.toFinset` + `Fintype` インスタンスを補う**: 2/3 のパターンはこれで消える。

⚠ どれも**意味は変わらない**が、統一しないと下流の呼び出しが混乱するので、
**11 件をまとめて 1 つの方針で**やるのが望ましい。

## 完了条件

`lake build OddOrder` の warning から `please avoid 'open (scoped) Classical'` が消えること。

## 参照

- `issues/0123-linter-warnings-cleanup.md` (lint 全体、wave 5 の該当項目)
- `issues/0132-naming-pairunion-stepdata-too-long.md` (同じく owner 判断待ちの lint)
- 判定スクリプト: 1 ファイルずつ `open scoped Classical` を除去 → `lake build <module>` →
  `grep -c "^error: <path>"` → `git checkout -- <path>`
