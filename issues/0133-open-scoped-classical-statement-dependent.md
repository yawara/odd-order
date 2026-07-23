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
- ⚠ **2026-07-23 訂正 (この前提は誤りだった)**: 「`open scoped Classical in` を宣言ごとに付けると
  warning がむしろ増える (ファイル 1 件 → 宣言 N 件)」は**誤り**。linter は **bare な
  file/section-level `open (scoped) Classical` だけを flag** し、**per-declaration
  `open (scoped) Classical in` は flag しない**。linter message 自身が
  "use `open Classical in` for definitions or instances, the `classical` tactic for proofs" と
  推奨している。実測: `S04_InduceConjFinset` は `open ... in` を 5 個持つが warning は bare 1 個のみ。
  → **localization** (bare 除去 + 影響 decl ごとに直前へ `open scoped Classical in`、proof だけなら
  `classical` タクティク) が linter 公認の fix で、**statement/signature を一切変えない** (option A の
  `[DecidablePred]`/`[Fintype]` 追加による call-site API 変更は不要)。`set_option ... false` は指摘
  自体を消すだけなので依然不採用。

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

---

## ✅ 2026-07-23 実施 (lane a) — 8/11 ファイルを localization で解消

上記「訂正」に基づき **option A でなく localization** で解消 (linter 公認・API 非改変)。手順は
各ファイルで: **bare `open scoped Classical` を除去 → `lake build` で decidability error 箇所を採取
→ 各 error を囲む top-level 宣言の docstring 直前へ `open scoped Classical in` を挿入** (proof のみの
decidability も `open ... in` が宣言全体を覆うので同一手で足りる)。error 行→宣言のマッピングは
`scratchpad/localize_classical.py` で自動化 (docstring/`@[…]`/`omit … in`/`structure` を跨いで挿入点を
確定、`@[simp] theorem` と `omit … in` の前置きは要手当)。

**lane-a 所有の 8 ファイル = 全解消** (各 leaf build green・openClassical 0・新規 warning 0):

| ファイル | 局所化した宣言数 |
|---|---|
| `S04_InduceConjFinset` | 8 |
| `S04_DadeIsometry/MobiusAssembly` | 2 |
| `S08_CaseBAnchoredSeed` | 2 (def) |
| `S08_CaseBWeightedEndgame` | 4 |
| `S08_CoherenceWeighted` | 6 + 1 `structure` |
| `S08_Theorem63` | 3 |
| `S09_Building78C` | 4 + 1 `@[simp]` |
| `S09_CertificateDischarge` | 2 |

`bin/lint-baseline.tsv` を 181→173 に ratchet-down (openClassical 8 件除去)。ratchet gate 緑。

**残 3 ファイル (本 issue 継続)** — lane-a territory 外ゆえ未着手:
- `GroupTheory/RepresentationTheory/InflationInduction` / `NonInflatedDegreeSqInterval` (shared infra)
- `Appendices/SemilinearField` (lane c)

同一 localization 手順で解消可能 (option A も API 変更も不要)。これらが片付けば baseline から
openClassical が消え、issue クローズ + `--strict` gate へ一歩前進。**注意**: これらは所有レーンが
frontier 通過時に、または shared-infra claim の上で解消する (hub 調整)。
