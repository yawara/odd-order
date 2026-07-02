---
id: 50
slug: lean-eval-submission-candidates
title: "lean-eval 提出候補の定理を棚卸し・パイプライン化"
created: 2026-05-30
---

# lean-eval 提出候補の定理を棚卸し・パイプライン化

## 背景

`leanprover/lean-eval` (公開面 https://lean-lang.org/eval/) は **comparator 方式**の公式
formal-math ベンチ。problem ごとに `Challenge.lean` が文を固定し, 解答者が `Submission.lean`
で証明 → **comparator が受理したら solved**。解答側は **Mathlib 自由使用可**。トピック
フォルダに `GroupTheory` / `Algebra` / `RepresentationTheory` があり, 本リポ (FT 形式化) は
「mathlib にまだ無い研究級の有限群論定理」を量産できる立場なので, lean-eval の弾の鉱脈。

すでに **Baer-Suzuki (p-core 版)** を提出済 (issue 0042 close, `notes/meta/lean_eval_baer_suzuki.md`)。
ユーザの当面の狙いは Burnside / 最終的に odd-order。この issue は **提出候補を一覧化し,
各々を 0042 と同型の per-theorem sub-issue に落とすためのアンブレラ (index)**。

「良い challenge / 解きやすい submission」の 3 軸:
1. **有名・名前がある** (ベンチ価値)
2. **statement が mathlib 既存 def だけで self-contained** (comparator が文を pin する。
   自作 def への依存が少ないほど提出が楽。J(P) など bespoke def は Challenge に焼き込みが要る)
3. **証明が難しく mathlib 未収録** (でないとベンチにならない)

## 提出候補一覧 (本リポ現状つき)

凡例: ✅=本リポに sorry-free で存在 / 🚧=構築中 / 🔭=未着手(将来通る道)

| 定理 | 本リポ現状 | self-contained 度 | 知名度 |
|---|---|---|---|
| Baer–Suzuki (p-core) | ✅ 提出済 (0042) | 中 | 高 |
| **Frobenius の定理** (核=正規補群) | 🚧 Ch06 で機構ほぼ完成 | 中 (Frobenius 条件を文に内包) | 最高 |
| **Thompson 正規 p-補群** (Isaacs 7.5/7.6) | ✅ 0029/0030 close | 高 | 最高 |
| **Burnside 正規 p-補群** (Isaacs 7.8) | ✅ 0032 close | 高 (Sylow+正規化群+中心のみ) | 高 |
| **Burnside p^aq^b 可解性** | 🚧 S7D1 Matsuyama 流で構築中 | 最高 (`card=p^a*q^b → IsSolvable`) | 最高 |
| Hall の定理 (可解 ⟺ 全 π で Hall) | 🚧 0012 open | 高 | 最高 (Sylow の次) |
| Fitting 部分群 nilpotent / F(G) | 🚧 0011 open | 高 (「正規 nilpotent で生成」を inline) | 高 |
| Thompson FPF-自己同型 ⇒ nilpotent (1959) | 🔭 | 最高 (def 不要で綺麗) | 高 |
| Glauberman ZJ 定理 | 🚧 App.B Puig 系 (2000/2001) | 低 (J(P) を Challenge に焼き込み要) | 高 |
| Brauer–Fowler (対合中心化群で位数有界) | 🔭 Peterfalvi 系 | 中 | 高 (CFSG の起点) |
| **Feit–Thompson (奇数位数)** | 🔭 最終目標 | 最高 (`Odd (card G) → IsSolvable`) | 伝説級 |

> 「Burnside theorem」は二義: **p^aq^b 可解性** (有名な方, S7D1 で 🚧) と **正規 p-補群版**
> (Isaacs 7.8, ✅ 0032)。両方とも別個に提出できる。

## やること

- [ ] **lean-lang.org/eval に各 problem が存在するか / signature を確認**
      (存在しない場合は「解く」でなく「提案」になる。0042 は stub 提示済だった)
- [ ] **即提出ライン (✅ もの) を per-theorem sub-issue 化** — 0042 と同型 (repo 定理 ↔ eval
      signature の橋渡し + `AxiomsCheck` + `notes/meta/lean_eval_<name>.md`):
  - [ ] Thompson 正規 p-補群 (0029/0030 の成果を submit 形に)
  - [ ] Burnside 正規 p-補群 (0032 の成果を submit 形に)
  - [ ] Frobenius の定理 — **提出前に「核の存在を証明しているか (古典 Frobenius の難所),
        それとも核を前提にしているか」を要確認**。存在こそが lean-eval 向きの core
        ([Ch06 FrobeniusGroup.lean](../OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroup.lean):
        `kernel_eq_notConjugateSet` / `trivialIntersection` / `card_kernel_modEq_one` 周辺)
- [ ] **🚧 ライン (進行待ち)**: Burnside p^aq^b (S7D1 完成後) → Hall (0012) → Fitting (0011)
- [ ] **🔭 ライン (将来)**: Thompson FPF-nilpotency / Brauer–Fowler / Glauberman ZJ → odd-order
- [ ] 各提出時に self-contained 度を確認 (bespoke def 依存は Challenge への焼き込み or 複製)

## 完了条件

- アンブレラ issue。各候補が **per-theorem sub-issue (0042 型) に落ちきった**, または
  上記一覧が `notes/meta/` の常設トラッカーへ移行したら close。
- 単発の提出そのものは各 sub-issue 側の完了条件 (eval submit 可能形 + `AxiomsCheck` pass)
  に従う。

## 参照

- lean-eval: https://github.com/leanprover/lean-eval / 提出先 https://github.com/leanprover/lean-eval-submissions / 公開面 https://lean-lang.org/eval/
- 先行: issue 0042 (Baer-Suzuki), [`notes/meta/lean_eval_baer_suzuki.md`](../notes/meta/lean_eval_baer_suzuki.md)
- 関連 open: 0011 (Fitting), 0012 (Hall), 2000/2001 (App.B Puig / ZJ 系)
- 関連 close: 0029/0030 (Thompson 正規 p-補群), 0032 (Burnside 7.8)
- 文献: 100定理の未形式化は幾何/解析/超越数中心で群論の低い果実は無い
  (https://leanprover-community.github.io/100-missing.html); research-level は SOTA でも
  pass 率 ~10% (RLMEval, https://arxiv.org/pdf/2510.25427)

## 🧾 注記 (2026-07-02 hub 全体レビュー)

- 候補表は stale。現状更新 (2026-07-02 確認):
  - **Burnside p^aq^b 可解性** = ✅ **axiom-clean 完成** (`OddOrder.Isaacs.Ch07.burnside_p_pow_q_pow`,
    `OddOrder/AxiomsCheck.lean:~621` の `#assert_only_allowed_axioms` pass)。表の 🚧 は旧情報。
  - **Thompson 系** (正規 p-補群 7.5/7.6) も ✅ のまま提出可能ライン。
- 本 issue は **off-FT-path** (lean-eval 提出は FT 経路の実質的証明の積み上げでない) につき
  **park**: FT 経路凍結後の coverage phase まで着手しない (CLAUDE.md「FT 経路限定」)。
