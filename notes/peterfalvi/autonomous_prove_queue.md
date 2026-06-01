# Peterfalvi 自走証明キュー (2026-05-31〜, workflow `prove` 駆動)

> ユーザー指示 (2026-05-31): 「自走キューをセットアップして進めて」。main loop が `prove` workflow を
> 1 ターゲットずつ起動 → 完了通知で**独立監査** → commit 維持 / revert / escalate → 次ターゲット launch、
> を繰り返す。worktree = `gracious-hermann` (branch `claude/gracious-hermann-78e4d8`)。
>
> **workflow**: `.claude/workflows/prove.js` (scriptPath で起動)。設計詳細 = `notes/meta/prove_workflow.md`。
> args = `{book:'peterfalvi', mode, name, decl, target_file, ready_deps, mmd, skeleton, verify}`。
> 返り status: `PASS` / `VERIFY_FAILED` / `BLOCKED_DESIGN` / `BLOCKED_IMPL`。
> 返り値の `book`/`mode`/`agent_count`/`verify` で**意図した発火モードか必ず確認** (args 文字列化 footgun の検出)。

## mode ポリシー (escalation; 検証済 = `prove_workflow.md`「検証結果」)
- **fast** (~2 agent, ~5× 安, ~2× 速): well-scoped / computational / statement shape 自明な target。judgment
  verify を落とすので **main loop 監査が安全網**。
- **full** (~8 agent): 設計重い / statement shape 非自明 / scaffold 誘惑大 / 偽署名リスク高な target。
- **escalation**: fast が `BLOCKED` か監査 NG → 同 target を full で再挑戦。明らかに設計重い (Mackey 等) は最初から full。

## main loop の各ターン手順 (厳守)
1. 直前 workflow の返り値を読む。`result.book='Peterfalvi'` かつ意図した `mode` で走ったか確認。
2. **独立監査** (status 鵜呑み禁止 — memory `autonomous-proof-workflows`):
   - `git show <commit_sha>` で diff 精読 — **faithful** (statement 弱化/量化子取り違え無)? **thin-wrapper でない** (既存 decl の純リネームでなく load-bearing)? **scaffold/hoist 無** (hard content を未充足仮説に逃がしてない)?
   - `lake build OddOrder OddOrder.AxiomsCheck` 緑 + `#assert_only_allowed_axioms <decl>` 登録 + axioms ⊆ {propext, Classical.choice, Quot.sound}。
   - sorry 数不変 (S08:188 / S09:1589 = issue 0046/0044 の 2 件のみ)。
   - 判定: **PASS & 監査 OK** → commit 維持、本キュー更新。/ **VERIFY_FAILED or 監査 NG** → `git reset --hard HEAD~1` revert → fast なら full escalate、full でも NG なら BLOCKED 記録 skip。/ **BLOCKED_*** → ツリー緑のまま、fast なら full escalate、full なら decompose 検討 or skip。
3. キューの次の未完 target を選び mode 決定 → `prove` launch。
4. ターン終了。完了通知で 1 に戻る (notification 駆動の自走)。
5. キュー枯渇 / 全 BLOCKED → ユーザーに報告して停止。

## ターゲットキュー — [Is]Thm 6.34 chain → (6.8) wiring

目標: Frobenius/Dade 設定で `Ind_H^L θ` の既約性と次数 `|W₁|θ(1)` を建て、(6.8) capstone の wiring
(η_j(1)=|W₁|, X⊂Irr L) を解禁する。chain = Mackey-first (詳細 = issue 0046 進捗節)。

| # | target | decl 候補 | mode | 依存 (✅=ready) | 状態 |
|---|---|---|---|---|---|
| P1 | (iv) 誘導次数 `Ind θ(1)=[G:H]θ(1)` | `induce_apply_one` | — | — | ✅ PASS (25873a8, 監査済) |
| P2 | Mackey 部品 `g∈H ⇒ conjBy g θ=θ` (coset well-def) | `conjBy_eq_self_of_mem` | fast | — | ✅ PASS (1b9604b, 監査済) |
| P3 | **(i) Mackey 制限 `Res_H Ind_H^G θ = ∑_{c∈G⧸H} θ^{w_c}`** (H⊴G) | `restrict_induce_eq_sum_conjBy` | **full** | P2✅ `induceTerm_of_mem_normal`✅ `groupEquivQuotientProdSubgroup`✅ | 🔵 ACTIVE |
| P4 | (ii) `‖Ind θ‖² = \|I_L(θ):H\|` (θ∈Irr H) | `inner_induce_self_eq_index_inertia` | fast→full | P3, `inner_induce_eq_inner_restrict`✅ | ⬜ |
| P5 | (iii) Frobenius 既約性: θ≠1 ⇒ `Ind θ ∈ Irr L` | `induce_irreducible_of_frobenius` | full | P4, `brauer_permutation_lemma'`✅, Ch06 Frobenius✅ | ⬜ |
| P6 | 6.34 packaging: Frobenius ⇒ `Ind θ∈Irr L ∧ deg=\|W₁\|θ(1)` | `frobenius_induce_irreducible_degree` | fast | P5+P1 | ⬜ |
| P7 | (6.8) wiring: `Y=S(H')` の `η_j(1)=\|W₁\|` | (design 決定) | full | P6 + (1.6)✅ | ⬜ (6.34 後) |
| P8 | (6.8) wiring: `X={χ∈Irr L\|Z⊄ker χ} ⊂ Irr L` | (design 決定) | full | P6 + (4.5) | ⬜ (6.34 後) |

- **P3 (Mackey) が critical gate** (P4/P5 が依存)。`BLOCKED` なら sub-brick に decompose: coset-sum
  `∑_{x∈G}f(x)=∑_{c∈G⧸H}∑_{h∈H}f(c·h)`、`∑_{h∈H}θ(h⁻¹gh)=\|H\|θ(g)` (g∈H, class-fn 定数性) を別 target 化。
- P7/P8 以降は 6.34 完了後にキュー詳細化。さらに先は (6.8) capstone 本体 ((6.8.1)/(6.8.2)/(6.8.3)、
  なお (6.8.3) degree-sum `sumNonInflatedDegreeSq_eq_index_mul` は landed 済) → S08:188 discharge。

## 採番 / メタ
- Peterfalvi 系 issue base = 1000 (`ODD_ISSUE_BASE=1000`)。本キュー note が tracker、per-target issue は原則作らない。
- 関連: `issues/0046-...md` (6.8 全体 + 6.34 roadmap), `notes/meta/prove_workflow.md` (workflow 設計+検証), `notes/peterfalvi/s08_coherence_theorems.md`。
