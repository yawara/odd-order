# BG §10 分割と並行レーン計画 (2026-06-07)

## 背景: なぜ分割したか

依存構造の精査 (4 エージェント調査, 2026-06-07) の結論:
- FT のクリティカルパスは **BG §10–§16 の直列スパイン**。§7–9 は sorry-free 完了。
- **§10 が gate**: §11–13 (~34 結果) はほぼ全面 §10 の sorry (Lem 10.4c/10.8/10.9/10.10/10.11d/10.12/10.13/10.14d) 待ち。
- §10 内部は **V 字**: 証明済 Thm 10.1/10.2 の上に **6–7 個の独立 leaf** (ready-now) + **直列スパイン** (10.6→10.8→10.9/10.14)。
- Pf §3–9 は BG §10–16 と**完全独立** (唯一の BG 依存は §1 Frobenius typeclass)。実 sorry は (6.8) coherence + (7.10) のみ。
- FT 下流 (Pf §13–16, S15/S16.Hypothesis) は **interface 実体化済** (13.1.d/e genuine equality, Hypothesis body opaque 0)。残 producer は上流待ち → 巻き取り。

## 分割後の §10 ファイル構成 (commit e7ad28d)

| ファイル | 内容 | sorry | 並行 |
|---|---|---|---|
| `S10_HallStructure.lean` | **凍結 base** (defs + API + Thm 10.1 fusion control + Thm 10.2 `isHall_Msigma_Malpha` M_σ/M_α Hall) | **0** | — (proved) |
| `S10_LocalLemmas.lean` | 独立 leaf: Lem 10.3/10.4/10.5/10.12/10.13, Prop 10.11(a–d) | 7 | **lane A1 (ready-now)** |
| `S10_BetaRadical.lean` | 直列 spine: Thm 10.6→10.7→10.8, Prop 10.14/Cor 10.9/Prop 10.10 | 8 | **lane A2 (serial)** |
| `S10_MalphaMsigma.lean` | **hub** (3 つを re-export, 下流は不変 import) | 0 | — |

検証済: leaf↔spine 相互参照なし (clean fan-out, 両方 base のみ import); frontier は base の private を未使用。full build 3586 緑 + AxiomsCheck OK。

## 並行レーン計画 (3-way 実質並行)

- **Lane A1 = `S10_LocalLemmas`** (最高レバレッジ・ready-now): 7 独立 leaf。互いに非依存なので 1 セッションで順次でも、さらに細分割して複数セッションでも可。
- **Lane A2 = `S10_BetaRadical`** (serial spine): 10.6→10.8→{10.9, 10.14}。これを落とすと §11–13 の β-radical ブロッカー (10.9/10.12/10.14d) が開く。
- **Lane B = Pf §3–9 (6.8) coherence** (worktree `/home/ywr/odd-order-peterfalvi`): 真の独立並行。LEG2 全体の唯一の gate。
- **(巻き取り) FT 下流**: interface 実体化は完了。残 producer (bridge / `field_normalizer_structure` / `S15.basic_structure` / τ₃ pin) は上流待ち。

§10 (A1+A2) が landing すれば §11–13 (~34 結果) が一気に開く。これが現時点の最大レバレッジ。

## 次アクション候補

- worktree `bg-s10-leaves` (A1) / `bg-s10-spine` (A2) を立てて並行セッション化 (lake/references symlink + ODD_ISSUE_BASE 割当)。
- または main で A1 leaf から順次着手 (split 済なので並行セッションが A2 を非衝突で取れる)。
