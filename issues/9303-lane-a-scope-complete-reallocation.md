---
id: 9303
slug: lane-a-scope-complete-reallocation
title: "レーン a の担当 2 領域が完済 — 次の割当を求む"
created: 2026-07-19
---

# HUB: レーン a の担当 2 領域が完済 — 次の割当を求む

レーン a の担当 (正本 = `notes/meta/lane_reallocation_2026_07_16.md`: **Isaacs 全域 +
Peterfalvi 本文**) について、**被覆・特殊化債務の両軸とも実測で完済**した。
ungated な残作業が無いので、次の割当を裁定されたい。

⚠ AskUserQuestion でなく本 issue で照会する ([[hub-arbitrates-cross-lane-autonomously]] の
「lane も frontier 枯渇・方向・reallocation は user でなく hub に問う」に従う)。

## 実測サマリ (2026-07-19)

正本 note 2 本:
- `notes/isaacs/frontier_measured_2026_07_19.md` (本セッションで新設、再現手順つき)
- `notes/peterfalvi/frontier_measured_2026_07_19.md`

| 領域 | 実 sorry | 番号被覆 | 特殊化債務 |
|---|---|---|---|
| **Isaacs Ch.1–10 + App** | **0** | **未形式化 0 件** (書籍 ~305 件中 267 件 repo cite / 37 件 mathlib 被覆 / 5 件 repo に記述的名前 / 欠落 0) | **検出 11 件 → 実装 11 件** |
| **Peterfalvi 本文 S01–S16** | **0** | — | 残りは**全て hub issue 9163 に gated** |

⚠ 42 件が「repo に cite が無い」のは欠落でなく**ラッパー方針**による設計 (mathlib 直対応は
意図的に repo 実装なし)。「repo に無い ⟹ 未形式化」と読まないこと。

### Isaacs で解消した特殊化債務 11 件

- `p ≠ q` の削除 4 件 — **1.31 / 1.32 / 1.36 / 7.8** (書籍はいずれも相異性を課さず証明中で導出)。
  7.8 は下流 `Ch07/ForwardFromCh03.lean` の「偽の第 2 素数」捏造も解消。
- **1.38** — 「位数**最小**」→ 書籍どおり「包含**極小**」。⚠ Isaacs 自身が p.61 で両者を区別し
  「minimal order ⇒ minimal だが逆は偽」と明記しており、真の食い違いだった。
- **3.35** — 不要な `[Finite G]` 削除。
- **3.29 / 3.30** — 可解性仮定を巡回還元で除去 (書籍が 3.23-3.28 と違い意図的に落としている仮説)。
- **7.7** — 死んでいた `P ≠ ⊥` を 6 宣言から削除。
- **5.22** — **結論の欠落**を補充: 書籍の第 2 結論 `G/A^p(G) ≅ H/A^p(H)`。
- **7.5** — ∀-Sylow 量化 → 書籍どおり単一 `P`。

### Peterfalvi で完了した分 (本セッション)

- **(9.7) 完全形式化** (issue 1043、close 済) — (a) order-a 埋め込み + **(b) `W₁ ≅ Aut F` 節**
  (`caseB_exists_galoisField_repr_withAut`)。共有抽象層
  `OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldAut.lean` を新設。

## 裁定してほしいこと

1. **hub issue 9163 (typePA / A(M) 設計裁定) の優先度**。Pf 本文の残り ((8.15) type-II 残 /
   (8.18) / **(9.11) M 側**) は全てこれに gated。9163 が裁定されればレーン a は即座に再開できる。
   ⚠ 本セッションで **(9.11) M 側も同 gate** と判明したので、9163 の波及先は当初より広い
   (詳細は 9163 への追記)。なお §15 が既に Option B′ (`honestTypeP2ASet`) を実装して
   回っている事実は、B′ の実現可能性の証拠になる。
2. **9163 が当面裁定されない場合の代替割当**。候補 (いずれもレーン a の territory 外なので
   hub 裁定が要る):
   - Pf Appendices の非 Suzuki 系 (現 c 所管: NearFields / FeitSibley — 実 sorry が残る)
   - Suzuki チェーン (現 b 所管 — 実 sorry が残る)
   - BG 残 (現 c 所管)
   - Isaacs の**演習問題 (Problems)** — ⚠ 本セッションの被覆測定は**番号付き結果のみ**を
     対象にしており演習は含まない。スコープに入れるかは方針判断 (CLAUDE.md は 3 冊の
     「全番号付き結果」を対象と書いており、演習の扱いは明示されていない)。
   - 共有 infra の先回り整備 (claim-before-build で 9000 issue を立てる)

## 完了条件

hub がレーン a の次の割当を本 issue に記録し、レーン a が一意に着手先を決められる状態になること
(9163 の裁定でも、代替割当でも可)。

## 参照

- `notes/isaacs/frontier_measured_2026_07_19.md` (本セッション新設)
- `notes/peterfalvi/frontier_measured_2026_07_19.md`
- `issues/9163-typepa-mssharp-rescope-for-815-typeii.md` (gate 本体、本セッションで波及先を追記)
- `issues/closed/1043-pf-9-7-full-fidelity.md` ((9.7) 完了)
- `issues/9164-dedup-ringaut-algaut-bridge.md` (Suzuki の inline bridge dedup、b 所管)
