---
id: 184
slug: brauer-suzuki-eval-submit
title: "lean-eval proof submit: brauer_suzuki (Q₈ 完成で解禁)"
created: 2026-08-20
---

# lean-eval proof submit: `brauer_suzuki`

> **状態: CLOSED (2026-08-20)** — repo 側の数学・整備は完遂。提出操作はユーザー裁定で行わない
> (末尾参照)。

親 tracker = [0050](0050-lean-eval-submission-candidates.md) の checklist 項目
「🎯 (proof submit・凍結解除待ち) `brauer_suzuki`」。**2026-08-07 に issue 0147 (Q₈) が閉じた
ことで前提条件が消滅**し、着手可能になった (0050 / `notes/meta/lean_eval_submission.md` §0・§2.5
の「Q₈ 完成待ち」記述は stale)。

`brauer_suzuki` は lean-eval の GroupTheory で **未解決 (solver 0)**。本リポは 3 ケース
(cyclic / `|T| = 8` / `|T| ≥ 16`) すべてを sorry-free で持つ唯一の形式化。

## eval 側の statement (2026-08-20 実測)

`manifests/problems/brauer_suzuki.toml` → `LeanEval/GroupTheory/BrauerSuzuki.lean`:

```lean
theorem brauer_suzuki {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 3 ≤ n)
    (P : Sylow 2 G)
    (hquat : Nonempty ((P : Subgroup G) ≃* QuaternionGroup (2 ^ (n - 2))))
    (t : G) (ht_mem : t ∈ (P : Subgroup G)) (ht_ord : orderOf t = 2) :
    (QuotientGroup.mk t : G ⧸ oddCore G) ∈ Subgroup.center (G ⧸ oddCore G)
```

`oddCore G := sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}`
(`LeanEval/GroupTheory/Defs/OddCore.lean`; mathlib に `O(G)` 相当は無い)。

## repo 側との差分 (3 本)

1. **一般化 (特殊化債務)** — 一般四元数 Sylow からの結論は現在
   `RankOneHypothesis.brauerSuzuki` (RankOneAffineModel.lean:322) の**中に埋まっており**、
   `RankOneHypothesis` に特殊化されている。3 ケース分岐 (cyclic / Q₈ / `|T| ≥ 16` setup 組立) を
   **仮説なしの top-level 定理へ括り出す**。CLAUDE.md「特殊化債務はできる限り一般化する」に
   照らして eval と無関係に必要な作業。
2. **結論形の橋** — repo は `oPiCore {p | p ≠ 2} G ⊔ C_G(z) = ⊤`、eval は `z̄ ∈ Z(G/O(G))`。
   `oPiCore_sup_centralizer_eq_top_of_mk_mem_center` (BrauerSuzukiEndgame.lean:148) の**逆向き**が
   未整備 (易しい: `G = K·C` ⟹ 任意の `g = k·c` で `ḡ z̄ ḡ⁻¹ = z̄`)。
3. **`oddCore` = `oPiCore {p | p ≠ 2}`** (有限群) — `Odd (Nat.card N)` ⟺ `N` が `{p | p ≠ 2}`-群。

## やること

- [x] (1) 一般 statement を `OddOrder/GroupTheory/BrauerSuzukiGeneral.lean` に括り出し
      (`brauerSuzuki_of_quaternionSylowTwo`)、`RankOneHypothesis.brauerSuzuki` を呼び出しに縮める
      (commit `26c6c935c`; RankOneAffineModel 1075 → 889 行、消費者の消えた薄いラッパー
      `brauerSuzuki_quaternionSylow_q8` は削除)
- [x] (2) 逆向き橋 — `mk_mem_center_of_sup_centralizer_eq_top` (**任意の正規部分群**へ一般化した方が
      商の型を跨ぐ transport が要らず綺麗だったのでそちらに) + `brauerSuzuki_mk_mem_center`
- [x] (3) `AxiomsCheck` 登録 (7 本) + `OddOrder.lean` 配線 + フルビルド green
- [x] (4) `oddCore` ↔ `oPiCore {p | p ≠ 2}` — `isPiGroup_ne_two_iff_odd` /
      `oPiCore_ne_two_eq_sSup_normal_odd` / `brauerSuzuki_mk_mem_center_oddCore` (commit `fba43b094`)。
      **eval statement を逐語コピーして 1 行で証明できることを確認済** (`lake env lean` で
      `depends on axioms: [propext, Classical.choice, Quot.sound]`)
- [x] (4.5) **import 衛生** — `characterKernelSubgroup` を §13 → §3 に hoist (commit `64cba93b3`)。
      Endgame が定義 2 本のために §11–§13 spine を丸ごと import していたため、
      **import 閉包 775 module / 402k 行 → 362 module / 115k 行 (−71%)**
- [x] (5) self-contained workspace — `odd-order-submission/brauer_suzuki/` (commit `c3019b4`)。
      eval scaffold (`generated/brauer_suzuki` @ `7699436`) + `scripts/extract_feit_thompson.py`
      で 362 module を抽出。**lean-eval 自身の mathlib rev (`6f1ef4e5…`) で
      `lake build Submission Solution Challenge` が green (9,076 jobs / 4m25s)、抽出 source の
      改変ゼロ**。`Submission.brauer_suzuki` / challenge 側 `brauer_suzuki` とも
      `[propext, Classical.choice, Quot.sound]` のみ (= `config.json` の `permitted_axioms`)。
      付随整備: `check_source_lock.py` を lock 記載の `entry_module`/`submission_directory` で
      駆動して multi-submission 対応 / 上流 HEAD の module 数を固定値で assert していた
      stale test を構造検査に置換 (32 tests pass) / README (en/ja) を submission 一覧構成へ /
      `tools/BrauerSuzukiAxiomsCheck.lean`
- [x] (6) 0050 / `lean_eval_submission.md` の stale 記述 (Q₈ 待ち) を更新 (commit `7ba074f30`)

## 完了条件

eval の `brauer_suzuki` を repo 由来の証明で埋めた `Submission.lean` が
self-contained workspace でビルド green、かつ `#print axioms` が標準 3 公理のみ。
**→ 2026-08-20 達成**。

## ✅ CLOSED (2026-08-20) — 提出はしない (ユーザー裁定)

> **「submission系は記録に過ぎないから、今後も触らないで」** (ユーザー 2026-08-20)

`odd-order-submission` リポジトリと lean-eval への提出操作は**今後の作業対象から外す**。
以下は**やらない**:

- ~~`odd-order-submission` を push~~ — ローカルに commit `1a048d1` が 1 本残るが未 push のまま放置
- ~~`leanprover/lean-eval-submissions` に issue を立てる~~
- ~~comparator + nanoda replay~~ / ~~theorem-only slice v2~~

**⚠ 本 issue の価値は提出物ではなく repo 側の成果**であり、そちらは全て main に入っている
(一般化 / 商形の橋 / `O(G)` 対応 / import 衛生 −71%)。提出可能な状態まで検証済という事実だけ
記録として残す。将来この判断が覆るまで、submission workspace の再生成・検証はしない。

## 参照

- 正本: [`notes/meta/lean_eval_submission.md`](../../notes/meta/lean_eval_submission.md) §1.2 / §2.5
- 前例: 0042 (baer_suzuki) / 0120 (feit_thompson leanOptions parity)
- Q₈: [0147](0147-q8-modular-char-theory-frozen.md) / 9506
