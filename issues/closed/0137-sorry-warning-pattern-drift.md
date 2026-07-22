---
id: 137
slug: sorry-warning-pattern-drift
title: "sorry 警告文言のドリフト: count-sorry の ground-truth grep が v4.32 実文言に不一致"
created: 2026-07-21
---

# sorry 警告文言のドリフト: count-sorry の ground-truth grep が v4.32 実文言に不一致

## 背景

姉妹プロジェクト iut (`/home/ywr/iut`) のセットアップ作業 (2026-07-21) で実測発見。
v4.32.0-rc1 の sorry 警告の実文言は ``declaration uses `sorry` `` (**バッククォート**)
だが、`bin/count-sorry` の docstring が ground truth として案内するコマンドは

```sh
lake build OddOrder 2>&1 | grep -c "declaration uses 'sorry'"
```

で **シングルクォート前提 → 常に 0 を返す** (絶対数の照合手段が壊れている)。
iut では同パターンを移植した warning フィルタが実際にすり抜けた実害あり
(iut `notes/meta/lean_formalization_tips.md` §3 に記録)。

repo 内の該当は grep 実測で `bin/count-sorry:14` の 1 箇所のみ (CI・notes/meta には無し)。
count-sorry 本体は comment-strip + token count なので影響なし — 壊れているのは
docstring の照合コマンドだけ。

## やること

- [ ] `bin/count-sorry` docstring の ground-truth コマンドを引用符非依存の
      `grep -c "declaration uses .sorry."` に修正
- [ ] 実際に full build 出力で新パターンのヒット数と `bin/count-sorry` の値を突き合わせ、
      乖離があれば記録 (token count vs declaration count の既知差は docstring 通り)

## 完了条件

docstring のコマンドが実文言にマッチし、実測の照合結果が commit message か
本 issue の Close notes に残っている。

## 参照

- `bin/count-sorry:14`
- iut 側の記録: `/home/ywr/iut/notes/meta/lean_formalization_tips.md` §3、
  `/home/ywr/iut/bin/check-warnings` (引用符非依存パターンの実装例)
- 関連: issue 0138 (ゼロ警告 gate — 同じ warning フィルタを使う)

---

## ✅ Close (2026-07-22 hub)

- docstring の照合コマンドを引用符非依存 `grep -c "declaration uses .sorry."` に修正 (bin/count-sorry:14)。
- 実測照合: 本日 11:5x full build gate (4627 jobs, gate_final.log) で
  `uses .sorry.` 警告 = **7** / `bin/count-sorry` = **7** — 完全一致 (乖離なし)。
