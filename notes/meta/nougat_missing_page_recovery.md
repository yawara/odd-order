# Nougat MISSING ページの復元 — 方法と BG での実績 (2026-06-01)

`references/*.mmd` は Nougat (`0.1.0-base`) 抽出物。密な displayed 数式のページで Nougat が
**反復ループ (repetition)** に陥り、`[MISSING_PAGE_FAIL:N]` / `[MISSING_PAGE_EMPTY:N]` マーカーに
置換されるか、稀に**式を1個だけ黙って落とす** (マーカー無し) ことがある。`N` は **PDF 物理ページ番号**
(= `Read references/<book>.pdf pages=N` の 1-based index と一致)。BG 本体 (§10 以降) では `book page ≈ N − 13`。

## 結論: Nougat 再実行では復元できない。画像読みが正解

`references/.venv` に nougat-ocr 0.1.17 + CUDA torch (RTX 4090) + base/small 両モデル完備で
`nougat <pdf> -p N --no-skipping` でページ指定再実行は**可能**。だが検証 (BG p.123) の結果:

- **base/fp16, base/fp32 (`--full-precision`), small** の3通りとも、同じ密な式で**同じ反復ループを再現**。
  decode が決定的なので再実行は無意味。`--no-skipping` で得られるのは**ループ突入前の prefix だけ**。
- マーカー無しの「式1個脱落」(13.10(c) 等) は再実行で同じ脱落を再現。

→ **確実な復元手段 = PDF ページの画像読み** (`Read references/bg/local-analysis.pdf pages=N`)。
Read tool は PDF ページを画像として読め、Nougat が落とす密な数式も人間可読。

## BG `local-analysis.mmd` の MISSING 全 14 + dropped-formula の処理状況

| マーカー (PDF頁) | 章節 | 内容 | 状態 |
|---|---|---|---|
| §13.10(c), 13.11 (p.102-103) | §13 | dropped formula (マーカー無し) | **✅ 復元** (画像読み→splice) |
| EMPTY:139, EMPTY:140 (book 126-127) | §16 | **Theorem E 全文** + Thm D(4) tail + Thm A-E schematic proof | **✅ 復元** (最高価値) |
| EMPTY:123 (book 110) | §14 | **Lemma 14.6 全文** + Lemma 14.5(c) | **✅ 復元** |
| EMPTY:147 (§16→App 境界) | §16末 | **PDF blank ページ** (Thm II は L4510 に健在) | **✅ 確認のみ** (statement 損失なし; comment 付与) |
| EMPTY:117 (book ~104) | §13 | §13 最終結果の **proof body** (statement 無) | ⏸ defer (scaffold は statement のみ要) |
| EMPTY:151 (book ~138) | App | Appendix proof body | ⏸ defer (低価値) |
| EMPTY:169 (book ~156) | App D | App D (CN-groups) proof | ⏸ defer (App D は scaffold SKIP 方針) |
| EMPTY:184 (book ~171) | 文献 | bibliography ページ | ⏸ defer (数学的内容無) |
| FAIL:29/87/92, EMPTY:7/13/67 | §1-§9 | 既形式化領域 | ⏸ defer (Lean に既存) |

**方針**: scaffold に効く **statement/definition を持つ forward ページのみ復元** (139/140/123)。
proof body・appendix・文献は defer (低価値; 必要時に同手順で画像読み)。各 splice には
`<!-- pp.N recovered from PDF by visual read ...; 2026-06-01 -->` の追跡コメントを付与。

## 他書の MISSING (未処理、同手順で可)

- **Peterfalvi §10** `[MISSING_PAGE_EMPTY:15]` = (8.14)-(8.17) statement — scaffold 着手時に画像読み要。
- Peterfalvi §14/§16 等も scaffold plan note 参照。
- Isaacs / Gorenstein の MISSING は対応 Lean が既存 or 補助参照のため優先度低。

## 再実行が有効な唯一のケース

`MISSING_PAGE_FAIL` が**レイアウト都合** (テキスト主体ページで稀に発生) の場合は `-p N --no-skipping`
で全文回収できることがある。密な数式が原因のループ (大多数) では prefix のみ。判別は安いので
「まず `-p N --no-skipping` で試し、ループ式が残れば画像読みで補う」ハイブリッドが実務的。
