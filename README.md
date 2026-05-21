# odd-order

**Feit-Thompson 定理** (奇数位数定理)「位数が奇数の有限群はすべて可解である」の **Lean 4 + mathlib による完全形式化**を目指す長期プロジェクト。AI エージェント駆動。

## 概要

3 冊の教科書を順次 Lean 化する形で進める:

1. **Isaacs**, *Finite Group Theory* (AMS GSM 92, 2008) — 有限群論の前提一式 (Fitting, Hall, Frobenius, ZJ, transfer, F\*)
2. **Bender–Glauberman**, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994) — FT 局所解析 + 最終矛盾
3. **Peterfalvi**, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000) — FT 指標理論

詳細な計画・章節チェックリストは [ROADMAP.md](ROADMAP.md)、AI エージェント向けの開発規約は [CLAUDE.md](CLAUDE.md) を参照。

## ビルド

```bash
lake exe cache get   # mathlib のプリコンパイル済みキャッシュ取得 (初回 / mathlib 更新時)
lake build OddOrder
```

Lean toolchain は [`lean-toolchain`](lean-toolchain)、mathlib バージョンは [`lakefile.toml`](lakefile.toml) で固定。

## リポジトリ構成

| パス | 内容 |
|---|---|
| [OddOrder/](OddOrder/) | Lean ソース本体 (Phase 1 以降ここを埋めていく) |
| [ROADMAP.md](ROADMAP.md) | 長期計画・フェーズ・依存グラフ・チェックリスト |
| [CLAUDE.md](CLAUDE.md) | AI エージェント向け規約 (やらないこと、ファイル粒度、namespace、主要パス) |
| `notes/` | 章節単位のミニロードマップ・調査メモ |
| `references/` (gitignored) | 教科書 PDF + Nougat 抽出 Markdown — 別 private リポ `odd-order-references` をチェックアウト |

## ステータス

- ✅ **Phase 0**: プロジェクト初期化 (Lean 4 + mathlib、ロードマップ、教科書 PDF 整備、Nougat 抽出パイプライン)
- ⏳ **Phase 1**: Isaacs 形式化 (これから)

## ライセンス

未定。
