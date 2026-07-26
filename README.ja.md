# odd-order

[English](README.md) | 日本語

**Feit–Thompson の奇数位数定理** — *奇数位数の有限群はすべて可解である* — の **Lean 4 + mathlib** による完全形式化と、それを支える有限群論のライブラリ。

```lean
theorem feitThompson {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G)) :
    IsSolvable G
```

## 現状

**奇数位数定理は証明済みで、公理もクリーン** (2026-07-15):

```
#print axioms OddOrder.feitThompson
-- 'OddOrder.feitThompson' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`sorryAx` もプロジェクト固有の公理も無く、依存するのは Lean 標準の 3 公理のみ。

プロジェクトは現在第 2 フェーズにある: 奇数位数定理が必要とする経路だけでなく、
**3 冊の原典教科書を丸ごと形式化する**。

> 🚧 **Lean ソース (`OddOrder/`) に残る `sorry` は 1 つ**: Brauer–Suzuki の定理の `Q₈` の場合 —
> 原典はどれもこれを文献参照するだけで、証明していない。これに依存する結果
> (Peterfalvi の Appendix C, Proposition 1 とその下流) だけが条件付きであり、それ以外はすべて —
> 上の公理検査が示す通り `feitThompson` を含めて — `sorry` 無しである。解消の計画:
> Navarro の *Characters and Blocks of Finite Groups* に沿って、Z\*-定理までの
> モジュラー指標理論を形式化する。

## Feit–Thompson の定理のその先へ: 有限群論ライブラリ

Feit–Thompson の証明には、mathlib がまだ持っていない大量の有限群論が必要になる。
その理論がこのリポジトリの大部分を占めており、その完成は今ではそれ自体が独立した目標である:

- **Isaacs**, *Finite Group Theory* (AMS GSM 92, 2008) — 一般的な前提一式: Fitting 部分群、
  Hall 部分群と π-可分性、互いに素な作用、Frobenius 群、転送 (transfer)、Thompson 部分群と ZJ、
  一般化 Fitting 部分群 `F*(G)`。
- **Bender–Glauberman**, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994) —
  局所解析と最終矛盾。
- **Peterfalvi**, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000) —
  指標理論の側: Dade の等長写像 (Dade isometry)、コヒーレンス、例外指標の議論。
- **Gorenstein**, *Finite Groups* (1968) — **部分的にのみ**。Bender–Glauberman は証明をしばしば
  Gorenstein に委ねており ("**G**, Thm X.Y.Z")、特に p-安定性・ZJ・小階数 p-群のまわりで顕著。
  Peterfalvi の Appendix C も Brauer–Suzuki の定理 (Ch. 12) で Gorenstein を参照する。
  こうした参照が Isaacs や mathlib で既にカバーされていない場合、Gorenstein の証明を
  ここに書き起こしてある (Theorems 3.4, 3.7/3.8/3.10, 4.15, 5.3.9–5.3.13, 7.6.5、
  `|S| ≥ 16` の場合の Brauer–Suzuki など。`OddOrder/BG/` と `OddOrder/GroupTheory/` 配下)。
  唯一残っている `Q₈` の場合の Brauer–Suzuki は Gorenstein 自体に無い: 同書 Ch. 12 は
  `|S| ≥ 16` だけを証明し、位数 8 の場合は証明抜きで述べるにとどまる
  (「知られている証明はすべてモジュラー指標の理論を要する」— 同書が展開しない理論である)。
  これを閉じるには、Navarro の *Characters and Blocks of Finite Groups* に沿って
  Z\*-定理までのモジュラー指標理論を構築する必要がある。これがライブラリに唯一残る `sorry` であり、
  進行中の長期プロジェクトである。Gorenstein を書物として形式化することは*しない*。

さらに 2 つの証明はこれらの書物の外から来ている: 書物は結果を述べるだけで証明は原論文から
取っているため、その原典自体をここで形式化した。

- **Higman**, "Suzuki 2-groups" (*Illinois Journal of Mathematics* 7, 1963)。Peterfalvi の
  Appendix III は Higman による Suzuki 2-群の分類を再掲するが、その証明は明示的に論文に委ねている。
  この証明は [`OddOrder/Higman/`](OddOrder/Higman/) 配下で完全に形式化されている —
  約 65,000 行の `sorry` 無しのコードで、ライブラリ中最大の単一項目である。
- **Huppert**, *Endliche Gruppen I* (1967), Kapitel II, Satz 3.2: 可解な 2-推移置換群は
  初等アーベルな正則正規部分群を持つ。Peterfalvi の Appendix C が必要とする。

3 冊のカバレッジは結果単位で追跡している。2026-07-16 の監査で全 **815 個の番号付き結果**を数え上げた:
467 が書籍の主張の強さのまま形式化済み、78 は mathlib 自体が完全にカバー、54 は特殊化された形で
存在し一般化待ち、214 が残作業。この調査
([`notes/meta/three_books_full_survey_2026_07_16.md`](notes/meta/three_books_full_survey_2026_07_16.md))
は第 2 フェーズ開始時点のスナップショットであり、生きたスコープ文書ではない — 後の抜き取り検査で
章ごとのラベルの一部に信頼できないものが見つかっている。現在のスコープと進捗は git 履歴と `issues/`
で追跡しており、各項目は着手前にツリーの実状態と突き合わせて再確認する。

すべては細切れに mathlib へ upstream せず `OddOrder` namespace 配下に置いているが、命名・スタイルは
一貫して mathlib の規約に従っており、汎用部分は後から upstream できる状態を保っている。ツリーは
mathlib 標準の linter セットの下で非 `sorry` 警告ゼロでビルドされ、CI の strict gate で強制されている。

## ビルド

```bash
lake exe cache get     # ビルド済み mathlib olean (初回 checkout 時と mathlib 更新後)
lake build OddOrder
```

Lean toolchain は [`lean-toolchain`](lean-toolchain) に、mathlib のリビジョンは
[`lakefile.toml`](lakefile.toml) に固定されている。フルビルドはおよそ 4,450 jobs。

## リポジトリ構成

| パス | 内容 |
|---|---|
| [`OddOrder/`](OddOrder/) | Lean ソース本体 (~1,050 ファイル)。`Isaacs/`, `BG/`, `Peterfalvi/` が 3 冊をミラーし、`Higman/` が Suzuki 2-群の論文、`GroupTheory/`, `Algebra/`, `Mathlib/` が汎用部分 |
| [`OddOrder/FeitThompson.lean`](OddOrder/FeitThompson.lean) | 主定理と最小反例への還元 |
| [`OddOrder/AxiomsCheck.lean`](OddOrder/AxiomsCheck.lean) | 主要な結果すべてのビルド時公理監査 |
| [`ROADMAP.md`](ROADMAP.md) | 長期計画、フェーズ、依存グラフ、章別チェックリスト |
| [`CLAUDE.md`](CLAUDE.md) | 作業規約とコントリビュータガイド (`AGENTS.md` はその symlink) |
| `notes/` | 章別ロードマップ、設計判断、原文調査 |
| `issues/` | ファイルベースの issue tracker (`issues/` = open, `pending/`, `closed/`) |
| `coq/` | Submodule: [math-comp/odd-order](https://github.com/math-comp/odd-order)、Coq/mathcomp による形式化 — **読み取り専用の参照**で、教科書が省く行間をコメントが埋めているために併読する。ここから翻訳はしていない |
| `references/` | 教科書 PDF と抽出テキスト — gitignore 対象で、別の private リポジトリに保管 |

## AI の利用について

このプロジェクトは AI エージェントによって駆動されている: Lean コード・ノート・ドキュメントの
ほぼすべてが AI によって書かれており、**そのすべてが人間のレビューを受けているわけではない**。
証明の正しさはそのレビューに依存しない: Lean カーネルがすべての証明を機械検証し、公理監査
([`OddOrder/AxiomsCheck.lean`](OddOrder/AxiomsCheck.lean)) が各結果の依存先を正確に特定する。読者の懐疑がなお正当なのは*ステートメント*について、すなわち
Lean の宣言がそれが参照する教科書の定理を忠実に写しているかどうかである。docstring に書籍の
定理番号を載せているのは、まさにこの対応を検証できるようにするためである。

## ライセンス

Apache License 2.0 — [LICENSE](LICENSE) を参照。
