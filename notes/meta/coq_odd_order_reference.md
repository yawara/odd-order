# Coq 形式化 (math-comp/odd-order) の併読体制

`coq/` は [math-comp/odd-order](https://github.com/math-comp/odd-order) — Gonthier et al. による
Feit–Thompson 定理の **Coq/mathcomp 完全形式化** (CeCILL-B, 公開) を submodule として取り込んだもの。
pin = `master` の `6afa795b` (tag `mathcomp-odd-order.2.3.0` 系)。

## なぜ取り込むか — 行間補完の参照

各 `.v` ファイルの**コメントが教科書 (BG / Peterfalvi) の行間を埋めている**:

- ファイル冒頭の `(* This file covers B & G, section N ... *)` ヘッダで、その節が何を扱うか・どこを省くかを明示
- `Definition` / `Notation` に**意味付けのコメント** (例: BGsection10.v の `\alpha(M)` `\beta(M)` `\sigma(M)` の定義と、B&G が "ideal" prime と呼ぶ流儀への注記)
- 各補題に対応する**教科書番号・原文の言い回し**の注記、証明中の非自明ステップの一言メモ

これは「教科書が省略した行間」を一次的に再構成した資料として価値が高い。**原文 (`.mmd`/PDF) を読むタイミングで、対応する `.v` のコメントを併読する**のが取り込みの目的。

### スコープ (重要)

- 形式化対象は CLAUDE.md のとおり **3 冊 (Isaacs / BG / Peterfalvi) のまま**。Coq odd-order を独立に形式化対象にはしない。
- Coq は**行間補完・証明戦略のヒント・前提の所在確認の参照専用**。Lean へ直訳するソースではない (mathcomp の命名・convention・基盤は mathlib と別物)。教科書本文が一次ソースであることは変わらない。
- **Coq ツールチェインは不要**。`.v` を Read / grep するだけ (ビルドしない)。

## 取得 (fresh clone 時)

```bash
git submodule update --init coq          # coq/ だけ取得
# もしくは clone 時に
git clone --recurse-submodules <main>
```

## 教科書 ↔ `.v` ファイル 1:1 対応 (`coq/theories/`)

ファイル名が教科書構成と一致する。各 `.v` 冒頭コメントの "covers" 記述を併記:

| 教科書 | Coq ファイル | 冒頭コメントの要旨 |
|---|---|---|
| BG §1 | `BGsection1.v` | most of the material in B & G, section 1 |
| BG §2 | `BGsection2.v` | the useful material in B & G, Section 2 |
| BG §3 | `BGsection3.v` | the material in B & G, Section 3 (rep-theory keystone 群) |
| BG §4 | `BGsection4.v` | proof of structure theorems |
| BG §5 | `BGsection5.v` | Section 5 (一部の technical results を除く; narrow の定義) |
| BG §6 | `BGsection6.v` | most of B & G section 6 |
| BG §7 | `BGsection7.v` | proof of the Thompson Transitivity Theorem + 後で使う一般化 |
| BG §8 | `BGsection8.v` | two special cases |
| BG §9 | `BGsection9.v` | the Uniqueness ... |
| BG §10 | `BGsection10.v` | α(M)/β(M)/σ(M) と α/β/σ-core の定義 |
| BG §11 | `BGsection11.v` | one definition |
| BG §12 | `BGsection12.v` | M_σ の補元の prime set 定義 (τ1(M) 等) |
| BG §13 | `BGsection13.v` | section 13 |
| BG §14 | `BGsection14.v` | σ-decomposition / σ-supergroup / maximal subgroup の基本カテゴリ定義から |
| BG §15 | `BGsection15.v` | §14 の概観を補完; M_σ の intrinsic characterization + TI 性 |
| BG §16 | `BGsection16.v` | section 16 の結果を総括 (summarises all results) |
| BG Appendix A, B | `BGappendixAB.v` | useful material in appendices A and B |
| BG Appendix C | `BGappendixC.v` | (appendix C; prose ヘッダ無し・コメント少) |
| Peterfalvi §1 | `PFsection1.v` | Preliminary results |
| Peterfalvi §2 | `PFsection2.v` | the Dade isometry |
| Peterfalvi §3 | `PFsection3.v` | TI-Subsets with Cyclic Normalizers |
| Peterfalvi §4 | `PFsection4.v` | The Dade isometry of a certain ... |
| Peterfalvi §5 | `PFsection5.v` | Coherence |
| Peterfalvi §6 | `PFsection6.v` | Some Coherence Theorems |
| Peterfalvi §7 | `PFsection7.v` | Non-existence of a Certain Type of Group of Odd Order |
| Peterfalvi §8 | `PFsection8.v` | Structure of a Minimal Simple ... |
| Peterfalvi §9 | `PFsection9.v` | maximal subgroups of Types ... |
| Peterfalvi §10 | `PFsection10.v` | Maximal subgroups of Types III, IV, V |
| Peterfalvi §11 | `PFsection11.v` | Maximal subgroups of Types ... |
| Peterfalvi §12 | `PFsection12.v` | (§12; prose ヘッダ無し) |
| Peterfalvi §13 | `PFsection13.v` | The Subgroups S and T |
| Peterfalvi §14 | `PFsection14.v` | Non-existence of G (最終矛盾) |
| Wielandt fixed-point 公式 (BG §9 周辺) | `wielandt_fixpoint.v` | the Wielandt fixpoint order formula |
| FT 最終ステートメント | `stripped_odd_order_theorem.v` | minimal, self-contained reformulation of the Odd Order theorem |

> **Isaacs (有限群論の前提) はこの odd-order リポに無い** — Sylow / Hall / Frobenius / 指標など Isaacs 相当は
> mathcomp 本体側 ([math-comp/math-comp](https://github.com/math-comp/math-comp) の `fingroup` / `solvable` / `character`) にある。
> Isaacs 相当を Coq で照合したいときは別途 math-comp 本体を参照 (本リポには取り込んでいない)。

## 併読レシピ

例: BG §10 の Lemma 10.x を Lean で書いていて、原文の行間が知りたいとき —

```bash
# 1. ファイル全体の構造とコメントを把握
#    Read coq/theories/BGsection10.v  (冒頭ヘッダ + 定義群を通読)

# 2. 特定の補題・記法をピンポイントで
grep -n "10\.\|sigma\|narrow" coq/theories/BGsection10.v        # 教科書番号や記法で
grep -n "Lemma\|Theorem\|Definition" coq/theories/BGsection10.v # 宣言一覧から当たりを付ける
```

- mathcomp の補題名 (例 `Msigma_...`, `sigma_...`) と教科書番号は**コメント側に対応が書いてある**ことが多い。名前から逆引きするより、まずコメントを読む。
- Lean 側の lane (BG §N / PF §N) が詰まったら、まず同じ N の `.v` のコメントで「原文がどの補題に依拠して行間を飛ばしているか」を確認する。`notes/` の lane ノートにその所在をメモして残す。

## pin 更新

```bash
git -C coq fetch origin master
git -C coq checkout <new-sha>        # もしくは git -C coq pull origin master
git add coq && git commit            # main 側で submodule ポインタを更新
```

通常は pin を固定したまま (FT の数学は安定) でよい。mathcomp 側の大きな再編で参照が古くなったら更新する。

## ライセンス

math-comp/odd-order は **CeCILL-B** (BSD 系の帰属ライセンス)。submodule はポインタのみで本リポにソースを vendoring しないので、本リポのライセンス (`LICENSE`) とは独立。`.v` のコメントを Lean の docstring 等へ流用する場合は帰属に注意。
