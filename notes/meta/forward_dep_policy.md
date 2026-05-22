# Forward dependency policy

**確定**: 2026-05-22

## 背景

Isaacs FGT には **書籍内の章順と論理依存順序のズレ** が組み込まれている. 例えば
Ch.2 Thm 2.20 (Lucchini) の証明 (K = ⊥ case) は Ch.4 §4A-§4B (lower central series 加法性)
の補題を要する. このような「逆方向 (前章 → 後章)」の依存を Lean 上でどう扱うかを定める.

## 大原則

- **Lean import グラフは DAG** (循環禁止).
- **書籍の章 = 1 ファイル or 1 ディレクトリ** (CLAUDE.md の規約は維持).
- **forward dep は owner chapter (依存先の章) に置く** (本ノートで規定).

## 用語

- **owner chapter**: 依存先の章 (= 補題が論理的に属する章).
  例: 「Ch.2 Thm 2.20 は Ch.4 lcs を要する」の場合, owner chapter は Ch.4.
- **forward dep**: owner chapter > 使用元の章 となる依存.
  Lean import 順では owner chapter が後ろにビルドされる.
- **leaf axiom**: 使用箇所が 0 件の axiom (declaration のみで本体無し).

## ファイル構造ルール

### ルール 1: forward dep は owner chapter ディレクトリへ

`OddOrder/Isaacs/ChXX_<Topic>/` ディレクトリを作り, 以下のサブファイルに分割:

```
OddOrder/Isaacs/ChXX_<Topic>/
├── Main.lean (or ChXX 本体ファイル)
│       本来 ChXX で書かれる内容. 書籍順で読まれる主軸.
└── ForwardFromChYY.lean (各 YY < XX について必要なら)
        Ch.YY が ChXX 領域の補題を要請するファイル. ChYY からは
        このファイルを import する.
```

例:
- `Ch04_Commutators/ForwardFromCh02.lean`: Ch.2 Lucchini Thm 2.20 (Ch.4 lcs 依存)
- `Ch04_Commutators/ForwardFromCh03.lean`: Ch.3 §3E IsAInvariant 系 (Ch.4 coprime action 依存)
- `Ch06_FrobeniusActions/ForwardFromCh03.lean`: Ch.3 Hall-Higman 1.2.3 (Ch.6 P×Q 依存)
- `Ch07_Burnside/ForwardFromCh03.lean`: Ch.3 Thm 3.15, 3.17 (Ch.7 Burnside 依存)

### ルール 2: 「ファイル + コメントだけ」状態

owner chapter ディレクトリのファイルは, 着手前は **コメントのみ + 必要なら axiom** の状態:

- **leaf axiom (使用箇所 0 件)**: axiom すら書かず, ファイル冒頭の docstring に
  「将来この場所に Thm X.Y が来ること」を明記.
- **使用中 axiom**: 暫定 axiom として記載. owner chapter 完成時に theorem 化.
  ファイル冒頭の docstring に「暫定 axiom. 解消条件は ChXX §XY 完成」を明記.

### ルール 3: 使用元 chapter (ChYY) からの呼出

ChYY の本体ファイルで forward dep を使う場合, **owner chapter から import**:

```lean
-- ChYY_<Topic>.lean
import OddOrder.Isaacs.ChXX_<Topic>.ForwardFromChYY

-- 以下で forward dep の定理を呼べる
```

ChYY 自体には axiom を残さない. (現状の Ch.2 内 `lucchini_K_bot_aux` 等が
owner chapter ディレクトリへ移動する.)

### ルール 4: 「結合定理」の置き場

forward dep を使った主定理 (例: Lucchini 全体) は **owner chapter ディレクトリ** に
置く. これは書籍では使用元 chapter (Ch.2) で stated されるが,
Lean 上は依存先 chapter で実装する.

例外: ChYY の structural 部分のみ ChYY に残せる場合は残す.
例: Lucchini の K > ⊥ inductive reduction は subgroup correspondence のみ使うので
Ch.2 内 `lucchini_K_pos_reduction` として残し, 全体 `lucchini_index_normalCore_lt_index`
は `Ch04_Commutators/ForwardFromCh02.lean` に置く.

### ルール 5: mathlib への forward dep

mathlib に存在しない補題 (例: Schur-Zassenhaus 共役性) は **owner chapter とは別扱い**:

- 補題の論理的所属が **mathlib 範疇** (汎用) なら, `OddOrder/Mathlib/<Topic>.lean` 等の
  抽出先を作って後でその場所で実装. 使用元 chapter は import.
- 補題の論理的所属が **特定の Isaacs 章** なら owner chapter ディレクトリへ.

(現在: hall_C_conjugate は mathlib に SZ 共役性が無いことが障害. 暫定 axiom として
Ch.3 内に維持 or `Ch03_SplitExtensions/SZConjPending.lean` 等のサブファイル化.
本リポでは現状 **leaf axiom 削除** で対応, 将来再実装時に判断.)

## ファイル命名規約

- 既存 1 ファイル (`ChXX_<Topic>.lean`) → ディレクトリ化する場合は `ChXX_<Topic>/Main.lean` を
  作って中身を移し, ChXX_<Topic>.lean は薄い import 集約 (or 削除).
- `ChXX_<Topic>/ForwardFromChYY.lean`: 1 ChYY あたり 1 ファイル.
- `ChXX_<Topic>/Helpers/<Subtopic>.lean`: chapter 内の補助補題 (forward dep ではない).

## namespace 規約

- `Ch04_Commutators/ForwardFromCh02.lean` の中身は **`OddOrder.Isaacs.Ch04` namespace**
  (物理的所在で決まる; 書籍上 Ch.2 でも Lean では Ch.4 にいる).
- docstring に「**Isaacs Thm 2.20 (Lucchini)**」と書籍番号は明記.

## notes 規約

各章の `notes/isaacs/chXX_<topic>.md` に「逆引き: 他章から要求される補題」セクションを
持たせる (`ch04_commutators.md` で既に実施済). owner chapter ノートで forward dep を一覧化.

## leaf axiom 削除ガイドライン

axiom が **使用箇所 0 件** なら, 単に削除して owner chapter ディレクトリに
**空ファイル + docstring** を作る. notes に「将来この場所に Thm X.Y が来る」と書く.

```lean
-- 例: OddOrder/Isaacs/Ch07_Burnside/ForwardFromCh03.lean
/-!
# Ch.7 → Ch.3 forward dependencies

このファイルには **Isaacs FGT Ch.3 の以下の定理** が Ch.7 完成後に実装される:

- **Thm 3.15** `solvable_of_pcomplement_exists`: ∀ p, p-complement 存在 ⇒ G solvable.
  証明骨子: |G|-induction + Burnside `p^a q^b` 経由.
- **Thm 3.17** `solvable_of_three_subgroups` (Wielandt): 3 部分群 pairwise coprime
  + solvable ⇒ G solvable. 証明骨子: 単純群場合分けで Burnside 必要.

実装は Phase 4 (Ch.4-Ch.7 全完成後) に着手. それまでこのファイルは意図的に空.
詳細は [`notes/isaacs/ch07_burnside.md`](../../../../notes/isaacs/ch07_burnside.md).
-/

namespace OddOrder.Isaacs.Ch07
-- 意図的に空. 上記コメント参照.
end OddOrder.Isaacs.Ch07
```

## 適用優先度

1. **lucchini_K_bot_aux** (Ch.2 → Ch.4): Ch.4 dir 作成 + 移動 + Ch.2 reduction lemma 抽出.
2. **leaf axiom 7 個** (Ch.3 → 各章): owner chapter dir + 空ファイル + 削除.
3. **将来追加される forward dep**: 本ノートのルールに従って配置.

## 関連ノート

- [`notes/isaacs/ch04_commutators.md`](../isaacs/ch04_commutators.md): 「逆引き」セクション.
- [`CLAUDE.md`](../../CLAUDE.md): 1 章 = 1 ファイル規約 (本ノートで部分的に緩和).
