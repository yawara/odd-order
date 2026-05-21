# Lean 形式化の知見集

**スコープ**: `odd-order` プロジェクトを進める中で蓄積する mathlib API の罠・
形式化ワークフロー上の教訓・詰まった証明パターンの記録。**成長する辞書**として運用。

**初版**: 2026-05-21 (Ch.1 Phase 1 着手セッション後)。

新しい知見が出たら **末尾に追記** + **発生日と章節を併記** (古さの判断材料)。
重複が増えたら同種項目を統合。**削除より追記+理由併記**を優先。

---

## 1. mathlib API 罠

### 1.1 名前空間 / スコープ

| 項目 | 詰まった点 | 解 | 出所 |
|---|---|---|---|
| `n !` (factorial) | scoped notation で `open scoped Nat` 必要 | 代替 `Nat.factorial n` を使うか, section 冒頭で `open scoped Nat` | 2026-05-21 §1A Cor 1.2 |
| Lucas の定理 | `namespace Choose` (top-level, not `Nat.Choose`) | `Choose.choose_pow_mul_pow_mul_modEq_choose_nat` で完全修飾 | 2026-05-21 §1B Lemma 1.8 |
| `Subgroup.index_ker` | `MonoidHom.index_ker` ではない | `Subgroup` namespace: 呼び出しは `Subgroup.index_ker f` または `f.ker.index_ker` (実際は `(H.comap f).index = H.index` 形, H 暗黙) | 2026-05-21 §1E Lemma 1.34 |
| `Group.IsNilpotent` | `IsNilpotent` (no Group prefix) は型クラス無し | `Mathlib.GroupTheory.Nilpotent` import で `Group.IsNilpotent` が見える | 2026-05-21 §1D Thm 1.26 |
| `Nat.Primes` | `def Primes := {p // p.Prime}` で subtype | `(p : Nat.Primes)` から `(p : ℕ)` へ coerce; 引数は素数のみに制限される | 2026-05-21 §1D fitting 定義 |

### 1.2 引数の型違い / coerce

- **`Subgroup.normalizer`** は **`Set G`** を取る (`Subgroup G` 直接は通らない).
  - 部分群を渡すなら `((H : Subgroup G) : Set G)` で coerce. 例: §1C `card_sylow_eq_index_normalizer`.
- **`Sylow.coe_subgroup_smul`**: `↑(g • P) = MulAut.conj g • (P : Subgroup G)` — Sylow 上の MulAction smul を Subgroup の pointwise smul に橋渡し.
  - これと **`Subgroup.mem_pointwise_smul_iff_inv_smul_mem`** (`x ∈ a • S ↔ a⁻¹ • x ∈ S`) と
    **`MulAut.apply_inv_self`** (`e (e⁻¹ m) = m`) の 3 つが **「共役下のメンバシップ」計算の標準チェーン**.
  - §1D `opCore.normal` で実例.
- **`IsPGroup p G`** 自体は `G : Type*` の型クラスではなく述語. 部分群への遺伝は
  `P.2.of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective _)` で取る (h : opCore ≤ P).

### 1.3 構文

- **`omit [Fact ...] in`** は **docstring の前**.
  - `/-- doc -/` の **後** に `omit ... in theorem ...` を置くと `unexpected token 'omit'; expected 'lemma'`.
  - 正解: `omit [Fact p.Prime] in /-- doc -/ theorem foo ...`.
  - §1C `pgroup_le_sylow`, `pgroup_in_normalizer_le_sylow` で実例.
- **`section /- 1A: ラベル (pp. 1-10) -/`** の `/- ... -/` は lexer 段階でコメントとして剥がされる. section は anonymous. CLAUDE.md 規約.
- **`refine Subgroup.iSup_induction _ ... (C := ...)`** — motive が推論できないとき `(C := fun x => ...)` で明示.
  - §1D `fitting.normal` で `(C := fun x => g * x * g⁻¹ ∈ fitting G)` 明示要.
- **`le_iSup`** の関数引数は `_` で済まないことがある.
  - 失敗例: `le_iSup _ p` が `?m.8 p ≤ iSup ?m.8` で type error.
  - 解: 明示する `le_iSup (fun q : Nat.Primes => opCore (q : ℕ) G) p`.

### 1.4 finite / Nat.card 周辺

- **Cauchy の定理**: 2 形式あり.
  - `exists_prime_orderOf_dvd_card` (Fintype G 版)
  - `exists_prime_orderOf_dvd_card'` (Finite G 版) — **通常こちらが使いやすい**
- **`Subgroup.index_ne_zero_iff_finite`**: `H.index ≠ 0 ↔ Finite (G ⧸ H)`.
  - `H.index` から `Finite (G ⧸ H)` instance を作るときに使える.
- **`Subgroup.Normal.eq_bot_or_eq_top`** `[IsSimpleGroup G]`: 単純群の正規部分群は `⊥` or `⊤`.
  - Cor 1.3 で `normalCore` の二択処理に直結.
- **`Nat.card_perm`** `[Finite α]`: `Nat.card (Equiv.Perm α) = (Nat.card α)!`.
  - これを使うには `Mathlib.Data.Finite.Perm` を **明示 import** 要 (Sylow 経由では入ってこない).

### 1.5 構造定理パターン

- **TFAE 抽出**: `theorem .. : List.TFAE [P₀, P₁, P₂, P₃, P₄] := ...` の個別 iff は `.out i j`.
  - 例: `isNilpotent_of_finite_tfae.out 0 3 : IsNilpotent G ↔ ∀ p [Fact p.Prime] (P : Sylow p G), (↑P).Normal`.
  - **TFAE は 1 つ書けば 5 条件の全 10 個の iff が得られる** — Isaacs Thm 1.26 のような複数条件等価定理は TFAE 形がベストプラクティス.
- **`Subgroup.iSup_induction`** には **`inv` ケース無し** — `mem`, `one`, `mul` の 3 つだけ (内部で `closure_induction''` を使い inv は自動).
- **`independent_of_coprime_order`** (`Mathlib.GroupTheory.NoncommPiCoprod`): 「互いに素な位数 + 可換性 ⇒ iSupIndep」. 正規部分群の場合は別途 `commute_of_normal_of_disjoint` で可換性を出す.

---

## 2. ワークフロー教訓

### 2.1 着手前の mathlib 偵察を必ずやる

実装計画を細かく書く前に **目的の lemma を Explore agent (read-only) で grep 列挙**.

2026-05-21 の実例: §1D Fitting の設計を 14 step で書いてから Agent C に偵察させたら,
`isNilpotent_of_finite_tfae` の発見で step 7, 8 が丸ごと不要化, `independent_of_coprime_order` で step 6 もラッパー化. 結果 14 → 9 step.

**判断基準**: 新規実装が 50 行を超えそうなら必ず偵察。50 行以下なら直接書いて構わない。

### 2.2 build green が gate

エージェントが "completed" を返しても build red の可能性あり (今日 Agent D の `← map_inv` 向き誤りが実例).
**毎 commit 前に `lake build OddOrder` で確認**. 1638 jobs で ~5 秒, ペナルティ小.

### 2.3 TODO は 3 行で書く

ただの `-- TODO` でなく:

```
-- TODO **Isaacs Thm 1.X**.  N の主張.
--   証明骨子: A → B → C (1 行で).
--   未解決の点: D (mathlib の E をまだ grep していない / F でスタック).
```

これがあると次回 fresh context で 30 秒で復帰できる. 詰まりかけで TODO 化する **判断は正しい** — 30 分以上格闘するより, unblock して進む方が全体最適.

### 2.4 3 層トレーサビリティが効く

CLAUDE.md 規約の以下の組:

1. ファイル冒頭 `/-! # ... -/` — 本のどの章節か, ページ範囲, 状態テーブル
2. `section /- 1A: ラベル (pp. 1-10) -/` — subsection 構造ミラー
3. `theorem` の docstring 冒頭 `**Isaacs Thm 1.4** (慣用名)` — 番号と慣用名

500 行を超えた `Ch01_Sylow.lean` でも `grep "Thm 1.18"` で 1 秒で navigate.
**新しい theorem を追加する時は必ずこの 3 層を埋めてから本体を書く**.

### 2.5 mathlib 互換命名

CLAUDE.md 規約: 識別子に **番号を入れない** (`thm_1_4` NG), 記述的命名 (`sylowExistence`, `fundamentalCountingEquiv`).
将来 mathlib に PR する余地を残す. 番号は **docstring 内のみ**.

### 2.6 ファイル粒度

Isaacs: 1 章 = 1 ファイル, 1500-2000 行で subsection 単位に分割.  
BG / Peterfalvi: 1 節 = 1 ファイル. **先回り分割しない** — 育つかどうかは事前に読めない.

---

## 3. 詰まった証明パターン (後で再着手用 backlog)

このセクションは「mathlib のこのへんに何かあるはずだが時間切れ」案件を残す.
再着手者 (将来の自分 or サブエージェント) が grep の出発点に使う.

### Cor 1.5 (共役類サイズ = `[G : C_G(x)]`)

`ConjClasses.card_carrier` から `|G|/|stabilizer|` までは出る. `(Subgroup.centralizer {x}).index` への書き換えに `ConjAct.toConjAct` の全単射性 + `Subgroup.centralizer_eq_comap_stabilizer` + `Subgroup.index_comap_of_surjective` の H 明示が必要. 一度通した版が pattern unify で不安定.

→ **再着手のヒント**: `index_comap_of_surjective` の H を `(H := MulAction.stabilizer ...)` で明示する形を試す.

### Cor 1.6 (部分群の共役の総数 = `[G : N_G(H)]`)

`ConjAct G` の `Subgroup G` への点別共役作用 (Pointwise locale) で軌道サイズ = stabilizer 指数. `Subgroup.index_map_equiv` の H 明示と `conjAct_pointwise_smul_iff` の組み合わせ要.

→ **再着手のヒント**: `open scoped Pointwise` をセクション冒頭でなく theorem 直前に置く形を試す.

### Isaacs Lemma 1.27 (互いに素な位数の正規部分群族の積は直積)

`Subgroup.independent_of_coprime_order` 直接は `Pairwise commute` 要求. 正規 + coprime cards → Disjoint → `commute_of_normal_of_disjoint` の中継補題が必要. `Disjoint H K` を coprime cards から出すには `orderOf` を経由した Lagrange 整除が必要.

→ **再着手のヒント**: 補助補題 `disjoint_of_coprime_card` を先に書く. mathlib `IsPGroup.le_or_disjoint_of_coprime` の一般化形.

### Thm 1.16 (`n_p ≡ 1 (mod |S : S∩T|)`)

S, T で `|S∩T|` 最大の場合の精密な mod 計算. S 上の共役作用で固定点を数える必要があり, mathlib 直対応無し. 40+ 行が見込まれるため TODO.

→ **再着手のヒント**: mathlib `Sylow.card_modEq_card_normalizer` 系を grep し, 抽象化された版が無いか確認.

---

## 関連ドキュメント

- [`CLAUDE.md`](../../CLAUDE.md) — プロジェクト規約 (ファイル粒度・トレーサビリティ・命名)
- [`ROADMAP.md`](../../ROADMAP.md) — Phase 計画 + 章節チェックリスト
- [`notes/meta/mathlib_coverage.md`](mathlib_coverage.md) — マクロレベルの mathlib 偵察 (「Sylow」「冪零」等の分野別)
- [`notes/meta/subagent_orchestration.md`](subagent_orchestration.md) — サブエージェント並列運用方針
- オートメモリ `feedback_lean_formalization_tips.md` — このファイルへのポインタ (自動ロード用)
