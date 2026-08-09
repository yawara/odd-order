---
id: 180
slug: bg-appc-problem1-p-eq-three
title: "BG App.C Problem 1: Theorem C で p = 3 はありうるか (未解決問題)"
created: 2026-08-09
---

# BG App.C Problem 1 — 未解決問題

3 冊逐条監査 (775 件、issue 0172/0176/0177) と [Remark (IV) の形式化](closed/0179-bg-appc-remark-iv-glauberman-norton.md)
が完了した後に残る**最後の項目**。⚠ **これは形式化の残債ではなく、1993 年以来の未解決問題**。

## 問題

**BG p.152 / Glauberman–Norton p.1094 "Problem (Péterfalvi)"**:

> Can the hypothesis of Proposition 9 be satisfied for `p = 3`?

Proposition 9 の仮説 (記法は
[`references/glauberman-norton/SOURCE.md`](../references/glauberman-norton/SOURCE.md) と
[`OddOrder/BG/AppC_GlaubermanNorton.lean`](../OddOrder/BG/AppC_GlaubermanNorton.lean) を参照):

* (A) `q ∤ p − 1`
* (B) 単射準同型 `σ : H → G` (`H = P ⋊ U`)、**有限可換 `p′`-部分群** `Q ≤ G`、`y ∈ Q` が存在して
  `σ(P₀)` が `Q` を正規化し、`σ(P₀)^y` が `σ(U)` を正規化する

⚠ **`G` の有限性は要求されていない** (有限性が課されているのは `Q` だけ)。字義どおり読むと
有限アマルガムの完備化による構成の余地がある。

## 状態 (2026-08-09)

**未解決。** 形式化のターゲットではなく、数学として未決着。

* `p = 2` は実現する (Example 10 = `SL(2,2^q)`、Example 11 = `Sz(2^q)`)。
* `p ≤ 3` は Glauberman–Norton の Prop 7 から従う ([0179](closed/0179-bg-appc-remark-iv-glauberman-norton.md) で形式化済)。
* **`p = 3` は組合せ的には何の障害も無い** — 標数 3 では `E = E⁻¹` が自動
  (`NormSet.normSetE_eq_inv_of_p_eq_three`、Lean 検証済・AxiomsCheck 登録済)。
  ⟹ 問題は**純粋に (B) の実現可能性**。

### 文献調査 (2026-08-09 実測)

| データベース | Glauberman–Norton 1993 の被引用数 |
|---|---|
| OpenAlex (`W2059497267`) | **0** |
| Semantic Scholar | **0** |

⟹ 1993 年以降この問題に触れた公刊物は無さそう (MathSciNet は未確認)。

## こちらで確立した還元 (2026-08-09)

`x` = `σ(P₀)` の生成元 (位数 3) とする。

1. **`y` は `x` を中心化できない。** `H = P ⋊ U` は Frobenius 群なので `N_H(U) = U`。
   `x ∈ σ(P) ∖ {1}` だから `x` 自身は `σ(U)` を正規化しない。`xσ(U)x⁻¹` は `H` の中で決まる条件なので
   `G` を大きくしても変わらない。⟹ `y ∈ C_Q(x)` なら `σ(P₀)^y = σ(P₀)` で条件が破れる。
2. **`Q` は `[Q,x]` に取り替えてよい。** `Q` は 3′-群なので互いに素な作用で `Q = C_Q(x) × [Q,x]`。
   `y = y₁y₂` (`y₁ ∈ C_Q(x)`, `y₂ ∈ [Q,x]`) と分解すると `x^y = x^{y₂}` なので `y₂` で置き換えられる。
   置換後は `C_Q(x) = 1`、すなわち `K := Q ⋊ ⟨x⟩` は核 `Q`・補群 `C₃` の**有限 Frobenius 群**。
3. **条件は次に帰着する**: `K` の位数 3 の元 `g ∈ xQ` (`g = x·[x,y]`) であって、`G` の中で `σ(U)` を
   正規化するものが存在するか。つまり `G ⊇ H` と `G ⊇ K` を `⟨x⟩` で貼り合わせ、さらに
   `⟨σ(U), g⟩` が群をなすという**横断条件**を満たす完備化が存在するか (= 群の三角形の完備化問題)。
4. **`|Aut U|` が 3 で割れないとき** (書籍の注、例 `q = 5` で `|U| = (3⁵−1)/2 = 11²`)、`g` は `σ(U)` を
   中心化するので `⟨σ(U), g⟩ = σ(U) × ⟨g⟩`。一方 `H` 内では `C_H(U) = U` なので **`g ∉ σ(H)`** が強制される。

⚠ いずれも紙の上の議論で、まだ Lean 化していない。

## ChatGPT (GPT-5.6 Sol / 推論レベル Pro) への相談 (2026-08-09)

ユーザー指示で投入。**完走せず** (1 回目は約 2.5 時間で network error、再試行は 4 時間以上走って未完了)。
運用上の教訓は [`notes/meta/chatgpt_consult_via_chrome.md`](../notes/meta/chatgpt_consult_via_chrome.md)
2026-08-09 節に記録済。

進捗表示から回収できた**未検証**の中間主張 (再開するならここから):

* こちらの問題文の読みは正確、標数 3 の議論は原論文 Lemma 4(b) そのもの、後続文献に解決主張なし
  (いずれもこちらの独立調査と一致)
* 核心は **`⟨x, x^y⟩` が abelian-by-`C₃`** という還元 — こちらで検証済・正しい
  (`⟨x,x^y⟩ ≤ Q⋊⟨x⟩` で `⟨x,x^y⟩ ∩ Q` は可換、商は `C₃`)
* `Q = ⟨y, y^x⟩` に圧縮して `C_Q(x) = 1`、**`Q ∩ H = 1`** — ⚠ 後者は根拠未確認
  (`Q ∩ σ(P) = 1` は 3′ から出るが、`Q ∩ σ(U) = 1` の理由が要る)
* 最小位数の**有限**例は一意な非可換極小正規部分群をもち `Aut` へ忠実に埋め込まれる
  ⟹ 可解群と `P ◁ G` 型のアフィン構成は排除される — ⚠ 未検証
* `q = 3` (`F = GF(27)`, `|U| = 13`) で `³D₄(3)` による候補を検証 — ⚠ 結論不明

## 次にやるとしたら

* 上記 1–4 の還元を Lean 化する (未解決問題そのものでなく、**還元は確定した数学**なので形式化可能)。
* `q = 3` の有限の場合を計算機で潰す (`K = Q⋊C₃` と `H = P⋊U` の融合の探索)。
* ChatGPT に投げ直すなら**問題を絞る** (「`q = 3` に限定して (B) の実現可能性を判定せよ」)。
  未解決問題をそのまま投げると発散して完走しない。

## 参照

- 原論文: [`references/glauberman-norton/`](../references/glauberman-norton/) (p.1094 が Prop 9 と Problem)
- BG: `references/bg/local-analysis.pdf` (Problem 1 = p.152、Remark (IV) = p.148)
- 形式化済の周辺: [issue 0179](closed/0179-bg-appc-remark-iv-glauberman-norton.md)
