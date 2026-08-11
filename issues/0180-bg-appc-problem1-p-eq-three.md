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

## ▶ 再開手順 (2026-08-11 時点)

1. ~~次の Lean 作業 = トレース障害の形式化~~ → **2026-08-11 完了**。leaf =
   [`OddOrder/BG/AppC_Problem1Trace.lean`](../OddOrder/BG/AppC_Problem1Trace.lean)
   (330 行、axiom-clean)。判定法の仮説が `AddSubgroup.closure (collisionSet …) = ⊤` から
   **「衝突 1 個で `Tr S ≠ 0`」** (`false_of_collisionPair_trace_ne_zero`) に弱まり、さらに
   指数の非 Frobenius 性 `hnotfrob` も**不要**になった (矛盾が `N` の完全性を経由せず
   定理 1 の終局 `not_commute_conj` に直接落ちるため)。
2. **走らせている計算**: `notes/meta/gap/verify_trace_obstruction.g` (q=7,13,19,29 の独立検証。
   q=7,13,19 は決着済 — 衝突 1〜5 個で `Tr S ≠ 0`) と `q = 31` のトレース判定
   (scratchpad の派生スクリプト、6000 万サンプル)。
3. **一般 `q` は依然 open**。示すべきことは 2 段階に弱まった:
   **(B1)** 衝突が 1 つ存在する (= `A_E = {(u,u^E)}` が Sidon でない ⟸ `z ↦ z^E` の擬ランダム性。
   これが本丸、ChatGPT も未証明) / **(B2)** その `S` が `Tr S ≠ 0`。
   ⚠ **(B2) も未証明** — 実測では常に数個以内の衝突で当たる (13 ケースで平均 1.8 個) が、
   それはヒューリスティックであって定理ではない。構造的には
   「`span{S} ⊆ ker Tr` (= 唯一の Frobenius 安定な超平面) が起きない」という主張で、
   旧判定 (`span{S} = F`) より真に弱いだけ。各 `q` の証明書では直接確認するのでギャップにならない。

## 状態 (2026-08-11 更新) — **q ≤ 29 決着**、判定法は Lean 化済

2026-08-11 に **collision-span 障害** (ChatGPT Work 5.6 Sol ウルトラ由来、こちらで全ステップ検証 +
独立計算再現) が入り、**最小の未決ケース `q = 13` が落ちた**。詳細 =
[`notes/bg/appC_problem1_partial_resolution.md`](../notes/bg/appC_problem1_partial_resolution.md)
「q = 13 決着」節。

判定法 (一般・証明済): `T = {p ∈ U : p−1 ∈ U}`、`D(p) = p^E − (p−1)^E`、
`K(p) = (p−1)^{E²} − p^{E²}` として、**衝突** `D(p) = D(r)` で `δ = r^E − p^E ∈ U` なるものから
`S(p,r) = K(p)·δ^{−E}` を作る。**`S` たちが `F` を張れば witness は存在しない**
(∵ `b(S)^{a(−1)} ∈ B` ⟹ `a(−1) ∈ N_G(B)` ⟹ `U`-共役で `A ≤ N_G(B)` ⟹ `N = AB` は有限 3-群 =
冪零 ⟹ 完全な `N` は自明、定理 2 に矛盾)。`G` の有限性は不要。

| `q` | 状態 |
|---|---|
| 3, 5, 11, 17, 23, 37, 43, … (`3 ∤ φ(n)`) | ✅ 定理 1 |
| 7 | ✅ 合同枚挙 + collision-span (rank 7/7) |
| **13, 19, 29** | ✅ **collision-span (rank 満杯、独立再現済)** |
| 31 以降 | 🟡 可解/有限奇位数は不可 (定理 2)。exotic 指数ごとに collision-span を測れば個別決着 (`q=31` は射程内、`q=41` 以降は要高速化) |

⟹ **`q ≤ 29` の全奇素数で hypothesis (B) は不可能**。

**残る一般化 (priority A)**: 「すべての exotic `E` で `S_E(p,r)` が `F` を張る」を証明する。

### Lean 形式化 (2026-08-11 完了)

collision-span 判定法は**群論側・体側とも丸ごと形式化済** (axiom-clean、full build green)。
capstone = `Problem1.false_of_collisionSet_spanning`:

> `collisionSet p q e` (= 衝突かつ `δ` 平方元から作る `S` たちの集合、**`data` に依存しない
> 純粋な体の集合**) が `(𝔽_{3^q}, +)` を生成すれば hypothesis (B) に witness は存在しない。

内訳 = `layered_relation_field` → `layerFieldHom_two_eq` (1) → `layerFieldHom_two_factor` (2)
→ `layerFieldHom_one_conj` (3) → `conj_layerFieldHom_one_mem` (4) → capstone、
群論側は `U_le_normalizer_layerOne` / `false_of_s_normalizes_layerOne` /
`false_of_normalizes_layerOne`。

⚠ 各 `q` の証明書 (rank の計算) は `GaloisField` が計算可能でないため Lean 内では回せない。
**判定法が機械検証済みの定理、`q` ごとの証明書は外部計算 (GAP)** という切り分け。

**強化: トレース障害** ([`AppC_Problem1Trace.lean`](../OddOrder/BG/AppC_Problem1Trace.lean)、
2026-08-11)。capstone = `Problem1.false_of_collisionPair_trace_ne_zero`:

> 衝突が**ひとつ**あって、その `S` が `Tr S = ∑_{j<q} S^{3^j} ≠ 0` を満たせば witness は存在しない。

機構 = `S` の Frobenius 閉性 `S(p³,r³) = S(p,r)³` (`CollisionPair.frobenius`; 標数 3 で
`p³−1 = (p−1)³`) で関係式 (4) を `q` 本作り、可換な第 2 層で掛け合わせて
`x·b(Tr S)·x⁻¹ = b(Tr S')` (`conj_layerFieldHom_one_trace`)。両トレースは素体に落ちる
(`fieldTrace_pow_char`) ので双方 `⟨x^g⟩ ≅ C₃` に属し、`Aut(C₃) ≅ C₂` に位数 3 の元は無い
(`eq_one_of_conj_eq_inv`) ⟹ `x` が `x^g` を中心化 ⟹ `not_commute_conj`。
旧判定より仮説が真に弱く、**`hnotfrob` (指数の非 Frobenius 性) も不要**。
証明書コストも桁で下がる (`q = 19` で衝突 1〜3 個 / サンプル 5k〜43k、旧 span は数百万)。

## 状態 (2026-08-10 更新) — 大幅に前進、ただし全面解決ではない

**部分解決。** 2026-08-10 に以下が確定した (詳細 =
[`notes/bg/appC_problem1_partial_resolution.md`](../notes/bg/appC_problem1_partial_resolution.md))。

`g` = `σ(P₀)^y` の生成元が `σ(U)` に誘導する指数を `e` (`e³ ≡ 1 mod n`, `n = (3^q−1)/2`) とする。
`⟨3⟩ ≤ (Z/n)^×` は位数 `q` なので、**位数 3 の `e` が Frobenius 冪になるのは `q = 3` だけ**。

| 場合 | 状態 | 根拠 |
|---|---|---|
| **`e ∈ ⟨3⟩`** (`e = 1` は全 `q`、`e ≠ 1` は `q = 3` のみ) | ✅ **どんな `G` でも不可能** | **定理 1** = 人手証明 (計算機不要) |
| ⟹ **`q = 3`** (`e = 1, 3, 9` 全部) | ✅ **完全決着** | 定理 1 (+ 合同枚挙でも独立確認) |
| ⟹ `3 ∤ φ(n)` なる `q` (= 5, 11, 17, 23, 37, 43, …) | ✅ **完全決着** | 定理 1 の系 (書籍 p.1094 の注) |
| **`e ∉ ⟨3⟩`** (`q ≥ 7` で `3 \| φ(n)`) | 🟡 **`G` は可解でない。有限奇位数群は不可** | **定理 2 + 補題 D** (全 `q` で証明済) |
| `q = 7`, `e = 151, 941` | ✅ **完全決着** | 定理 2 + `[Γ_e : H] = 3` の実測 |

**主定理: 全ての奇素数 `q` について、(B) を満たす `G` は非自明な完全部分群を含む。
特に可解群は witness になれず、奇数位数定理より有限奇位数群も witness になれない。**
BG App.C が置かれている文脈そのものでは否定的に決着した。
残るのは「`q ≥ 13` で `e ∉ ⟨3⟩`、`G` は非可解 (無限でもよい)」だけ。

* `p = 2` は実現する (Example 10 = `SL(2,2^q)`、Example 11 = `Sz(2^q)`)。
* `p ≤ 3` は Glauberman–Norton の Prop 7 から従う ([0179](closed/0179-bg-appc-remark-iv-glauberman-norton.md) で形式化済)。
* **`p = 3` は組合せ的には何の障害も無い** — 標数 3 では `E = E⁻¹` が自動
  (`NormSet.normSetE_eq_inv_of_p_eq_three`、Lean 検証済・AxiomsCheck 登録済)。
  ⟹ 問題は**純粋に (B) の実現可能性**。

### 決め手になった着想 (ChatGPT Work 由来、こちらで検証・分解)

有限群 `D = ⟨x,g⟩` を枚挙するのは**無駄だった**。`c := x^{-1}g = [x,y] ∈ Q` を新しい生成元と見て、
`Q` が可換であること (`[c, c^x] = 1`) と `g³ = 1` だけを課した**万能完備化**

```
Γ_e = ⟨ H, z | [z, z^x] = 1, (xz)³ = 1, (xz)u(xz)^{-1} = u^e ⟩
```

を考えると、任意の witness はその商 (`z ↦ c`)。ゆえに `Γ_e` で `z³ = 1` が言えれば
`c³ = 1` かつ `c ∈ Q` (3′) から `c = 1`、`g = x` となって矛盾する。
**`G` の有限性はどこにも使わない。**

さらにこちらで `[x^{-1}g, (x^{-1}g)^x] = (gx)³` (語の恒等式、`x³ = g³ = 1` の下で) に気づき、
`Γ_e` を経由せず **`G` の中だけで完結する証明**に分解できた。`(gx)³ = 1` を `σ(U)` で共役すると

```
R(s):   (s^{e²})^{g²} · (s^e)^g · s = 1        (s ∈ S = 平方元全体)
```

が出る。ここで **`e` が Frobenius 冪かどうか**が分かれ目:

* `e = 3^j` なら `s ↦ s^e` は加法的 ⟹ 3 本の `R(s), R(t), R(s+t)` を消去して `[t, (s^e)^g] = 1`。
  `T = { s : s, s+1 ともに平方 }` が `F` を張る (`|T| = (3^q−3)/4`, Weil) ので `[x, x^g] = 1`、
  よって `c³ = 1` ⟹ `c = 1` ⟹ `g = x` で矛盾 (**定理 1**)。
* `e ∉ ⟨3⟩` なら加法性が壊れる。代わりに関係格子
  `L_e = span{ (s, s^e, s^{e²}) : s ∈ S } ≤ V³` を見ると **`L_e = V³` ⟺ `e ∉ ⟨3⟩`**
  (**補題 D**: `f(a) = Tr(λa + μa^e + νa^{e²})` の簡約多項式の指数集合が `⟨3⟩ ≤ (Z/(3^q−1))^×`
  の 3 つの剰余類 `A, eA, e²A` に分かれ、`e ∉ ⟨3⟩` なら互いに素ゆえ全係数が消える)。すると
  `N = ⟨σ(P), σ(P)^g, σ(P)^{g²}⟩` のアーベル化が消え、**`N` は非自明な完全群**になる
  ⟹ `G` は非可解 (**定理 2**)。`e = 3^j` のときは `dim L_e = q` にしかならないので、
  2 つの定理はちょうど相補的。

### 文献調査 (2026-08-09 実測)

| データベース | Glauberman–Norton 1993 の被引用数 |
|---|---|
| OpenAlex (`W2059497267`) | **0** |
| Semantic Scholar | **0** |

⟹ 1993 年以降この問題に触れた公刊物は無さそう (MathSciNet は未確認)。

## こちらで確立した還元 (2026-08-09)

⚠ **下記 3 (有限 `D` への還元) と「計算機探索」節の `D` 枚挙は 2026-08-10 に不要になった**
(上記の万能完備化が真に強い)。1・2・4 は今も有効で、実際 2 は使っていないが 1・4 は使う。
記録として残す。

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

## ChatGPT Work 3 回目 — 残る 1 ケース専用 (2026-08-10 夜、ユーザー指示)

定理 1・定理 2 の形式化完了後、**残った 1 ケースだけ**に絞って再投入した。

* サーフェス = `Work`、モデル `GPT-5.6 Sol`、**思考レベル `ウルトラ`** (バッジで目視確認)
* プロンプト全文 = [`notes/bg/appC_problem1_chatgpt_prompt_open_case.md`](../notes/bg/appC_problem1_chatgpt_prompt_open_case.md) (9,596 字)
* スレッド = `https://chatgpt.com/c/WEB:b1cd2e72-e66d-463a-bc70-f57294162e0d`
* 渡した検証済入力: (1)–(11) = `c ∈ Q` / 語の恒等式 / 指数 `e` / 関係式族 `R(v)` /
  **定理 1** / **定理 2** / **`N = ⟨P, P^g⟩` (2 層で足りる)** / `D = ⟨x,g⟩` は有限メタアーベル /
  `q = 7` の合同枚挙 / 小さい `q` の否定チェック / Gersten–Stallings が効かないこと
* 訊いたこと: (A) 残りケースの決着 (否定証明 or witness 構成)、(B) 無理なら `q = 13` を
  決定的に、(C) `q = 7` の崩壊の一般機構 (2 つの初等アーベル 3-群が生成する完全群 +
  f.p.f. トーラス + 位数 3 の巡回自己同型は標数 3 で存在しうるか)
* **⚠ p = 2 の witness `SL(2,2^q) = ⟨U, U⁻⟩` がまさに「2 つの可換部分群が生成する完全群」**
  なので、定理 2 + 2 層だけでは矛盾にならない旨も明記した

## ChatGPT Work (GPT-5.6 Sol / 思考レベル ウルトラ) への再投入 (2026-08-10)

ユーザー指示で、従来の `Chat` でなく **`Work` サーフェス**に投入 (モデル `GPT-5.6 Sol`、
**思考レベル `ウルトラ`**)。UI 手順は [`notes/meta/chatgpt_consult_via_chrome.md`](../notes/meta/chatgpt_consult_via_chrome.md)
2026-08-10 節。

* プロンプト全文 = [`notes/bg/appC_problem1_chatgpt_prompt.md`](../notes/bg/appC_problem1_chatgpt_prompt.md) (10,728 字)
* スレッド = `https://chatgpt.com/c/6a7935bc-0d48-83ee-9d4c-202c494dcb38`
* 1 回目 (2026-08-09) の反省を反映: **問題を絞り**、上記の還元 R1–R4 と GAP 結果を検証済み入力として
  与え、**最優先タスクを「未決 15 ケースの判定」に固定**。さらに「完走しなくても部分報告を必ず出せ」
  「(a) 証明済 / (b) 実行した計算 / (c) 発見的推測 を区別せよ」を明示。

## 計算機探索 (2026-08-09、自前 GAP)

ChatGPT 打ち切り後、ユーザー指示でこちらで探索した。スクリプト = [`notes/meta/gap/`](../notes/meta/gap/)
(GAP 4.16.0 = `~/gap-4.16.0/gap`)。

### 探索を有限化する第 2 の還元

上記の還元に加えて: `G = ⟨H, g⟩` は**融合積 `H *_U L` (`L = U⋊⟨g⟩`) の商**なので、
`D = ⟨x,g⟩` の表示を課した有限表示群 `Γ` の**合同枚挙 (Todd–Coxeter)** で判定できる。
`Γ` が `H` を埋め込み `⟨x,g⟩ ≅ D` なら witness、`Γ` が潰れれば (有限・無限を問わず) 不可能。

`q = 3` では探索対象が有限リストの直積になる:

| 軸 | 個数 |
|---|---|
| `D` (位数 ≤ 60) | 5: `A₄`, `C₇⋊C₃`, `C₁₃⋊C₃`, `(C₄×C₄)⋊C₃`, `C₁₉⋊C₃` |
| 生成対 `(x,g)` | `Aut(D)`-軌道代表 (1〜2 個) |
| `g` の `U ≅ C₁₃` への作用 | 3: `u↦u`, `u↦u³`, `u↦u⁹` |

⚠ `x` の取り方は任意 — `U` は `P` の 13 本の `𝔽₃`-直線に推移的に作用する。

### 結果 (24 ケース)

**否定で確定 = 9 ケース** (`Γ` が潰れ `H` が埋まらない):

| `D` | 生成対 | `uexp=1` | `uexp=3` | `uexp=9` |
|---|---|---|---|---|
| `A₄` | 1/1 | `\|Γ\|=13` ✗ | `\|Γ\|=1` ✗ | `\|Γ\|=1` ✗ |
| `C₇⋊C₃` | 2/2 | `\|Γ\|=13` ✗ | `\|Γ\|=1` ✗ | `\|Γ\|=1` ✗ |
| `(C₄×C₄)⋊C₃` | 1/1 | `\|Γ\|=13` ✗ | `\|Γ\|=1` ✗ | `\|Γ\|=1` ✗ |

**未決 = 15 ケース** (合同枚挙が 300s で終わらず): `C₇⋊C₃` の生成対 1、
`C₁₃⋊C₃` の生成対 1・2、`C₁₉⋊C₃` の生成対 1・2 の各 3 作用。
⚠ **タイムアウトは「不可能」を意味しない** — `Γ` が無限か枚挙が重いだけかは未判定。

### 📌 観測された位数 13 / 1 は `Γ` のアーベル化そのもの (手で出る)

`Γ^ab` は **`D` の選び方によらず一様に**決まる:

1. `U` は `P` に不動点なく作用するので、その行列 `M` について `M − I` は `𝔽₃` 上可逆。
   アーベル化すると `u` の作用が自明になるので `(M−I)v = 0` ⟹ `v = 0`、すなわち
   **`P` は必ず死ぬ** (`a = b = c = 1`)。
2. `D = A⋊C₃` は f.p.f. なので `a ↦ [a,x]` が全単射 ⟹ `[D,D] = A`、よって `D^ab = C₃`。
   `g = x^y` は共役だからアーベル化で `x` と像が一致し、`x = 1` から **`g = 1`**。
3. 残る `u` は `g u g⁻¹ = u^{uexp}` のアーベル化 `u^{uexp−1} = 1` に従う。
   `uexp = 1` なら無条件、`uexp = 3` なら `u² = 1`、`uexp = 9` なら `u⁸ = 1`;
   いずれも `u¹³ = 1` と合わせて `uexp ∈ {3,9}` では `u = 1`。

⟹ `Γ^ab ≅ C₁₃` (`uexp = 1`) / 自明 (`uexp = 3, 9`)。**確定した 9 ケースは `Γ` が
自分のアーベル化まで潰れていた**ということ。裏を返すと **アーベル化は未決ケースの判定に
一切使えない** (どのケースでも同じ値になる) ので、別の手段が要る。

### 具体的な群での否定

* `PSL(2,27)`, `PGL(2,27)`: `H` は Borel 部分群として入るが `|N_G(U)| = 26, 52` で
  3 で割れない ⟹ 位数 3 の `g` が存在しない。
* `AΓL(1,27)` 型 (`P ◁ G`): `N_G(U)` の位数 3 の元はすべて `U`-共役で Frobenius 写像
  `φ: a ↦ a³` に帰着するが、`φ` は `1 ∈ F` を固定するので `x` と可換 ⟹ `⟨x,φ⟩ ≅ C₃×C₃`
  で Frobenius にならない。`φ^u` を取っても `⟨x, φ^u⟩ ⊇ P` となり核が 3-群。
* 次数 ≤ 21 の原始置換群: どれも `H = C₃³⋊C₁₃` を含まない。
  ⚠ ただし `A₂₇` 以上は `H` を含むので、**原始群の掃引は網羅的な方法として不適**。

### 無限 `G` を許す場合 (アマルガム)

`H`, `D`, `L` を辺群 `⟨x⟩`, `U`, `⟨g⟩` で貼る**群の三角形**の完備化になる。
Gersten–Stallings の非球面条件 `Σ 1/m_v ≤ 1` による自動的な発展可能性は**使えない**:
頂点 `N = U⋊⟨g⟩` のリンクには長さ 4 の閉路がある (`u₁g^{a}u₂g^{-a} = 1` が非自明解をもつ)
ので `m_N = 2` で、条件が破れる。

## Lean 形式化の状況 (2026-08-10 更新: **確定した数学はすべて形式化済**)

leaf = [`OddOrder/BG/AppC_Problem1.lean`](../OddOrder/BG/AppC_Problem1.lean) +
[`OddOrder/BG/AppC_Problem1Lattice.lean`](../OddOrder/BG/AppC_Problem1Lattice.lean) +
[`OddOrder/Algebra/PaleySpanning.lean`](../OddOrder/Algebra/PaleySpanning.lean) +
[`OddOrder/Algebra/RelationLattice.lean`](../OddOrder/Algebra/RelationLattice.lean) +
[`OddOrder/Algebra/PowerMonomialIndependence.lean`](../OddOrder/Algebra/PowerMonomialIndependence.lean)。
すべて AxiomsCheck 登録済 (allowlist のみ)、フルビルド green、--strict lint clean。

**2 つの主定理はどちらも無条件** (仮説は (A) + (B) と場合分けの条件だけ):

| | Lean | 仮説 |
|---|---|---|
| **定理 1 (中心化の場合)** | `Problem1.false_of_centralizing` | (A)+(B)、`g` が `σ(U)` を中心化 |
| **定理 2** | `Problem1.commutator_layerClosure_eq_top_of_exp` | (A)+(B)、`g` の指数 `e` が `U` 上 Frobenius 冪でない |
| ⟹ **witness は非可解** | `Problem1.not_isSolvable_of_exp` | 同上 |

### 定理 1 の内訳

| 数学 | Lean | 状態 |
|---|---|---|
| 補題 A′ `(xcx)³ = (xc)³` | `Problem1.pow_three_mul_eq_pow_three_of_commute` | ✅ |
| 仮説 (B) ⟹ `(g·x)³ = 1` | `Problem1.conj_mul_pow_three_eq_one` | ✅ |
| 関係式の族 `R(s)` | `Problem1.pow_three_mul_conj_eq_one` | ✅ |
| 補題 C (3 層消去) | `Problem1.cross_commute_of_three_relations` | ✅ |
| エンジン (Frobenius 捻り付き/なし) | `Problem1.commute_conj_of_le_closure(_twisted)` | ✅ |
| 最後の一マイル + 矛盾 | `..._of_commute_conj` / `Problem1.not_commute_conj` | ✅ |
| **補題 B (Paley 型の張り生成)** | `Paley.addClosure_paleySet_eq_top` | ✅ **Weil 不要の初等証明** |
| 補題 B の移送 (ノルム 1 ⟺ 平方元) | `Problem1.mem_normOneUnits_iff_isSquare` / `le_closure_orbitS` | ✅ |
| **🎯 定理 1 capstone (無条件)** | `Problem1.false_of_centralizing` | ✅ |

### 定理 2 の内訳

| 数学 | Lean | 状態 |
|---|---|---|
| 層写像の半線形性・捻れた関係式族 | `Problem1.conj_layer_of_exp` / `layered_relation_of_exp` | ✅ |
| 線形段・群段・完全群 | `Problem1.eq_one_of_closure_eq_top` / `eq_top_of_generators_mem` / `commutator_eq_top_of_relations` | ✅ |
| ambient 形 (仮説付き) | `Problem1.commutator_layerClosure_eq_top` | ✅ |
| 補題 D 解析的半分 (trace 展開 + Dedekind) | `PowerMonomial.eq_zero_of_forall_trace_sum_eq_zero` | ✅ |
| 補題 D 組合せ的半分 (剰余類分離) | `Problem1.injective_pow_mul(_pow)` | ✅ |
| **トレース双対性** (汎関数 = trace form) | `RelationLattice.exists_trace_repr` / `span_eq_top_of_trace_annihilator` | ✅ |
| **補題 D 本体** `L_e = F³` | `RelationLattice.span_triples_eq_top` | ✅ |
| 部分群版 (奇数指数で `S` → `Fˣ` に伝播) | `RelationLattice.span_triples_subgroup_eq_top` | ✅ |
| **補題 D の 𝔽_{3^q} 版** (奇代表の算術) | `Problem1.span_triples_normOne_eq_top` | ✅ |
| 関係格子を `σ(P)³` へ移送 | `Problem1.fieldTripleHom` / `closure_relationTriples_eq_top` | ✅ |
| **🎯 定理 2 capstone (無条件)** | `Problem1.commutator_layerClosure_eq_top_of_exp` | ✅ |
| **🎯 witness は非可解** | `Problem1.not_isSolvable_of_exp` | ✅ |

⚠ **形式化されているのは「部分解決」の部分であって、Problem 1 そのものではない**。
残る数学的ギャップは下記「次にやるとしたら」の 1・2 (`q ≥ 13`、`e ∉ ⟨3⟩`、`G` 非可解・無限可)。

## 次にやるとしたら (2026-08-10 更新)

1. **定理 2 の完全群 `N` をさらに潰す**。`N` は 3 個の共役可換 3-部分群で生成され、`U`
   (`P` に既約・不動点なく作用) が正規化している。`q = 7` では実際に潰れるので、その一般化が本線。
2. `q = 13` 以降で `[Γ_e : H̄] = 3` を実測する (定理 2 と合わせれば完全決着)。
   ⚠ 関係子 `u^n` が長い (`q = 13` で `n ≈ 8·10⁵`)。生成元を素冪分解した表示にすると軽くなるはず。
3. `c ∈ Q` が 3′-元であることは定理 2 では未使用。組み合わせる余地がある。
4. ~~**Lean 化**~~ **完了 (2026-08-10)**。定理 1・定理 2 とも無条件に形式化済 (上表)。
   補題 B は Weil 評価が不要な初等証明が見つかり、補題 D はトレース双対性 +
   Dedekind 独立性で閉じた。
5. 旧項目「`D` の枚挙」は**破棄**。万能完備化に置き換わった。

## 参照

- 原論文: [`references/glauberman-norton/`](../references/glauberman-norton/) (p.1094 が Prop 9 と Problem)
- BG: `references/bg/local-analysis.pdf` (Problem 1 = p.152、Remark (IV) = p.148)
- 形式化済の周辺: [issue 0179](closed/0179-bg-appc-remark-iv-glauberman-norton.md)
