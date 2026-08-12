# (B2) への攻撃: 衝突対の合成計算 (pair composition calculus) — 2026-08-13

[issue 0180](../../issues/0180-bg-appc-problem1-p-eq-three.md)。ChatGPT 第 4 回回答が open と明言した
「`S ≠ S′` の一般衝突に必要な**射影比 `S′/S` に依存する閉包定理**」
([`appC_problem1_chatgpt_answer_b1.md`](appC_problem1_chatgpt_answer_b1.md) §III.2) を正面から攻めた記録。
**結論: 閉包定理は「比の乗法的合成計算」として実在する。** ここから trace 不要の新判定が 3 つ出て、
既存 Theorem B の仮説も 2 本 (`hnotfrob`, `q ≠ 3`) 落ちた。

記法は Lean 側と揃える: `F = 𝔽_{3^q}`, `U` = 非零平方元 (= ノルム 1), `a(t), b(t), d(t)` =
`layerFieldHom data 0/1/2` (各層は `(F,+)` の忠実コピー、`g`-共役で `a → b → d → a`)、
関係式 `d(u^{e²}) b(u^e) a(u) = 1` (`u ∈ U`)、`e` 奇・`z^{e³} = z` (∀z)・`χ(−1) = −1` (`q` 奇)。

## 0. 出発点: 衝突関係式の正規形

`CollisionPair S S′` (向き付け済み: `δ = r₀^e − p₀^e ∈ U`) の関係式 (3)
(`layerFieldHom_one_conj`) で `v := δ z^e` と置換すると (`z ∈ U ⟺ v ∈ U`、
`K_p z^{e²} = S v^e`, `K_r z^{e²} = S′ v^e`):

> **(3′)  ∀v ∈ U: a(v) · b(S v^e) · a(v)⁻¹ = b(S′ v^e)**

これを一般化した対象を **conjPair** と呼ぶ:

> `conjPair (s, s′)` :⟺ ∀v ∈ U: `a(v) b(s v^e) a(v)⁻¹ = b(s′ v^e)`

- 衝突 ⟹ `conjPair (S, S′)` [(3′)]。
- **加法的**: `conjPair (s₁,s₁′) ∧ conjPair (s₂,s₂′) ⟹ conjPair (s₁+s₂, s₁′+s₂′)`
  (`b` が加法的 + 共役が準同型)。特に 𝔽₃-線形、負元閉包。
- **グラフ**: `conjPair (0, x) ⟹ x = 0` (`b` 単射)。よって conjPair 全体は
  部分 𝔽₃-空間上の単射加法写像 `Ψ` のグラフ (`Ψ` 単射: 逆向きは `a(v)⁻¹`-共役)。
- **𝔽₃-スケール**: `conjPair (s,s′) ⟹ conjPair (cs, cs′)` (`c ∈ 𝔽₃`; 関係式の `c` 乗)。

## 1. 不動点原理 — `W` の非零元 1 個 = 無条件矛盾

`conjPair (m, m)` (`m ≠ 0`) は `mem_commSubgroup_of_square` (c = 1) 経由で
`m ∈ commSubgroup` を与える。そして:

> **補題 A1.** `s ∈ commSubgroup ∖ {0}` ⟹ 矛盾。**trace も `hnotfrob` も `q ≠ 3` も不要。**

証明: 反転閉包 (`inv_mem_commSubgroup`) + 二分法 (`pow_four_eq_one_or_forall_mem`)。
- `W = F` 枝: `1 ∈ W`。
- `s⁴ = 1` 枝: `s² = −1` は `−1` 非平方で不可 ⟹ `s = ±1` ⟹ (負元閉包) `1 ∈ W`。

どちらも `1 ∈ W`、すなわち `Commute(a(1), b(1))`。ところが `a(1) = x`, `b(1) = g⁻¹xg` なので
これは **`not_commute_conj` (定理 1 の終局) に直接矛盾**。∎

⟹ 既存 `false_of_collisionPair_self` (Theorem B) の 2 分岐 (trace 経由 / `false_of_s_normalizes_layerOne`
経由) は両方この 1 本に短絡し、**仮説 `hnotfrob` と `q ≠ 3` が落ちる** (旧証明の `W = F` 枝だけが
`hnotfrob` を使っていた)。

## 2. 合成定理 — 比は乗法的に合成される

> **定理 C1 (straight compose).** `conjPair (s, s′)`, `conjPair (t, t′)`、すべて非零とする。
> `r := s′t′/(ts)` (比の積 `ρ_s ρ_t`) と置くと、ある `m ≠ 0` が存在して
> `conjPair (m, r·m)` **または** `conjPair (r·m, m)`。
> **退化は起こらない** (仮説は非零性のみ)。

証明。`v ∈ U` を任意とする。`χ(c s′/t) = 1` となる `c ∈ {±1}` を取る (ちょうど一方; 存在だけ使う)。
`η := (c s′/t)^{e²} ∈ U`、`u := η v ∈ U`。すると
`u^e = (cs′/t)^{e³} v^e = (cs′/t) v^e` ⟹ `(ct)·u^e = s′ v^e`。

1. pair 1: `a(v) b(s v^e) a(v)⁻¹ = b(s′ v^e)`。
2. pair 2 の `c`-スケール版を `u` で: `a(u) b(ct·u^e) a(u)⁻¹ = b(ct′·u^e)`。引数一致より
   `a(u) b(s′ v^e) a(u)⁻¹ = b(ct′ u^e)`、そして `ct′u^e = ct′(cs′/t)v^e = (s′t′/t) v^e`。
3. 合成: `a(u)a(v) = a((1+η)v)`:

> `a(τ v) · b(s v^e) · a(τ v)⁻¹ = b((s′t′/t) v^e)`,  `τ := 1 + η`。

**`τ ≠ 0`**: `τ = 0 ⟺ η = −1`、しかし `η ∈ U` かつ `χ(−1) = −1` — 不可能。これが
「退化なし」の理由 (平方性の選択が退化を構造的に排除する)。

正規化: `χ(τ) = 1` なら `w := τv` が `U` を走り、pair `(s τ^{−e}, (s′t′/t) τ^{−e})` — 比 `r`。
`χ(τ) = −1` なら `w := −τv` で `a(τv) = a(w)⁻¹`、関係式が裏返って pair
`((s′t′/t) τ^{−e}, s τ^{−e})` (負元閉包で符号は吸収) — 比 `r⁻¹`。∎

> **定理 C2 (flip compose).** 同上で `t′ ≠ ±s′` を仮定すると、`r̂ := s′t/(t′s)` (比の商
> `ρ_s ρ_t^{−1}`) について、ある `m ≠ 0` で `conjPair (m, r̂·m)` または `conjPair (r̂·m, m)`。

証明: pair 2 を逆向きに使う。`χ(c s′/t′) = 1` なる `c`、`η̂ := (cs′/t′)^{e²}`、`û := η̂ v`、
`u := −û ∈ −U`。pair 2 の逆・`c`-スケール: `a(−û) b(ct′ û^e) a(−û)⁻¹ = b(ct û^e)`。
`ct′û^e = s′v^e` (同じ計算)、出力 `ct·û^e = (s′t/t′) v^e`。合成: `a(−û)a(v) = a((1−η̂)v)`。
**退化 `1 − η̂ = 0 ⟺ cs′/t′ = 1 ⟺ t′ = ±s′`** — これが仮説。以降同じ。∎

⚠ straight は退化なし・flip は `t′ = ±s′` でのみ退化、という非対称が本質的
(自分自身との flip 合成 = 「比 1 をタダで作る」だけが禁止されている —
witness が存在しうるための構造的整合性)。

## 3. 新判定 3 つ (すべて trace 不要)

### 定理 N1 (`S′ = −S` は致命的)

`conjPair (S, −S)` なら `−1`-スケールで `conjPair (−S, S)` でもある。`v`-共役を 2 回:
`a(v)² = a(2v) = a(−v)` ⟹ `a(−v) b(Sv^e) a(−v)⁻¹ = b(Sv^e)` ⟹ `Commute(a(v), b(Sv^e))`
(∀v ∈ U) ⟹ `S ∈ commSubgroup ∖ 0` ⟹ **矛盾** (A1)。∎ (合成定理すら不要、char 3 の `2 = −1` だけ。)

### 定理 N2 (比が等しい 2 衝突は致命的)

衝突 `(S₁, S₁′)`, `(S₂, S₂′)` が `S₁′ S₂ = S₂′ S₁` (比が等しい) かつ `S₂′ ∉ {±S₁′}` なら、
C2 で `r̂ = 1` の pair ⟹ `conjPair (m, m)`, `m ≠ 0` ⟹ **矛盾**。∎

Frobenius twist (`CollisionPair.frobenius`: `(S^{3^k}, S′^{3^k})` も衝突) と組めるので、
実効条件は「`ρ₁ = ρ₂^{3^k}` なる `k` があり、対応する twist が `±`-同一でない」。

### 定理 N3 (Frobenius 束の零化判定)

conjPair の加法性 + Frobenius twist より、任意の係数 `c_j ∈ 𝔽₃` で
`conjPair (Σ c_j S^{3^j}, Σ c_j S′^{3^j})`。グラフ性と A1 から:

- `Σ c_j S^{3^j} = 0` なのに `Σ c_j S′^{3^j} ≠ 0` ⟹ 矛盾 (グラフ性、witness では起これない
  ⟹ **witness は `Ann_{𝔽₃[Frob]}(S) = Ann(S′)` を強制**)。
- `Σ c_j (S′^{3^j} − S^{3^j}) = 0` かつ `Σ c_j S^{3^j} ≠ 0` ⟹ 比 1 の pair ⟹ **矛盾**。
  ⟹ **witness は `Ann(S′ − S) ⊆ Ann(S)`、すなわち `⟨S⟩_{𝔽₃[Frob]} ⊆ ⟨S′−S⟩_{𝔽₃[Frob]}` を強制**。

trace との関係 (敵対的検証で精密化): `c = (1,…,1)` は `ConjPair (Tr S, Tr S′)` を与え、両成分は
`𝔽₃` に落ちる。そこから場合分け (`Tr S ≠ 0` なら `Tr S′ = ±Tr S` の両ケースがそれぞれ
比 1 / N1 型で致命的、`Tr S′ = 0` はグラフ性で `Tr S = 0` を強制) すると、**旧 trace 判定
`Tr S ≠ 0 ∨ Tr S′ ≠ 0 ⟹ ⊥` 全体が合成計算から再導出される** — 旧証明の「関係式 `q` 本の積 +
`Aut(C₃)`」機構は不要になった。新しいのは trace 以外の成分: **`q ≠ 3`** なら `x^q − 1` は
squarefree で `(x−1)·Π f_i` と分解し、各既約因子 `f_i` ごとに独立な判定になる。

## 4. 到達可能性ゲームと残る壁

合成で作れる比の集合 `R ∋ ρ := S′/S` は「`r₁, r₂ ∈ R ⟹ (r₁r₂)^{±1} ∈ R`」で閉じる
(`±1` は field data `χ(τ)` が決める — 我々には選べない)。**比 1 に到達すれば矛盾**なので、
witness は到達可能集合が 1 を避けるよう field data が完璧に整合することを要求される。

- 符号が完全に敵対的でも: 自己合成は大きさを倍にする ⟹ `ord(ρ)` の 2-part は必ず潰せる。
  `ord(ρ) | Q − 1 = 2n` (`n` 奇) なので 2-part だけで落ちるのは `ρ = ±1` (N1/Theorem B) のみ。
- 奇数 order の残部には flip 合成 (退化条件つき) が要る: 「同じ比・異なる base」の pair 2 つで
  比 1 に落とす。base が `±` 一致する例外系列 (`m(s,t) = ±m(t,s)` 型の明示的な体の恒等式) を
  witness が全部満たすことだけが逃げ道。
- ⟹ **(B2) の完全消去は「例外恒等式系が充足不能」の証明に帰着した**。これは体の中の明示的な
  方程式系であり、群論はもう要らない。未証明だが、per-collision certificate としては
  即座に使える (N1/N2/N3 のどれかが当たれば trace 不要で決着)。

サイズ ≥ 3 のファイバー (`q = 13` で 3471 個) では比がコサイクル `ρ_{12}ρ_{23} = ρ_{13}` を
なすので、C1 の合成 (符号 +) と衝突 pair `(S₁₃, S₁₃′)` が「同じ比・異なる base」を大量生産する
— N2 の適用先は実際には豊富。

## 5. 検証状況

- 導出はすべて (1)–(3′) と層の可換性・加法性のみ使用。`d`-展開 ((1) の逆順版) は
  今日の結果には**不要** — すべて `(a, b)` 二層で閉じている。⚠ 手計算版で使っていた
  `e` の奇数性も、群側の定式化 (conjugator を `a(ηv)⁻¹` に取る) では**不要**になった。
- **敵対的検証 (subagent、2026-08-13)**: (3′)・A1・C1・C2・N1・N2・N3 の全ステップを repo の
  規約と突き合わせて独立再導出、**反証ゼロ** (全項目 CONFIRMED)。指摘 nit 3 件は反映済み
  (N1 の `S ≠ 0`、`q = 3` での因子分解注記、trace 再導出の記述)。
- **Lean 化完了 (2026-08-13、axiom-clean・AxiomsCheck 登録済・--strict lint clean)**:
  [`OddOrder/BG/AppC_Problem1PairComposition.lean`](../../OddOrder/BG/AppC_Problem1PairComposition.lean)
  (`ConjPair` + add/sum/graph/`of_collisionPair` + `compose`/`composeFlip` +
  `false_of_collisionPair_neg`/`_ratio_eq`/`_frobCombo`)、
  [`AppC_Problem1SameCoset.lean`](../../OddOrder/BG/AppC_Problem1SameCoset.lean)
  (`false_of_mem_commSubgroup_ne_zero` = A1; **Theorem B と証明書形から `hnotfrob` と
  `q ≠ 3` を除去**)。

## 6. 数値インパクト測定 (2026-08-13、GF(3^7)/GF(3^13) 悉皆)

`q = 7` (70 衝突 × 2 指数) と `q = 13` (50,726 衝突 × 2 指数、`T` 全列挙) で
各判定のカバレッジを測った (独立実装 2 通り、既知のファイバー分布と完全一致):

| q / E | 衝突 | 旧 trace | N1 (`S′=−S`) | 比 1 | N2/F | 合計 | **escape** |
|---|---|---|---|---|---|---|---|
| 7 / 151 | 70 | 56 | 0 | 0 | 0 | 56 | **14** |
| 7 / 941 | 70 | 63 | 0 | 0 | 0 | 63 | **7** |
| 13 / E₁ | 50726 | 44798 | 0 | 0 | 1625 | 44993 | **5733** |
| 13 / E₂ | 50726 | 45227 | 0 | 0 | 1690 | 45409 | **5317** |

読み取り:

1. **N2 (等比 2 衝突) は q = 13 で trace の外側を実際に殺す** (F-only = 195/182 件) —
   深さ 1 の合成だけで判定が真に強くなった初の実測。
2. `S′ = ±S` は q = 7, 13 の実データでは**一度も起きない** (N1/Theorem B の実効カバレッジは
   この 2 つの q ではゼロ。定理としては残る)。
3. **escape が残る** — q = 7 で 3 Frobenius 軌道 (14+7 衝突、全て両端 trace 0・等比相手なし)。
   ⟹ 深さ 1 の判定集合では (B2) は消えない。**次の一手 = 合成チェーン (深さ ≥ 2)**:
   compose で作った pair の base `m = s(1+η)^{−e}` は明示式なので、
   「`m(s,t)` vs `m(t,s)` (同比・異 base) → flip で比 1」の探索は場合分けの符号
   (`χ(1+η)`) 込みで**全部計算可能**。escape 21 衝突に対して深さ 2 チェーンが閉じるかを
   測るのが次の実験。
4. 整合性: trace-dead = escape + F-only (5928 = 5733+195, 5499 = 5317+182) ✓。

スクリプト = scratchpad `collision_impact/` (session-local。恒久化するなら
`notes/meta/` へ移す — 現状は結果のみ本 note に記録)。
