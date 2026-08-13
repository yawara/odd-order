# (B2) への攻撃: 衝突対の合成計算 (pair composition calculus) — 2026-08-13

> **⚠ 2026-08-13 深夜に §9 で完結**: (B2) は**定理として完全消滅**した (chain reversal C3 +
> Frobenius 加群の巡回性)。**衝突が 1 個あれば witness は無条件に死ぬ** — trace も span も
> 剛性も不要。§6–§8 の実験・剛性還元は歴史的記録 + (B1) への手がかりとして残す
> (証明としては superseded)。残る壁は (B1) = 衝突の存在、のみ。

[issue 0180](../../issues/closed/0180-bg-appc-problem1-p-eq-three.md)。ChatGPT 第 4 回回答が open と明言した
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

### 第 3 の kill 条件 (K3) と escape の生存条件

pair 空間 `V` (生成 pair の 𝔽₃-span) の `Dom` (第 1 成分の射影) が **`F` 全体に達したら
それ自体が致命的**: 全ての `s` に pair があるなら `a(v)` が `B` 全体を `B` に写す ⟹
`A ≤ N_G(B)` ⟹ `false_of_normalizes_layerOne` (要 `hnotfrob` = exotic なら自動)。

escape 衝突 (`Tr S = Tr S′ = 0`) では初期 `Dom₀ = ⟨S⟩_{Frob} ⊆ ker Tr`。`3` が `mod q` の
原始根なら (`q = 7, 13` ✓) `ker Tr` の Frobenius 加群は既約なので `Dom₀ = ker Tr` (dim `q−1`)。
⟹ **escape が生き残る必要十分に近い条件: 合成で出る base `m = s·τ^{−E}` が全部
`Tr m = 0` に留まり続け (1 個でも破れたら span が `F` になり K3)、かつ不動点 (K1) が
出ないこと**。合成 base は `E`-冪と `τ = 1 ± (c s′/t)^{E²}` を含み Frobenius 加群構造を
一般には保たない ⟹ この confinement は極端に強い制約で、(B2) 完全消去の証明目標は
「`Tr(s·τ^{−E}) = 0` が閉包全体で維持されることの不可能性」= `ker Tr` 上の構造化された
指標和の非消滅、にまで具体化した。

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
3. ~~escape が残る~~ → **閉包実験で全滅 (下記 §7)**。
4. 整合性: trace-dead = escape + F-only (5928 = 5733+195, 5499 = 5317+182) ✓。

スクリプト = scratchpad `collision_impact/` `chain_closure/` (session-local。
結果は本 note に記録)。

## 7. 🎯 閉包実験 — escape は深さ 1 で全滅、(B2) は q = 7 で経験的に完全消滅 (2026-08-13)

escape 21 衝突 (3 Frobenius 軌道) に対し、pair 空間
`V := span_{𝔽₃}{(S^{3^j}, S′^{3^j})} ⊆ 𝔽₃^{14}` を C1/C2 合成で飽和させる実験
(kill 条件: **K1** = `V ∩ Δ ≠ 0` 不動点 / **K2** = グラフ性違反 `(0, x≠0) ∈ V` /
**K3** = `dim Dom(V) = q` ⟹ `A ≤ N_G(B)` ⟹ `false_of_normalizes_layerOne`):

> **全 21 衝突が round 1 で死亡** — しかも**最初の自己合成 C1(v,v) 1 回**で。
> 機構は一様: escape は `Tr S = Tr S′ = 0` ⟹ 初期 `V` はちょうど dim 6
> (= `x⁷−1` の次数 6 因子成分 = `ker Tr` 加群)。自己合成 1 回が**必ず加群の外に出て**
> dim 7 に達し、dim 7 は K2 ∨ K3 を強制 (14/21 は K1 も)。C1 だけでも C2 だけでも殺せる。
> 検証 0 anomaly (exactly-one-c / τ ≠ 0 / 全 kill の brute-force 再検証込み)。

⟹ **GF(3⁷) の全 140 衝突 (両指数) が有効な証明書** — {trace ∪ N2 ∪ 深さ 1 閉包} で
escape ゼロ。**(B2) は q = 7 で経験的に完全消滅**した。

### 一般証明への含意 (次の一手の具体形)

escape の生存には「合成 base が全部 `ker Tr` (唯一の Frobenius 安定超平面) に閉じ込め
られ続ける」ことが必要 (§4 の K3 観察)。実験はこの confinement が**最初の 1 歩で必ず破れる**
ことを示した。⟹ (B2) 完全消去の証明目標は 1 本に絞られた:

> **予想 (B2-elim)**: `q` 奇素数、`E` exotic、衝突 `(S, S′)` が `Tr S = Tr S′ = 0`、
> `v = (S, S′)`-型の Frobenius 加群元の自己合成 `C1(v,v)` の base `m = s·(1+η)^{−E}`
> (`η = (cs′/s-型)^{E²}`) について、**`Tr m ≠ 0` となる加群元 `v` が常に存在する**
> (あるいは K1/K2 で死ぬ)。

これは `ker Tr` 上の構造化された指標和の非消滅で、生の (B1) equidistribution より
はるかに手がかりが多い (`τ` の明示式・加群の既約性・`E³ = 1`)。⚠ (B1) 自体
(衝突の存在) は依然 open — (B2) が消えると残る仮定は純粋に「衝突が 1 個ある」だけになる。

- ~~K3 の Lean 入口は未形式化~~ → **完了** (`false_of_conjPair_spanning`、v = 1 評価で
  `x` が第 2 層の生成系を層内に写す ⟹ 有限性 ⟹ `false_of_s_normalizes_layerOne`)。
  K1 入口 = `false_of_conjPair_self`、K2 入口 = `ConjPair.right_eq_zero` — **3 条件とも Lean 済**。

### q = 13: escape 11,050 件も全滅 (2026-08-13)

同エンジンで **11,050 / 11,050 killed、生存者ゼロ・anomaly ゼロ** (8,528 合成、全 kill を
明示 witness — K1/K2 は kernel 組合せベクトル、K3 は単位ベクトル所属 — で独立再検証)。
kill round: r0 = 1625+1196 (`V₀` 単独で K1/K2 = **N3 型、既 Lean 化の `frobCombo` の射程**)、
r1 = 4082+4069 (自己合成 1 回)、r2 = 26+52 (dim₀ = dom₀ = 9 の特殊軌道、決定的)。
Frobenius 同変性の実証: 全 850 軌道で 13 メンバーの結果が完全一致。

q = 7 との違い: q = 13 では `dim V₀ ∈ {9, 12}` (q = 7 は一様に 6) で、`V₀` 単独で死ぬ
衝突が 2,821 件ある (`x¹³−1` の因子構造が豊富なため)。r2 の 78 件はすべて
`dim₀ = dom₀ = 9` 軌道で、うち 1 軌道は dim 12 のまま**真の K1** (dim-13 機構でない) で死んだ。

⟹ **両方の q で全 101,592 衝突が例外なく有効な証明書** — 合成閉包 + 線形代数は
(この 2 つの q では) 完全な証明書生成器である。

## 8. 剛性定理への還元 (2026-08-13 夜、導出済・数値検証中)

`3` が `mod q` の原始根の場合 (`q = 7, 19, 29, 31, …`; `x^q−1 = (x−1)f`、`W := ker Tr ≅ K :=
𝔽₃[x]/f ≅ 𝔽_{3^{q−1}}` は既約 `R`-加群)、(B2)-elim 予想を**明示的な方程式系の被覆不能性**に
還元した。escape 衝突では `S′ = μ·S` (`μ ∈ K^×` の加群作用、一意)。witness が生きるには
全合成 base が `ker Tr` に入る必要があり (K3)、固定した平方 `z₀` に対して有効な第 1 pair は
`φ(aμ) ∈ W ∩ z₀W ∖ 0` (dim `q−2` — `−W = W` なので両符号が同じ集合に落ちる) を**全部**走る。
よって:

> **剛性**: witness ⟹ `v(z₀) := (1+z₀^{E²})^{−E}` が dim 2 の明示空間
> `P(z₀) = (ψ*)^{−1}(𝔽₃·1 + 𝔽₃·z₀^{−1})` に入る (∀ 有効 `z₀`)。
> ここで `ψ` = `μ^{−1}` の加群作用、`*` = trace 形式の随伴 (`c(x) ↦ c(x^{−1})`、
> `(W ∩ zW)^⊥ = 𝔽₃·1 + 𝔽₃·z^{−1}` を使用)。

`−E²` 乗 (`E³ ≡ 1`) で統一形に落ちる:

> **(B2)-elim ⟺ 8 本の方程式 `α·n₁ + β·ν̃(X^{−E}) = (1+X)^{−E}`** (`(α,β) ∈ 𝔽₃²∖0`、
> `ν̃` = 固定線形写像、`n₁ = ν̃(1)`) **が admissible な `X` 全体を覆えない**。
> `β = 0` の 2 本は `v` の単射性から**解が高々 1 個ずつ** (証明済)。残る 6 本
> (`β ≠ 0`) の解数評価が最後の壁 — ここは加法的 `ν̃` と `E`-冪の混合方程式で、
> 生の (B1) より構造が濃い (`E³ = 1`・`ν̃` の加群性・`X ↦ X^{−E}` の乗法性)。

**✅ 数値検証完了 (2026-08-13、GF(3⁷) 全 3 escape 軌道、反証ゼロ)**:

- `μ` の存在・一意性 (mod `Ann(S)`)・Frobenius 軌道内不変 ✓。加群作用の随伴 = 係数反転
  `c(x) ↦ c(x⁻¹)` ✓ (200 triple)。`(W∩z₀W)^⊥ = 𝔽₃·1 + 𝔽₃·z₀⁻¹` ✓ (100/100)。
  `dim(W ∩ z₀W) = q−2` は **全 2184 個の `z₀ ∉ 𝔽₃^×` で悉皆確認** ✓。
- **twist の正体 = `σ(μ) := μ(x⁻¹)` の作用** (`μ⁻¹` でなく!)、`R = 𝔽₃ × K` への可逆 lift
  (`(1, σ(μ))`; 非可逆 lift は `P` が潰れる — lift の可逆性が必須)。`P(z₀)` は直接核計算と
  100/100 一致。
- ⚠ 符号 nit: 論文式 base `m = (aS)(1+η)^{−E}` は `χ(τ) = −1` 側で閉包実装の base と
  `−1` 倍ずれる (実装は `−τ` を代入)。`V`, `P` が `−1`-閉なので membership 論には無影響。
- **Claim 4 (定量・本命)**: 統一方程式の可解集合 (witness の生存に必要な `z₀`) は
  1092 個の平方 `z₀` のうち **151/A: 14 個 (2 Frobenius 軌道) / 151/B: 14 個 / 941/A: 0 個
  (空!)**。ランダム基準 (期待 0.57 軌道) と整合 = 構造的強制なし。witness は**全** `z₀` で
  成立を要求されるので、剛性 1 本で escape は圧倒的マージンで死ぬ。

⟹ 剛性は**「z₀ を 1 個取って `v(z₀) ∉ P(z₀)` を確認する」激安の新証明書形**を与える
(閉包 LA より軽い; Lean 入口は既存の `false_of_conjPair_spanning` + frobCombo 有限個で
組める)。**(B2)-elim の一般証明の残件 = `β ≠ 0` の 6 本の方程式族の解数が admissible 集合
(≈ Q/2) を覆えないことの証明** (`β = 0` の 2 本は単射性で解 ≤ 1 個ずつ、証明済)。
`3` が原始根でない `q` は `W` の分解に応じた同型の議論が要る (未着手)。
**→ §9 で全て不要になった** (剛性ルートは per-z₀ 証明書としても superseded)。

## 9. 🎯🎯 (B2) の完全消去 — chain reversal 定理 (2026-08-13 深夜、Lean 化・検証済)

§8 が「退化」として除外していた **z₀ ∈ 𝔽₃^× の合成サイト**を調べる過程で、char 3 特有の
3 行の恒等式が見つかり、(B2) が**丸ごと定理として落ちた**。

### 補題 C3 (chain reversal)

> **conjPair (s, s′) ∧ conjPair (s′, s″) ⟹ conjPair (s″, s)。**
>
> 証明: 同じ `v` で 2 つの関係式を連鎖すると `a(v)² b(sv^e) a(v)⁻² = b(s″v^e)`。
> `a` は加法的で char 3 なので `a(v)² = a(2v) = a(−v) = a(v)⁻¹` ⟹
> `a(v)⁻¹ b(sv^e) a(v) = b(s″v^e)` ⟹ 両辺を `a(v)` 共役して `conjPair (s″, s)`。∎

C1/C2 と違い χ・τ・`E`-冪が一切出ない (N1 の機構 `a(v)² = a(−v)` の一般化)。
同値な言い方: `a(v)³ = a(3v) = 1` — conjugation by `a(v)` は位数 3。

### 定理 ((B2)-elim 完全版)

> **`q ≠ 3` のとき、衝突対 `(S, S′)` が 1 つでも存在すれば witness は矛盾する。**
> トレース条件・span 条件・`e` の exotic 性・`3 mod q` の位数、すべて不要。
> (`q = 3` は exotic `e` が存在せず定理 1 が既にカバー — 何も失わない。)

証明の骨子 (5 手):

1. **(K-frob)**: `conjPair (c.S, c.S′)` ∀`c ∈ 𝔽₃[x]` (Frobenius twist + 加法性; 既存機構)。
2. **Ann 包含**: `c.S = 0` なら graph 性 (K2) より `c.S′ = 0`。
3. **巡回性**: Frobenius の最小多項式 = `x^q − 1` (Dedekind 独立性) ⟹ `F` は
   `𝔽₃[x]/(x^q−1)` の正則表現 (multiplicity-free) ⟹ Ann 包含から **`S′ = a₀.S`**。
4. **chain**: C3 を `(S, S′), (S′, a₀².S)` に適用 ⟹ `conjPair (a₀².S, S)`;
   pair `(a₀².S, a₀³.S)` との差 + K2 ⟹ **`a₀³.S = S`**。
5. **char 3 + squarefree**: `a₀³ − 1 = (a₀ − 1)³`、`x^q − 1` は `q ≠ 3` で squarefree
   ⟹ Ann は radical (gcd/Bezout) ⟹ `(a₀ − 1).S = 0` ⟹ **`S′ = S`** ⟹
   Theorem B (`false_of_collisionPair_self`、無仮説版) で矛盾。∎

### Lean 化 (2026-08-13、axiom-clean・AxiomsCheck 登録済・--strict lint clean)

| 内容 | Lean |
|---|---|
| 補題 C3 | `ConjPair.chain` (PairComposition) |
| (K-frob) の標準 packaging | `conjPair_aeval_of_collisionPair` |
| Frobenius 加群の巡回性 (正規基底不要の直接構成) | `OddOrder/Algebra/FrobeniusCyclicModule.lean`: `frobEnd` / `minpoly_frobEnd` / `exists_frobenius_cyclic_vector` / `exists_aeval_frobEnd_eq_of_forall_imp` |
| radical 降冪 (squarefree + gcd/Bezout) | `aeval_frobEnd_eq_zero_of_pow` |
| **🎯 capstone** | **`false_of_collisionPair`** (仮説 = data + `p = 3`, `q` 素数 ≠ 3, 奇 + `e` 奇・`e³`-cube・共役指数 + 衝突 1 個) |

実装メモ: 巡回性は mathlib の `minpoly_frobeniusAlgHom` (Frobenius の最小多項式 = `X^q − 1`) +
`Module.exists_ker_toSpanSingleton_eq_annihilator` (PID 上の f.g. 加群) + 次元勘定で、正規基底
定理を経由せずに閉じた。radical 性は `Squarefree.dvd_pow_iff_dvd` + `EuclideanDomain.gcd_eq_gcd_ab`
の 3 行。dedupe: `CollisionPair.frobenius_pow` (PairComposition の重複) を削除し
`frobenius_iterate` (Trace) に一本化。

### 検証 (2026-08-13)

- **敵対的検証 (subagent 3 レンズ、全 CONFIRMED・fatal 0)**: (i) group レンズ = C3 を Lean 定義
  から独立再導出 (−v トラップ無し・向き一致)、q = 3 では反例 `a₀ = x` が実在し squarefree の
  必要箇所が正確であることを 𝔽₃[x]/(x⁷−1) の 20,000 ランダム試行で確認。(ii) module レンズ =
  正規基底/multiplicity-free/gcd の全リンク + **GF(3⁵) で 243×243 全ペアの悉皆計算検証**
  (Ann 包含 ⟹ 軌道所属、違反 0)。(iii) history レンズ = §6 の「escape」は「安い証明書が
  当たらない」の意味で「witness が生き残る」ではない ⟹ 閉包実験の kill 100% (101,592/101,592)
  と完全整合; §7/§8 が一般証明を取り逃した理由 = 閉包エンジンは C1/C2 のみで **C3 を持って
  いなかった**。
- **数値サニティ**: 検証済み compose_C1 エンジンはサイト `((w, μw), (μw, μ²w))` で正確に
  `(μ².w, w)` を出力 (3 escape 軌道 × 200 w、全 600 一致、anomaly 0) — C3 は C1 の
  `z_raw = 1, τ = −1` 退化点そのもの。
- **coverage 悉皆スキャン** (本 session、§8 剛性の独立確認): 8 統一方程式の被覆数は
  **全 728 twist ν で最大 21/1092** (平均 3.0、β = 0 は全 ν で 0 件、escape 3 軌道の
  14/14/0 を再現)。剛性ルートも全 ν で成立していた — が、C3 定理により不要になった。

### 帰結

- **(B2) は消滅**。witness への障害は「**衝突が 1 個存在する**」だけ = **(B1) に一本化**。
- **per-q 証明書が激安化**: 各 exotic 指数類 {E, E²} につき衝突 1 個の発見で決着
  (trace 値・剰余類・span・閉包 LA すべて不要; E↔E² 共役で片方の類のみで十分)。
  `q = 47, 73` の残り指数も birthday 探索 1 回/類で閉じる。
- §7 の閉包実験・§8 の剛性定理・trace 判定・N1/N2/N3 は certificate としては superseded
  (定理としては残る; (B1) の equidistribution への手がかりとしての価値は不変)。
