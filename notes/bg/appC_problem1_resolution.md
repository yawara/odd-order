# BG App.C Problem 1 (p = 3) の否定的解決 — 統合証明文書 — 2026-08-13

[issue 0180](../../issues/0180-bg-appc-problem1-p-eq-three.md)。
[`appC_problem1_pair_composition.md`](appC_problem1_pair_composition.md) §9 ((B2)-elim) と
[`appC_problem1_skew_calculus.md`](appC_problem1_skew_calculus.md) §1–6.2 (skew calculus +
endgame) を **1 本の定理 + 完全証明**として書き下した統合文書。敵対的検証 6 レンズ
(部品 5 + 最終 assembly 監査、全 CONFIRMED・fatal 0、§8) を反映済。
**✅✅ 完全機械検証 (2026-08-13 深夜)**: **主定理が Lean で完結** —
**`hypothesisB_false : FieldNormalizerData p q G → p = 3 → False`**
(`AppC_Problem1SkewEndgame.lean`、全 `q`・`G` の有限性不要・追加仮定ゼロ・axiom-clean)。
内訳: `q ≠ 3` = skew calculus のケース木 (`false_of_witness` — 指数は
`exists_odd_cube_exponent` で witness から抽出、`q` の奇性は (A) から)、`q = 3` =
指数が全部 Frobenius 冪 (`e³ ≡ 1 mod 13` の解 {1,3,9} = ⟨3⟩、decide) で定理 1 の
`e ∈ ⟨3⟩` 側 (`false_of_frobenius_exponent` — twisted engine + Frobenius 移送 spanning)。
紙上のみの部分は消滅 — 本文書の主定理は §0 の形のまま全て機械検証済 (issue 0181 closed)。

## 0. 問題と結果

**問題 (BG p.152 / Glauberman–Norton p.1094 "Problem (Péterfalvi)", 1993)**:

> Can the hypothesis of Proposition 9 be satisfied for `p = 3`?

Proposition 9 の hypothesis: (A) `q ∤ p − 1`、(B) 単射準同型 `σ : H → G` (`H = P ⋊ U` は
Frobenius 群)、有限可換 `p′`-部分群 `Q ≤ G`、`y ∈ Q` が存在して `σ(P₀)` が `Q` を正規化し
`σ(P₀)^y` が `σ(U)` を正規化する。**`G` の有限性は要求されない**。

> **主定理.** `p = 3` のとき、**すべての奇素数 `q`** に対し hypothesis (B) を満たす
> `(G, σ, Q, y)` は存在しない (`G` は無限でもよい)。**答えは NO**。

証明の場合分け: `g := σ(P₀)^y` の生成元が `σ(U) ≅ Fˣ` の平方元群 `U` に誘導する指数を
`e` (`e³ ≡ 1 mod n`, `n = (3^q − 1)/2`) とする。

- **`e ∈ ⟨3⟩` (Frobenius 冪) — 全 `q`、特に `q = 3` の全ケース**: **定理 1**
  (`false_of_centralizing`、Lean 済) で決着。`q = 3` では位数 3 の指数がすべて `⟨3⟩` に
  入るので `q = 3` はここで完結する。
- **残り (`q ≠ 3`)**: 本文書の**ケース木** (§2–§6)。木は `e` の exotic 性を使わない
  (`e ≡ 1` でも `D` が定数になり衝突が氾濫して step 1 で死ぬ) ので、`q ≠ 3` の全指数を
  一様に覆う。Part I が要求する「`x^q − 1` が 𝔽₃ 上 squarefree」がちょうど `q ≠ 3` であり、
  定理 1 と正確に相補的。

## 1. 設定と標準仮定 (すべて Lean 検証済)

`F = 𝔽_{3^q} = GaloisField 3 q`、`Q := 3^q`、`U` = 非零平方元 (= ノルム 1 元)、
`χ` = 平方指標。witness から得る構造 (`FieldNormalizerData`):

- **層** `a, b, d` = `layerFieldHom data 0/1/2`: 各層は `(F,+)` の忠実 (単射・加法的) な
  コピーで、`g := conjGen` 共役が `a → b → d → a` と巡回 (`g³ = 1`)。
- **基本関係式** (`layered_relation_field`): `d(u^{e²})·b(u^e)·a(u) = 1` (∀u ∈ U)。
- **Paley 集合** `T := {p ∈ U : p − 1 ∈ U}`。`D(p) := p^e − (p−1)^e`、
  `K(p) := (p−1)^{e²} − p^{e²}`。**衝突** = `D(p) = D(r)` なる `p ≠ r ∈ T`
  (向き付けて `δ := r^e − p^e ∈ U`、`CollisionPair`)。

**標準仮定とその導出** (witness から全部出る):

| 仮定 | 導出 |
|---|---|
| `χ(−1) = −1` | `q` 奇 ⟹ `Q ≡ 3 mod 4` |
| `e` 奇 | `\|U\| = n` 奇なので奇な代表を取れる |
| `z^{e³} = z` (∀z ∈ F) | `e³ ≡ 1 mod n` + 両者奇 ⟹ `e³ ≡ 1 mod Q−1` (CRT) |
| `gcd(e, Q−1) = 1`、`x ↦ x^e` 全単射 | cube 条件の直接の帰結 |
| `gcd(3e, Q−1) = 1` | `3 ∤ Q−1` |
| `K(p) ≠ 0` (∀p ∈ T) | `p ≠ p−1` + `x ↦ x^{e²}` 単射 |
| `\|T\| ≥ (Q−3)/4 ≥ 6 ≥ 4` | `card_paleySet_lower` (`p ↦ p−1` で `T ≅ paleySet`) |
| swap の成分反転 (§4) | `χ(−1) = −1` の帰結 |

equidistribution・Weil 評価・Davenport・鳩の巣は**最終版では一切使わない**。

## 2. Part I — (B2)-elim: 衝突 1 個で witness は死ぬ [Lean 済]

正本 = [`appC_problem1_pair_composition.md`](appC_problem1_pair_composition.md) §9。

> **定理 I (`false_of_collisionPair`).** `q` 素数 ≠ 3・奇、標準仮定の下、衝突
> `CollisionPair (S, S′)` が 1 つでも存在すれば矛盾。トレース条件・span 条件・
> `e` の exotic 性・`3 mod q` の位数、いずれも不要。

証明 (5 手):

1. **正規形 (3′)**: 衝突関係式で `v := δz^e` と置換すると
   `∀v ∈ U: a(v)·b(Sv^e)·a(v)⁻¹ = b(S′v^e)` (`S = K(p)δ^{−e}`, `S′ = K(r)δ^{−e}`)。
   この形の対を **`ConjPair (s, s′)`** と呼ぶ。加法的・𝔽₃-線形で、
   **graph 性** `ConjPair (0, x) ⟹ x = 0` (`b` 単射; `ConjPair.right_eq_zero`)。
2. **(K-frob)**: 標数 3 で `p³ − 1 = (p−1)³` ⟹ Frobenius twist `(S^{3^j}, S′^{3^j})` も
   ConjPair。加法性と合わせ `ConjPair (c.S, c.S′)` ∀`c ∈ 𝔽₃[x]` (Frobenius 加群作用;
   `conjPair_aeval_of_collisionPair`)。
3. **Ann 包含 + 巡回性**: graph 性より `c.S = 0 ⟹ c.S′ = 0`。Frobenius の最小多項式 =
   `x^q − 1` (Dedekind 独立性) ⟹ `F` は `𝔽₃[x]/(x^q−1)` の正則表現 (multiplicity-free)
   ⟹ Ann 包含から **`S′ = a₀.S`** なる `a₀` が存在
   (`FrobeniusCyclicModule.lean`: `minpoly_frobEnd` / `exists_frobenius_cyclic_vector` /
   `exists_aeval_frobEnd_eq_of_forall_imp`)。
4. **chain reversal C3** (`ConjPair.chain`): 標数 3 で `a(v)² = a(−v) = a(v)⁻¹` なので
   `ConjPair (s, s′) ∧ ConjPair (s′, s″) ⟹ ConjPair (s″, s)`。これを
   `(S, a₀.S), (a₀.S, a₀².S)` に適用 ⟹ `ConjPair (a₀².S, S)`; 対 `(a₀².S, a₀³.S)` との
   差 + graph 性 ⟹ **`a₀³.S = S`**。
5. **radical 降冪**: `a₀³ − 1 = (a₀ − 1)³` (標数 3)、`x^q − 1` は `q ≠ 3` で squarefree
   ⟹ `Ann(S)` は radical (`aeval_frobEnd_eq_zero_of_pow`) ⟹ `(a₀ − 1).S = 0` ⟹
   **`S′ = S`** ⟹ 不動点原理 (`false_of_conjPair_self`: 比 1 の非零 pair は
   `Commute(a(1), b(1)) = Commute(x, x^g)` に潰れ `not_commute_conj` に矛盾)。∎

**一般化 (loop 用の入口)**: 手 3–5 は衝突を経由せず、**Frobenius 閉な ConjPair 族**
`{(S^{3^j}, S′^{3^j})}_j` (`S ≠ 0`) さえあれば同じ矛盾が出る =
**`false_of_conjPair_frobenius_family`** (family capstone、Lean 済)。Part II の loop kill は
すべてここに流し込む。

## 3. Part II — skew calculus: 衝突なしの辺・合成・loop ⟹ kill [紙上]

正本 = [`appC_problem1_skew_calculus.md`](appC_problem1_skew_calculus.md) §1–§3。
衝突の存在 (= (B1)) を**仮定せずに** witness を攻撃する calculus。

**点関係式 (P)** (基本関係式の `a(z) = a(pz)·a((p−1)z)⁻¹` 展開; ∀p ∈ T, z ∈ U):

> (P) `a(z) = b(−p^e z^e) · d(K(p) z^{e²}) · b((p−1)^e z^e)`

**skew 辺 (E)** (2 本の (P) の消去; 任意の順序対 `(p, r) ∈ T²`, `p ≠ r` —
**`D(p) = D(r)` は要求しない**):

> (E) `b(δ₀ z^e) · d(K(p) z^{e²}) · b(−δ₁ z^e) = d(K(r) z^{e²})` (∀z ∈ U)
> `δ₀ := r^e − p^e`, `δ₁ := (r−1)^e − (p−1)^e` (どちらも ≠ 0)

辺データ `(A, B; X, Y) = (δ₀, δ₁; K(p), K(r))`、**比** `ρ := δ₁/δ₀`。
`ρ = 1 ⟺ 衝突` (衝突は「比 1 の辺」として埋め込まれる)。反転 (群逆元) =
`(B, A; −X, −Y)`。**swap 辺** `(r, p)` = `(−A, −B; Y, X)` — `ρ` 不変で、
`χ(−1) = −1` ゆえ**符号成分 `c := χ(δ₀)` が反転する** (成分反転)。

**合成と閉条件**:

- 再スケール `z ↦ tz` (`t ∈ U`): `(At^e, Bt^e; Xt^{e²}, Yt^{e²})`。
- 合成 (`B₁ = A₂` で内側の `b` が相殺): `(A₁, B₂; X₁+X₂, Y₁+Y₂)`。
- k 辺の連鎖: 逐次 `t_{i+1}^e = Bᵢtᵢ^e / A_{i+1}` が可解 ⟺ **符号条件**
  `χ(Bᵢ) = χ(A_{i+1})` (t 非依存)。**閉条件はちょうど `∏Bᵢ = ∏Aᵢ`** (閉じの符号は
  `∏χ(ρᵢ) = 1` で自動)。閉じた loop の結果:

> `b(A z^e) · d(X_tot z^{e²}) · b(−A z^e) = d(Y_tot z^{e²})` (∀z ∈ U)
> `X_tot = Σ Xᵢ tᵢ^{e²}`, `Y_tot = Σ Yᵢ tᵢ^{e²}`

**loop ⟹ kill**: 閉 loop の重みが `(X_tot, Y_tot) ≠ (0,0)` なら:

- 片方だけ 0 ⟹ 層の単射性で即矛盾 (例: `X_tot = 0` なら `1 = d(Y_tot z^{e²})`)。
- `X_tot = Y_tot ≠ 0` ⟹ 比 1 ⟹ `false_of_conjPair_self` 直行。
- 一般 (`X_tot ≠ Y_tot`、両方 ≠ 0) ⟹ `χ(A) = ±1` に応じ layer-(1,2) の
  `ConjPair¹(X_tot A^{−e}, Y_tot A^{−e})` またはその逆向き・負号版 ⟹ `g`-共役 1 発で標準
  `ConjPair data e s s′`。**cube-loop** (全辺を `(pᵢ³, rᵢ³)`・`tᵢ³` に置換; `T` は
  Frobenius 安定、積条件・符号は cube 不変、重みは freshman dream で `(X_tot³, Y_tot³)`;
  向きの分岐は `χ(A)` が支配し cube 不変なので族全体で整合) が **Frobenius 族**
  `ConjPair (s^{3^j}, s′^{3^j})` を供給 ⟹ **`false_of_conjPair_frobenius_family`** ⟹ 死。

敵の自己相殺 loop (自己合成・自由 3-閉路・`e ∘ rev(e)`・swap 直接 2-loop の符号ブロック)
は完全に分類済で、以下の議論はそれらに依存しない (skew note §5)。

## 4. Part III — endgame: κ-共謀の反駁 [紙上]

正本 = skew note §6–§6.2 + lens A/B + assembly 監査 (§8)。

### 4.1 共謀と slot 定数 κ

Part II により、witness が生き残る ⟺ **共謀** = 「閉じられるすべての loop の重みが
`(0,0)`」。辺は **slot** `(ρ-クラス, 符号成分 c = χ(δ₀))` に分類される。swap が `ρ` を保ち
成分を反転するので、**実現している ρ-クラスの両成分は常に同時に非空** (swap population)。

- **same-slot 2-loop** `e ∘ rev(e′)` (同 slot の相異なる 2 辺) は常に合法 (同 `ρ`・同成分
  ⟹ 接合符号 `χ(δ₁) = χ(δ₁′)` も閉条件 `ρρ′⁻¹ = 1` も自動) で、重みの X 成分 =
  `K(p) − K(p′)(δ₁/δ₁′)^e`。共謀 ⟹ **`κ := K(p)δ₁^{−e}` が各 slot 上定数**。
  同時に `κ′ := K(r)δ₁^{−e}` も定数で、恒等式 **`κ′(p,r) = −κ(r,p)`** より κ′ は κ の
  swap-slot 値で決まる (Y 側の消滅条件は成分 `−c` での X 側条件と同値 — 新情報なし)。
  singleton slot でも κ は自明に well-defined なので、**鳩の巣 (同 slot 2 辺の存在) は
  以降不要**。`κ̂ := K(p)δ₀^{−e} = κρ^e` と書く。

### 4.2 可換子 loop と交換関係 (EX)

実現クラス `ρ, σ` (`ρ ≠ σ`) と成分 `c₁ ∈ {±}` に対し、**4 脚の可換子 loop**
(高さ `v → ρv → σρv → σv → v`) を組む。脚ごとの slot・寄与:

| 脚 | 向き | slot | 入口高さ | 重み寄与 (X 側) |
|---|---|---|---|---|
| `g₁` | 前進 | `(ρ, c₁)` | `v` | `+κ̂(ρ, c₁)·v^e` |
| `g₂` | 前進 | `(σ, χ(ρ)c₁)` | `ρv` | `+κ̂(σ, χ(ρ)c₁)·(ρv)^e` |
| `g₃` | 後退 | `(ρ, χ(σ)c₁)` | `σρv` | `−κ(ρ, χ(σ)c₁)·(σρv)^e` |
| `g₄` | 後退 | `(σ, c₁)` | `σv` | `−κ(σ, c₁)·(σv)^e` |

(前進脚は slot `(ρ,c)` で入口符号 `χ(v) = c` を要求し `v ↦ ρv`、後退脚は逆辺で入口符号
`χ(w) = χ(ρ)c`、`w ↦ w/ρ`。) 接合符号条件は表の 4 つの slot 条件に正確に帰着し、閉条件は
`ρσρ⁻¹σ⁻¹ = 1` で**恒等的に**閉じる。swap population により **4 つの slot は任意の実現
クラス対・両方の `c₁`・全 4 符号セクター `(χρ, χσ)` で常に非空** — loop は無条件に合法
(辺の再利用も可なので slot の辺数は問わない)。共謀 ⟹ 重み消滅。`v^e` で割り整理すると:

> **(EX)** `κ(ρ,c)ρ^e − κ(σ,c)σ^e = σ^eρ^e·[κ(ρ, χ(σ)c) − κ(σ, χ(ρ)c)]`

**⚠ どの脚がどの κ-項か** (lens A の指摘による明確化): 左辺の `κ(ρ,c)ρ^e = κ̂(ρ,c)` は
**前進 ρ-脚 `g₁`**、左辺の `κ(σ,c)σ^e` は**後退 σ-脚 `g₄`** 由来。右辺の `κ(ρ,χ(σ)c)` は
**後退 ρ-脚 `g₃`**、右辺の `κ(σ,χ(ρ)c)` は**前進 σ-脚 `g₂`** 由来。相手クラスの符号が
`−1` のとき、同じクラスの前進脚と後退脚は**別の slot** を読む — ここの取り違えが §6.1
初稿の捻れミスの原因だった。

### 4.3 (EX) ⟹ master formula (anchor 論法による一意性)

**master 族**: 定数 `λ₊, λ₋` により `κ̂(ρ, c) = λ_c − λ_{χ(ρ)c}·ρ^e`。master は (EX) を
全 4 セクターで恒等的に満たす (記号計算 + 数値 8000/8000)。逆に、実現クラスがすべて
`ρ ≠ 1` (step 1 通過後) で単集合 `{−1}` でない (step 4 で分岐) とき、(EX) の解は
master 族**のみ**である — **anchor 論法**:

1. **`χ = +1` の実現クラス `ρ₀` がある場合**: `χρ = χσ = +1` の対では (EX) が
   `κ̂(ρ,c)(1−σ^e) = κ̂(σ,c)(1−ρ^e)` に整理される。`ρ ≠ 1 ⟹ 1−ρ^e ≠ 0`
   (`x ↦ x^e` 全単射; 同じ理由で `ρ^e = σ^e ⟹ ρ = σ`) なので
   **`λ_c := κ̂(ρ₀, c)/(1 − ρ₀^e)`** と anchor すると、全 +クラスで
   `κ̂(ρ,c) = λ_c(1−ρ^e)` (= master の +形)。次に anchor と任意の −クラス `σ` の混合対の
   (EX) が各 −クラスを **`κ̂(σ,c) = λ_c − λ_{−c}σ^e`** に pin する。
2. **実現クラスが全部 `χ = −1` (2 クラス以上)**: (EX) は和・差に分離し
   `s(ρ) := κ̂(ρ,+) + κ̂(ρ,−) = Σ̄(1−ρ^e)`、`d(ρ) := κ̂(ρ,+) − κ̂(ρ,−) = Δ(1+ρ^e)`
   (標数 3 で 2 = −1 可逆)。anchor `σ₀ ∉ {±1}` から `(λ₊, λ₋)` を解く — 係数行列式
   `1 − σ₀^{2e} ≠ 0` (`σ₀^{2e} = 1 ⟹ σ₀^e = ±1 ⟹ σ₀ = ±1`、`e` 奇)。`1+ρ^e = 0` は
   `ρ = −1` のみで、そこでは `d(−1) = 0` が第 2 クラスとの (EX) から整合的に強制される。
3. **単集合 `{ρ₀}`, `ρ₀ ∉ {1, −1}`**: (EX) は空虚だが一意性は不要 — master 写像
   `(λ₊,λ₋) ↦ (κ̂(ρ₀,+), κ̂(ρ₀,−))` が**全単射** (`χρ₀ = +1` なら det `(1−ρ₀^e)²`、
   `χρ₀ = −1` なら det `1−ρ₀^{2e}`、どちらも ≠ 0) なので λ が存在して master が成立。
4. **唯一の例外 = 単集合 `{−1}`**: `ρ₀ = −1` では master 像が対角
   `κ̂(+) = κ̂(−) = Σ̄` (dim 1) に潰れ、(EX) の解空間 (dim 2) を尽くさない。
   ⟹ この人口だけは master 以前に別途殺す (木の step 4)。

master を `K` に戻すと (`K(p) = κ̂(ρ,c)δ₀^e`、`χ(ρ)c = χ(δ₁)`):

> **MASTER**: `K(p) = λ_{χ(δ₀)}·δ₀^e − λ_{χ(δ₁)}·δ₁^e` (∀(p, r) ∈ T², p ≠ r)

### 4.4 枝の撃破

`Δ := λ₊ − λ₋`、`Σ̄ := λ₊ + λ₋`、`μ_c := λ_c − λ_c³` (`μ_c = 0 ⟺ λ_c ∈ 𝔽₃`)。
辺の**パターン** = `(χ(δ₀), χ(δ₁))`。swap は `(+,+) ↔ (−,−)`、`(+,−) ↔ (−,+)` を交換。

- **Δ = 0**: master が符号自由 `K(p) = λ(δ₀^e − δ₁^e)` になり、swap 辺に適用すると
  `K(r) = λ((−δ₀)^e − (−δ₁)^e) = −K(p)` (`e` 奇)。相異なる 3 点で
  `K(p) = −K(r), K(r) = −K(s), K(p) = −K(s)` ⟹ `2K(s) = 0`、`2 = −1` 可逆 ⟹
  `K(s) = 0` — `K ≠ 0` に矛盾。死。
- **Σ̄ = 0**: master の差 `K(p) − K(r) = Σ̄(δ₀^e − δ₁^e)` (指示関数の相殺に swap の
  成分反転 = `χ(−1) = −1` と `e` 奇を使う) が 0 ⟹ **`K` は `T` 上定数** ⟹
  **e²-衝突ブリッジで死**。glue chain を明示すると:
  `K` 定数 ⟹ (`p ∈ T ⟺ p−1 ∈ paleySet`、`K(p) = −powDiff (e·e) (p−1)` の翻訳で)
  相異なる `p₁, p₂ ∈ T` の像 `a := p₁−1 ≠ b := p₂−1 ∈ paleySet` で
  `powDiff (E·E) a = powDiff (E·E) b` ⟹ **`exists_paley_collision_pow_mul_down`**
  (下向き `E ↔ E²` 共役、`z^{e⁴} = z^e`) が `powDiff E c = powDiff E d` なる
  `c ≠ d ∈ paleySet` を返す ⟹ `pow_injective_of_cube` で `δ ≠ 0` ⟹
  **`exists_collisionPair_of_sub_ne_zero`** が向き (`±δ` のちょうど一方が平方、
  `χ(−1) = −1`) を処理して `CollisionPair` に包む ⟹ **`false_of_collisionPair`** (Part I)。
  死。(部品は全 Lean 済; 合成の 1 補題化は Lean 化残作業。)
- **Frobenius 量子化 (`μ ≠ 0` の反駁)**: `T` は Frobenius 安定 (`(p−1)³ = p³−1`)、
  `δᵢ(p³,r³) = δᵢ³`、`K(p³) = K(p)³`、`χ` は cube 不変。master を `(p³, r³)` に適用した式
  から master の cube (freshman dream) を引くと、各辺で
  **`μ_{χ(δ₀)}·δ₀^{3e} = μ_{χ(δ₁)}·δ₁^{3e}`**。ある `μ_c ≠ 0` なら:
  - **同符号パターン辺** (`χδ₀ = χδ₁ = c`) があれば `ρ^{3e} = 1` ⟹ `ρ = 1`
    (`gcd(3e, Q−1) = 1`) = 衝突 ⟹ Part I で死。swap が `(+,+) ↔ (−,−)` を対にするので、
    **どちらかの `μ` が非零なら同符号辺 1 本で死ぬ**。
  - `μ` の一方だけ 0 なら混合辺は「非零 = 0」で即矛盾 ⟹ 全辺同符号 ⟹ 上で死。
  - 両方非零なら、混合辺とその swap (同 `ρ`、逆パターン) から `μ₊/μ₋ = μ₋/μ₊` ⟹
    `μ₊ = ±μ₋`。`μ₊ = μ₋` は混合辺で `ρ = 1` を強いる (`χ(1) = +1` で不可能) ⟹
    `μ₊ = −μ₋` かつ**全混合辺が `ρ = −1`** (`(−1)^{3e} = −1`、`3e`-冪の単射性)。
    生き残りは「全辺混合・`δ₁ = −δ₀` 大域」の世界だが、そこでは master が
    `K(p) = Σ̄·δ₀^e` に退化 (step Σ̄=0 は処理済なので `Σ̄ ≠ 0`) ⟹ `δ₀(p,r)^e` が
    `r` に依らず定数 ⟹ `e`-冪単射性で `r` が `p` ごとに一意 ⟹ `|T| − 1 ≤ 1`、
    `|T| ≥ 3` に矛盾。死。
  ⟹ **`λ₊, λ₋ ∈ 𝔽₃`**。
- **𝔽₃ の残候補**: `Δ, Σ̄ ≠ 0` を満たすのは
  **`(λ₊, λ₋) ∈ {(1,0), (−1,0), (0,1), (0,−1)}` の 4 本のみ**
  (9 対から Δ=0 の 3 対と Σ̄=0 の 2 対を除く)。**致死パターンは候補依存**:
  - `(±1, 0)` (`λ₋ = 0`): **(−,−)-辺**が master で `K(p) = λ₋(δ₀^e − δ₁^e) = 0` を
    強制 — `K ≠ 0` に矛盾、即死。
  - `(0, ±1)` (`λ₊ = 0`): **(+,+)-辺**が同様に `K(p) = 0` を強制、即死。
  - もう一方の同符号パターンは**その swap が致死パターン**になる (`(+,+)` の swap は
    `(−,−)`、逆も然り) ⟹ **4 候補とも、同符号辺が 1 本でもあれば死**。
  - 残るのは全辺混合の世界: 固定した `p` から出る各辺は `(+,−)` か `(−,+)`。
    `(+,−)`-辺は `K(p) = ±δ₀^e`、`(−,+)`-辺は `K(p) = ∓δ₁^e` を強制し、それぞれ
    `e`-冪単射性で `δ₀` (resp. `δ₁`) ゆえ **`r` を `p` ごとに一意に pin** ⟹ `p` の
    out-degree `|T| − 1 ≤ 2`。しかし `|T| ≥ 4` ⟹ `|T| − 1 ≥ 3` — 矛盾。死。
    (パターン人口の仮説も「G-定数型」残渣恒等式も不要。)

## 5. ケース木の総覧 (主定理の証明)

`q = 3` / `e ∈ ⟨3⟩` は定理 1 (§0)。以下 `q ≠ 3`、witness を仮定して矛盾を導く:

1. **ρ = 1 クラスが実現** (= 衝突が存在): **Part I** `false_of_collisionPair` で死 [Lean 済]。
   以下、衝突なし (全実現クラス `ρ ≠ 1`)。
2. **非退化重みの閉 loop が 1 つでもある**: **Part II** の cube-loop 経由で
   `false_of_conjPair_frobenius_family` で死 [入口 Lean 済]。以下、**共謀** (全 loop 消滅)。
3. 共謀 ⟹ **same-slot κ-定数** (2-loop、常に合法; singleton slot は自明) [§4.1]。
4. **実現クラスが単集合 `{−1}`**: fwd-fwd 2-loop `e ∘ swap(e)` (接合は `χρ = −1`、閉条件は
   `ρ² = 1` — **`ρ = −1` でのみ合法**な特殊 loop) の重みが
   `X_tot = Y_tot = (K(p) + K(r))·t^{e²}` ⟹ 共謀が全対に `K(p) = −K(r)` を強制 ⟹
   3 点 + `2 = −1` 可逆で `K ≡ 0` — 矛盾。死。
5. それ以外: **可換子 loop が任意の実現クラス対・両成分・全 4 セクターで合法** [§4.2]
   ⟹ (EX) ⟹ **anchor 論法で master formula が T² 全体で成立** [§4.3]。
6. **master の枝** [§4.4]: `Δ = 0` ⟹ 3 点矛盾 / `Σ̄ = 0` ⟹ `K` 定数 ⟹ e²-衝突 ⟹
   下向き共役ブリッジ ⟹ step 1 で死 / **`μ ≠ 0`** ⟹ 同符号辺は `ρ = 1` 衝突・全混合世界は
   `ρ ≡ −1` 退化で out-degree 矛盾 ⟹ **`λ₊, λ₋ ∈ 𝔽₃`**。
7. **𝔽₃ 残 4 候補** `(±1,0), (0,±1)`: 同符号辺 1 本で死 (致死パターンは候補依存、swap が
   補完) / 全混合世界は 2 パターン各 1 本の pin で out-degree `≤ 2` vs `|T| − 1 ≥ 3` — 矛盾。死。

全ケースで矛盾 ⟹ **witness は存在しない**。定理 1 と合わせて主定理が従う。∎

**使用仮説の総目録** (§1 の表がすべて; 再掲): `χ(−1) = −1`・`e` 奇・`z^{e³} = z`
(⟹ `e`/`e²`/`3e`-冪の全単射性)・`K ≠ 0`・`|T| ≥ 4`・swap の成分反転 (χ(−1) = −1 の帰結)。
equidistribution・Weil・Davenport・鳩の巣は不要。

## 6. 帰結

- **BG App.C Problem 1 (Péterfalvi 1993) は否定的に全面解決** (紙上)。(B1) = 「衝突が
  存在する」の証明は**不要になった** (APN 分類予想への依存も消滅)。
- per-q 証明書・trace 判定・N1/N2/N3・閉包実験・剛性ルートは certificate として
  すべて superseded (定理としては残る)。

## 7. Lean 検証状況

**Lean 済** (すべて axiom-clean・AxiomsCheck 登録済; 名前は grep で実在確認済 2026-08-13):

| 部品 | Lean | 所在 |
|---|---|---|
| 定理 1 (`e ∈ ⟨3⟩`) | `false_of_centralizing` | `OddOrder/BG/AppC_Problem1.lean` |
| 定理 2 (witness 非可解) | `not_isSolvable_of_exp` | `OddOrder/BG/AppC_Problem1Lattice.lean` |
| 層・基本関係式 | `layerFieldHom` / `layered_relation_field` | 同上 |
| `\|T\| ≥ (Q−3)/4` | `card_paleySet_lower` | `OddOrder/Algebra/PaleySpanning.lean` |
| **Part I capstone** | **`false_of_collisionPair`** | `OddOrder/BG/AppC_Problem1PairComposition.lean` |
| family capstone (loop kill 入口) | `false_of_conjPair_frobenius_family` | 同上 |
| chain reversal C3 | `ConjPair.chain` | 同上 |
| 不動点原理 (比 1) | `false_of_conjPair_self` | 同上 |
| graph 性 (K2) | `ConjPair.right_eq_zero` | 同上 |
| Frobenius 巡回加群 | `frobEnd` / `minpoly_frobEnd` / `exists_frobenius_cyclic_vector` / `exists_aeval_frobEnd_eq_of_forall_imp` / `aeval_frobEnd_eq_zero_of_pow` | `OddOrder/Algebra/FrobeniusCyclicModule.lean` |
| 下向き `E ↔ E²` 共役 | `exists_paley_collision_pow_mul_down` | `OddOrder/Algebra/PaleySpanning.lean` |
| 衝突 packaging (`δ ∈ U` 向き) | `exists_collisionPair_of_sub_ne_zero` | `OddOrder/BG/AppC_Problem1Trace.lean` |
| `e`-冪単射性 | `pow_injective_of_cube` | `OddOrder/Algebra/PaleySpanning.lean` |

**Part II–III の Lean 化 (2026-08-13 夜に完了、issue 0181)** — 新 leaf
`AppC_Problem1SkewCalculus.lean` + `AppC_Problem1SkewEndgame.lean`、全 axiom-clean:

| 部品 | Lean |
|---|---|
| skew 辺・groupoid ops・graph・loop ⟹ ConjPair | `SkewPair` / `skewPair_edge` / `SkewPair.rev`/`comp`/`rescale`/`conjPair_of_self(_neg)` |
| loop ⟹ kill (Frobenius 族) | `FrobFam` calculus + `false_of_skewPair_self_frobenius_family` |
| same-slot 2-loop ⟹ κ-定数 (step 3) | `false_of_proportional_edges` / `weights_proportional_of_proportional_edges` |
| fwd-fwd 2-loop・step 4 | `false_of_antipodal_edge` / `false_of_three_antipodal` |
| leg supply・可換子 loop・(EX) (step 5) | `FrobFam.leg_fwd`/`leg_swap`/`leg_resolved` / `exchange_relation` (8 セクター一括) |
| anchor 論法 ⟹ master (§4.3) | `exists_masterFormula_of_plus_anchor` / `_minus_anchor` / `_of_no_collision` |
| 枝 Δ=0 / Σ̄=0 (+e²-衝突 glue の 1 補題化) | `false_of_masterFormula_delta_zero` / `_sigma_zero` |
| 枝 μ≠0 / λ∈𝔽₃ (§4.4) | `false_of_masterFormula_mu_ne_zero` / `_cubic` |
| **capstone (`q ≠ 3` 全指数)** | **`false_of_exotic`** |

形式化で見つかった簡約 (紙の証明の改良): (i) layer (0,1) 構築で loop ⟹ ConjPair が
g-共役なしの純代入になる。(ii) 具体対 (EX)(X, anchor) は χ(anchor 比) = +1 だけで
全 target に合法 — 紙の 2 段 pinning (＋クラス → −クラス) は不要。(iii) (Q) + swap-(Q)
の和で μ₊ + μ₋ = 0 が人口場合分けなしに出る。(iv) 3-冪単射は char 3 の Frobenius
単射性から無料 (gcd(3e, Q−1) = 1 の供給不要)。

**統合 glue (2026-08-13 深夜に完了)**:

| 部品 | Lean |
|---|---|
| 指数抽出 (§1 の導出表: 冪写像・奇代表・CRT) | `exists_odd_cube_exponent` (`AppC_Problem1Exponent.lean`) |
| `q` 奇 ⟸ 条件 (A) | `q_odd_of_conditionA` |
| witness 単独の排除 (`q ≠ 3`) | `false_of_witness` |
| 定理 1 の `e ∈ ⟨3⟩` 側 (twisted engine + Frobenius 移送 spanning) | `false_of_frobenius_exponent` |
| **最終形 (全 `q`)** | **`hypothesisB_false`** |

⚠ 註: 定理 1 の Lean 化はもともと `false_of_centralizing` (`e = 1` 側) のみだった —
`e = 3^j` 側は「σ の twist で e が変わる」わけではなく (hexp の `e` は `(g, U)` に
内在的)、**σ_e = Frobenius 冪の加法性**で twisted engine
(`commute_conj_of_le_closure_twisted`、関数 + P 上乗法性へ一般化) を直接回す。

## 8. 検証記録

**敵対的検証 6 レンズ (すべて 2026-08-13、全 CONFIRMED・fatal 0)**:

| # | 対象 | 方式 | 判定 |
|---|---|---|---|
| 1–3 | skew calculus Steps 1–6 (群計算 / 組合せ / 整合性・行き止まり照合) | 独立再導出 + `lens2_verify.py` / `lens3_verify.py` (q = 7 悉皆) | CONFIRMED |
| 4 (lens A) | 可換子 loop 合法性・(EX) 解空間 (rank 解析込み) | `lensA_commutator_verify.py`: 全 8 (セクター, c₁) 組合せ × 両指数 4000/4000、負対照 2000/2000 blocked | CONFIRMED・nit 4 (§4.2 の per-leg 表・単集合 {−1} 例外はここ由来) |
| 5 (lens B) | 枝撃破・Frobenius 量子化 | `lensB_verify.py`: synthetic master データで全恒等式 (S1–S6) | CONFIRMED・nit 6 (ρ-confinement 副枝と G-定数残渣の**閉鎖** = 強化 2 件を含む) |
| 6 | **最終 assembly 監査** (effort max) | 量化子構造・循環なし・全退化人口 walk・e² glue の end-to-end 数値検証・独立スポットチェック `assembly_spotcheck.py` 45/45 × 2 指数 | CONFIRMED・nit 6 (§4.3 anchor 論法・§4.4 候補依存パターンはここ由来) |

Part I ((B2)-elim) は別途 3 レンズ (group / module / history) で敵対的検証済
(pair_composition note §9; `q = 3` での反例 `a₀ = x` により squarefree の必要箇所が正確で
あることの確認、GF(3⁵) 243² 悉皆の Ann 包含検証を含む)。

**数値的証拠 (GF(3⁷)、両 exotic 指数 E = 151, 941)**:

- same-slot 対 **10,154,844 / 10,146,444 件の悉皆検証で both-zero = 0 — kill 率 100%**。
  `ρ` は全 2186 値を被覆 (q = 7 の事実; 証明では仮定しない)。`ρ = 1` 辺 140 = 衝突 70×2、
  `ρ = −1` 辺 112。
- 可換子 loop 重み公式: literal chain composer と **1010/1010** (`endgame_check.py`;
  (+,+) セクター) + **4000/4000** (lens A; 全 8 セクター/成分組合せ)。重み恒等式は
  体論の恒等式として紙上再導出済 (数値依存なし)。
- master の最良 λ-fit **3/2000** (偶然水準)、𝔽₃-候補 9 本すべて **≤ 5/500**、dream-world
  恒等式の defect **500/500 非零** — 共謀は q = 7 で全滅 (木の予測 step どおりに死ぬことも
  spot-check 済)。
- Part I 側: 閉包実験で全 **101,592/101,592 衝突** (q = 7: 140、q = 13: 50,726×2) が
  例外なく kill。
- e²-衝突ブリッジ: q = 7 の実 e²-衝突で pipeline 全段 (像の相異・Paley 所属・E-衝突・
  `δ ≠ 0`・向き) を両指数 end-to-end 検証。

**スクリプト正本 = [`notes/meta/c/`](../meta/c/)**: `skew_cycles.py` (辺 census・閉包)、
`endgame_check.py` (重み公式・master fit)、`lensA_commutator_verify.py`、`lensB_verify.py`、
`chain_closure.py` / `collision_impact.py` (Part I 閉包実験)、`gf3_collision.c` (衝突探索)。

## 9. スコープの正直な申告と残作業

- **2026-08-13 深夜: 完全機械検証**。`hypothesisB_false` により、本文書の主定理
  (§0) は**そのままの一般性で** Lean 検証済となった: p = 3 の witness は全 `q` で
  存在しない、`G` 無限可、追加仮定ゼロ、axiom-clean。紙上のみの残作業は無い。
- witness 構造の基礎事実 (定理 1・定理 2・層・基本関係式・`|T|` 下界) と木の全 kill 入口
  (`false_of_collisionPair` / `false_of_conjPair_frobenius_family` / `false_of_conjPair_self` /
  ブリッジ部品) は Lean 済なので、残る形式化は**体の中の有限計算** (辺 calculus・可換子
  loop・master 崩壊・枝撃破) に閉じており、群論側の新規作業はない。
- Lean 化の設計・進捗は [issue 0181](../../issues/0181-skew-calculus-lean-formalization.md)
  (親 = [issue 0180](../../issues/0180-bg-appc-problem1-p-eq-three.md)) で追跡。
