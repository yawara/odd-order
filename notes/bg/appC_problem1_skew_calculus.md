# skew-pair calculus — 衝突仮定なしの witness 攻撃 ((B1) の迂回プログラム) — 2026-08-13

[issue 0180](../../issues/0180-bg-appc-problem1-p-eq-three.md)。(B2) 完全消去
([`appC_problem1_pair_composition.md`](appC_problem1_pair_composition.md) §9) の直後に発見。
**衝突 (CollisionPair) の存在 = (B1) を仮定せずに** hypothesis (B) の witness を攻撃する
calculus。敵対的検証 3 レンズ (群計算 / 組合せ / 整合性・行き止まり照合) **全 CONFIRMED・
fatal 0** (2026-08-13、q = 7 で悉皆数値検証込み)。Steps 1–6 は確立、Step 7 (endgame) が
残作業。

記法: `a, b, d` = layer 0/1/2 (`layerFieldHom`、単射・加法的、`g := conjGen` 共役で
`g·layer_{i+1}(x)·g⁻¹ = layer_i(x)`、`g³ = 1`)。基本関係式 (`layered_relation_field`):
`d(u^{e²})·b(u^e)·a(u) = 1` (∀u ∈ U)。`K(p) := (p−1)^{e²} − p^{e²} ≠ 0`。

## 1. 点関係式と skew 辺 (衝突不要) [検証済]

任意の `p ∈ T`, `z ∈ U`:

> (P) `a(z) = b(−p^e z^e) · d(K(p) z^{e²}) · b((p−1)^e z^e)`

任意の順序対 `(p, r) ∈ T²`, `p ≠ r` — **D(p) = D(r) は要求しない**:

> (E) `b(δ₀ z^e) · d(K(p) z^{e²}) · b(−δ₁ z^e) = d(K(r) z^{e²})` (∀z ∈ U)
> `δ₀ = r^e − p^e`, `δ₁ = (r−1)^e − (p−1)^e` (どちらも ≠ 0)

辺データ `(A, B; X, Y) = (δ₀, δ₁; K(p), K(r))`、比 `ρ := δ₁/δ₀`。
`ρ = 1 ⟺ D(p) = D(r)` (衝突は「比 1 の辺」として埋め込まれる)。
反転 (群逆元) = `(B, A; −X, −Y)`。swap 辺 `(r,p)` = `(−A, −B; Y, X)` (ρ 不変)。

## 2. 合成・閉条件 [検証済]

- 再スケール `z ↦ tz` (`t ∈ U`): `(At^e, Bt^e; Xt^{e²}, Yt^{e²})`。
- 合成 (`B₁ = A₂` で内側 b が相殺): `(A₁, B₂; X₁+X₂, Y₁+Y₂)`。
- k 辺の連鎖 + 閉じ: 逐次 `t_{i+1}^e = Bᵢtᵢ^e/A_{i+1}` (可解 ⟺ 符号条件
  `χ(Bᵢ) = χ(A_{i+1})`、t 非依存)。閉条件は**ちょうど** `∏Bᵢ = ∏Aᵢ` (閉じの符号は
  `∏χ(ρᵢ) = χ(1) = 1` で自動)。結果 (loop):

> `b(A z^e) · d(X_tot z^{e²}) · b(−A z^e) = d(Y_tot z^{e²})` (∀z ∈ U)
> `X_tot = Σ Xᵢ tᵢ^{e²}`, `Y_tot = Σ Yᵢ tᵢ^{e²}`

## 3. loop ⟹ kill [検証済 + Lean 入口 merge 済]

`(X_tot, Y_tot) ≠ (0,0)` の閉 loop から:
片方 0 ⟹ 層単射で即矛盾。両方 ≠ 0 ⟹ `χ(A) = ±1` に応じ layer-(1,2) の
`ConjPair¹(XA^{−e}, YA^{−e})` またはその逆向き・負号版 (負号は `ConjPair.neg` で吸収)
⟹ `g`-共役 1 発で標準 `ConjPair data e s s′` ⟹ **cube-loop** (全辺 `(pᵢ³, rᵢ³)`、
`tᵢ³`; 積条件・符号 cube 不変、重み = freshman dream で `(X³, Y³)`) が Frobenius 族
`ConjPair (s^{3^j}, s′^{3^j})` を供給 ⟹
**`false_of_conjPair_frobenius_family`** (2026-08-13 Lean 化・axiom-clean、
`AppC_Problem1PairComposition.lean`; (B2)-elim capstone の CollisionPair 非依存の一般化)
⟹ **witness 死**。`X_tot = Y_tot` の loop は `s = s′` で `false_of_conjPair_self` 直行
(bonus kill)。

## 4. 存在 — 鳩の巣は無条件 [検証済]

- 辺 `|T|(|T|−1) ≈ Q²/16` 本、(ρ-クラス × 符号成分) の slot ≤ 2(Q−1) 個 ⟹ ある slot に
  `≥ Q/32` 本 (Q > 32 で > 1) — **無条件**。
- クラスの符号成分は `(χδ₀, χδ₁) = (c, χ(ρ)c)` の 2 つで、swap が固定点なしに交換 ⟹
  **両成分は常に同数・同時に非空**。
- 同 slot の相異なる 2 辺 `e, e′` で `e ∘ rev(e′)` は自動的に閉じ (ρρ⁻¹ = 1、符号 ✓)、
  重み `X = K(p) − K(p′)u`, `Y = K(r) − K(p′... K(r′))u`, `u = (δ₁e/δ₁e′)^e`。
  (同一辺との反転合成 `e∘rev(e)` は恒等的に (0,0) — 除外必須。)

**数値 (GF(3⁷), 両 exotic 指数, 悉皆)**: ρ は全 2186 値を被覆 (q=7 の事実; 一般 q では
仮定しない)。**same-slot 対 10,154,844 / 10,146,444 件の悉皆検証で both-zero = 0 —
kill 率 100%**。ρ=1 辺 140 = 衝突×2 と一致。

## 5. 退化機構の完全リスト [検証済 — すべて回避]

敵が自己相殺する loop: (i) 自己合成 (`Σ_{h∈H} h = 0`、非自明部分群和)、
(ii) 自由 3-閉路 `(p,r)→(p−1,r−1)→(p+1,r+1)` (`K(p)+K(p−1)+K(p+1) = 0` のテレスコープ)、
(iii) `e ∘ rev(e)` (同一辺)、(iv) swap 直接 2-loop `e ∘ rev(ē)` は**常に符号ブロック**
(連鎖比 −1 非平方)。census はすべて除外済; 既録の行き止まり (自由対合・H-座標・Sidon・
APN) への還元なし (それらは衝突の**構成**を試みて χ(−1) に阻まれた; 本 calculus の
2-loop 存在は純鳩の巣)。

## 6. endgame (残作業): κ-共謀の反駁

敵の生存 ⟺ **共謀**: すべての有効 loop の重みが (0,0)。構造 (検証済):

- 成分内 2-loop の消滅 ⟺ `κ := K(p)δ₁^{−e}` と `κ′ := K(r)δ₁^{−e}` が各 slot 上定数。
- **恒等式 `κ′(p,r) = −κ(r,p)`** ⟹ κ′ は κ の swap-slot 値で決まる。
- **成分内可積分性 (一般証明、Lens 2)**: loop の重み寄与は `κᵢ·vᵢ^e`
  (`vᵢ` = 共有線の値、ρ-等比連鎖)。κ-定数なら任意の成分内 loop はテレスコープで 0
  ⟹ 共謀は成分内で自己整合 — **反駁には slot 間をつなぐ loop が必須**。
- 相互クラス 2-loop の消滅 ⟺ 相互性 `κ(ρ⁻¹, ·) = −κ(ρ, ·)ρ^e`。
- swap-ゲージ: 各辺は swap に差し替え可 (ρ 不変・成分反転)、monodromy
  `∏χ(ρ)` = +1 で連鎖整合は常に可能。ただし成分**横断** (e と ē を同一 loop に入れる)
  には χ-積 −1 の filler が必要 — swap 直接 2-loop の符号ブロックが正確にここを守る。
- 目標: 共謀 ⟹ `K(p) = −K(r)` (∀p≠r) 型の absurdity (|T| ≥ 3 で `K ≡ 0` ⟹ K≠0 矛盾)、
  または κ-定数 slot から `e²`-衝突 (`u = 1` の場合 `K(p) = K(p′)`) ⟹ E↔E² 共役
  (`exists_paley_collision_pow_mul` + `z^{e⁴} = z^e` の 1 補題ブリッジ) ⟹
  `false_of_collisionPair`。
- q = 7 では共謀は 2-loop 段階で悉皆的に偽 (κ は slot 上まったく定数でない)。

**残る数学**: 一般 q で「κ, κ′ が ~2(Q−1) slot を通して分解する」ことの反駁 1 本。
成分横断の符号 filler の存在 (χ(ρ) = −1 クラスの実在または迂回) と、横断 loop の
消滅条件から absurdity への線形代数。ρ-クラス個別の非空性は一般 q で未保証なので、
使ってよいのは鳩の巣 (ある slot が大きい) と Davenport 型 zero-sum のみ。

### 6.1 endgame: master formula への崩壊 (2026-08-13 深夜第 3 弾、重み公式は数値検証済)

⚠ 本節は同日夜の初稿の κ/κ̂ (= κρ^e) の捻れ取り違えを**訂正した版**。

**可換子 loop** (辺 e ∈ (ρ, c)、f ∈ (σ, χ(ρ)c) を前進、同クラスの辺を後退で使う 4 脚、
高さ v →ρ→σ→ρ⁻¹→σ⁻¹→ v)。前進脚は `κ̂(g)·v^e` (`κ̂ := K(p)δ₀^{−e}`)、後退脚は
`−κ(g)·v^e` (`κ := K(p)δ₁^{−e} = κ̂ρ^{−e}`) を寄与する。
**数値検証: この重み公式は literal chain composer と 1010/1010 一致** (GF(3⁷) 両指数,
`endgame_check.py`)。消滅 = 交換関係:

> (EX) `κ(ρ,c)ρ^e − κ(σ,c)σ^e = σ^eρ^e·[κ(ρ, χ(σ)c) − κ(σ, χ(ρ)c)]`

これを全セクター対で解くと (和・差の分離、混合対は整合的にパラメータを同定)、
定数 2 個 λ₊, λ₋ による**統一形**に崩壊する:

> **κ̂(ρ, c) = λ_c − λ_{χ(ρ)c}·ρ^e**、すなわち
> **MASTER: `K(p) = λ_{χ(δ₀)}·δ₀^e − λ_{χ(δ₁)}·δ₁^e` (∀(p,r) ∈ T²)**

(χρ = +1 では λ_c(1−ρ^e)、χρ = −1 では λ_c − λ_{−c}ρ^e — 前稿の
「swap-反対称で全 −1 セクター即死」は捻れ違いによる過剰主張で、正しくは
master formula は swap-整合的。)

**枝の撃破 (導出済・紙上)**:

- ρ = 1 クラスが実現 ⟹ 衝突 ⟹ (B2)-elim で死。
- **Δ := λ₊ − λ₋ = 0** ⟹ master が符号自由になり swap と合わせ `K(p) = −K(r)`
  (∀p≠r) ⟹ 3 点で `K ≡ 0` ⟹ K ≠ 0 と矛盾 ⟹ 死。
- **Σ̄ := λ₊ + λ₋ = 0** ⟹ `K(p) − K(r) = Σ̄(δ₀^e − δ₁^e) = 0` ∀対 ⟹ K 定数 ⟹
  e²-衝突の氾濫 ⟹ E↔E² 共役ブリッジで死。
- **Frobenius cube 整合**: master を (p³,r³) に適用 vs 元式の cube の差で
  `(λ_c − λ_c³)` 型の係数が生き残ると ρ^{3e} が ≤ 4 値に confine ⟹
  **λ₊, λ₋ ∈ 𝔽₃ か、または ρ-confinement 副枝** (副枝 = δ₁ = ρδ₀ が大域的に
  ほぼ成立 = twisted differential の巨大 fiber; 未処理)。
- λ ∈ 𝔽₃ で Δ, Σ̄ ≠ 0 の残候補は **(λ₊,λ₋) ∈ {(1,0),(0,1),(−1,0),(0,−1)}
  の 4 本のみ**。各候補はパターン別に: (−,−)-対があれば K(p) = 0 即死 /
  (+,−) or (−,+)-対が 1 つの p に 2 本あれば δ^e の単射性で即死 /
  残るのは「(+,+)-パターンで `G(r) := δ₀^e − δ₁^e` が定数」型の恒等式 1 本。

**数値 (GF(3⁷) 両指数)**: master の最良 λ-fit は 3/2000 (偶然水準)、𝔽₃-候補
9 本すべて ≤ 5/500 — **共謀は q = 7 で全滅**。dream-world 恒等式
`δ₀^e − δ₁^e = K(p) − K(r)` の defect は 500/500 非零。

**残る bookkeeping (次 session)**: (i) (EX) の符号条件の場合分けを敵対的検証
(可換子 loop の脚の成分選択が全セクター対で組めること)、(ii) λ ∉ 𝔽₃ の
ρ-confinement 副枝、(iii) 𝔽₃-候補 4 本の "wrong-pattern" 恒等式
(G-定数型; パターン人口の場合分けと合わせて)、(iv) 退化人口 (実現クラス ≤ 2、
単一セクター等)、(v) e²-衝突ブリッジ (`z^{e⁴} = z^e`) の Lean 化。
これらが閉じれば **Problem 1 全面解決**。
**→ §6.2: (i)–(iv) はすべて閉じた (2026-08-13 第 2 検証 wave)。(v) は Paley 級で
Lean 化済 (`exists_paley_collision_pow_mul_down`)。**

### 6.2 🎯 endgame CLOSED — 全ケース木 (2026-08-13、敵対的検証 2 レンズ CONFIRMED)

第 2 検証 wave (lens A = 可換子 loop 合法性/(EX) 解空間、lens B = 枝撃破/量子化;
`lensA_commutator_verify.py` 4000/4000 全 8 (セクター, c₁) 組合せ・
`lensB_verify.py` synthetic master データで全恒等式検証) により、残件 (i)–(iv) が
すべて閉じた。**witness 排除の完全なケース木**:

1. **ρ = 1 クラスが実現** (= 衝突が存在): `false_of_collisionPair` で死 [Lean 済]。
2. 以下衝突なしとする。**非退化重みの閉 loop が 1 つでもあれば**
   `false_of_conjPair_frobenius_family` で死 [Lean 済]。よって共謀 (全 loop 消滅)。
3. 共謀 ⟹ same-slot κ-定数 (2-loop、常に合法) ⟹ **可換子 loop は任意の実現クラス対・
   両成分で合法** (swap が両成分を常に共存させる; 全 4 符号セクターで検証済) ⟹ (EX)。
4. (EX) の解 = **master formula** `K(p) = λ_{χδ₀}δ₀^e − λ_{χδ₁}δ₁^e` (rank 計算で
   一意性確認; `x ↦ x^e` 全単射なので `ρ ≠ 1 ⟹ 1−ρ^e ≠ 0`、`ρ^e = σ^e ⟹ ρ = σ`)。
   **唯一の例外 = 実現クラスが単集合 {−1}**: このとき fwd-fwd 2-loop `e ∘ swap(e)`
   (ρ = −1 でのみ符号合法!) が `K(p) = −K(r)` を全対に強制 ⟹ 3 点で K ≡ 0 ⟹ 死。
5. master の枝: **Δ = 0** ⟹ swap で `K(p) = −K(r)` ∀対 ⟹ 3 点矛盾 (2 可逆, char 3)。
   **Σ̄ = 0** ⟹ `K(p) − K(r) = Σ̄(δ₀^e − δ₁^e) = 0` ⟹ K 定数 ⟹ e²-衝突 ⟹
   下向き共役ブリッジ [`exists_paley_collision_pow_mul_down`, Lean 済] で e-衝突 ⟹ 1 で死。
6. **Frobenius 量子化**: μ_c := λ_c − λ_c³ が 1 つでも非零なら: 同符号パターン辺
   (swap で (+,+)↔(−,−) ゆえ 1 本でもあれば) は `ρ^{3e} = 1 ⟹ ρ = 1` (gcd(3e,Q−1)=1)
   = 衝突 ⟹ 死; 全辺混合パターンの世界は swap 対で μ₊ = −μ₋ ⟹ 全辺 ρ = −1 ⟹
   master が `K(p) = Σ̄δ₀^e` に退化 ⟹ e-冪単射性で r が p ごとに一意 ⟹ |T| ≥ 3 と矛盾。
   ⟹ **λ₊, λ₋ ∈ 𝔽₃**。
7. 𝔽₃ 内で Δ, Σ̄ ≠ 0 の残候補 = **(±1, 0), (0, ±1) の 4 本**。各候補: (−,−)-パターン辺
   ⟹ K(p) = 0 即死; (+,+)-辺の swap は (−,−)-辺 ⟹ 同左; 混合パターン
   ((+,−): K(p) = ±δ₀^e / (−,+): K(p) = ∓δ₁^e) は e-冪単射性で p ごとに r を一意に
   pin ⟹ **out-degree |T|−1 ≤ 2 ⟹ |T| ≤ 3、実際は |T| = (Q−3)/4 ≥ 546 で矛盾**
   (|T| ≥ 4 のみ必要)。パターン人口仮説・G-定数型残渣は**不要**。

**使用仮説の総目録**: χ(−1) = −1 (Q ≡ 3 mod 4)、e 奇・`z^{e³} = z`・gcd(e, Q−1) = 1、
`K ≠ 0`、|T| ≥ 4、swap の成分反転、鳩の巣 (同 slot 2 辺 — 手順 3 の κ-定数の実効性)。
equidistribution・Weil 評価・Davenport すら**最終版では不要** (可換子 loop は辺再利用で
組めるため)。

⟹ **witness は全ケースで矛盾 = hypothesis (B) は p = 3 で実現不能。
定理 1 (e ∈ ⟨3⟩)・定理 2 と合わせ、BG App.C Problem 1 (Péterfalvi 1993) は
否定的に全面解決** — (B1) の証明は不要になった。

残作業 (数学は完結、記録と形式化):
1. 統合された完全証明文書 (§1–§6.2 を 1 本の定理として書き下し) + 最終 assembly
   検証 (部品は個別検証済; 組み立ての量化子構造の最終監査)。
2. Lean 化: skew 辺 (E(p,r))・合成/閉条件・可換子 loop・master 崩壊・枝撃破。
   入口 (`false_of_conjPair_frobenius_family`, `exists_paley_collision_pow_mul_down`) は
   merge 済。中規模プロジェクト (数 session 規模)。
3. 検証スクリプト正本: `endgame_check.py` / `lensA_commutator_verify.py` /
   `lensB_verify.py` (session scratchpad `rigidity/`)。

## 7. 帰結

- endgame が閉じれば **(B1) 不要で Problem 1 全面解決**。
- 閉じるまでも: **per-q 証明書が衝突探索から「同 slot 2 辺 + 重み非零」の O(|T|²) hash
  検査に短縮** (q = 47, 73 などに即適用可; birthday 探索 √Q·q 歩も不要になる)。
- Lean 状況: `false_of_conjPair_frobenius_family` / `conjPair_aeval_of_frobenius_family`
  merge 済 (axiom-clean)。skew 辺・合成・loop の形式化は endgame 決着後。

正本スクリプト: session scratchpad `rigidity/skew_cycles.py` (+ 検証 agent の
`lens2_verify.py`, `lens3_verify.py`)。結果は本 note に記録済。
