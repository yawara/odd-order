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

## 7. 帰結

- endgame が閉じれば **(B1) 不要で Problem 1 全面解決**。
- 閉じるまでも: **per-q 証明書が衝突探索から「同 slot 2 辺 + 重み非零」の O(|T|²) hash
  検査に短縮** (q = 47, 73 などに即適用可; birthday 探索 √Q·q 歩も不要になる)。
- Lean 状況: `false_of_conjPair_frobenius_family` / `conjPair_aeval_of_frobenius_family`
  merge 済 (axiom-clean)。skew 辺・合成・loop の形式化は endgame 決着後。

正本スクリプト: session scratchpad `rigidity/skew_cycles.py` (+ 検証 agent の
`lens2_verify.py`, `lens3_verify.py`)。結果は本 note に記録済。
