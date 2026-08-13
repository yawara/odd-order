# BG App.C Problem 1 (Péterfalvi 1993) 解決のまとめ — 俯瞰・経緯・方法論

作成 2026-08-13。**数学的正本** = [`appC_problem1_resolution.md`](appC_problem1_resolution.md)
(統合証明文書: 主定理 + 完全証明 + Lean 対応表 + 検証記録)。本 note は証明そのものではなく
**俯瞰**: 何が解けたか / どう解けたか / どう検証したか / どこに何があるか / 何が学べたか。
経緯の全記録 = [issue 0180](../../issues/closed/0180-bg-appc-problem1-p-eq-three.md)、
Lean 化の記録 = [issue 0181](../../issues/closed/0181-skew-calculus-lean-formalization.md)
(いずれも closed)。

## 1. 何が解けたか

**BG p.152 / Glauberman–Norton p.1094 "Problem (Péterfalvi)" (1993)**:

> Can the hypothesis of Proposition 9 be satisfied for `p = 3`?

Proposition 9 の hypothesis: (A) `q ∤ p − 1`、(B) Frobenius 群 `H = P ⋊ U`
(`P = 𝔽_{p^q}` の加法群、`U` = `𝔽_p` 上ノルム 1 の元 = 位数 `(p^q−1)/(p−1)` の巡回群;
`p = 3` では平方元全体 = 位数 `(3^q−1)/2`) の単射準同型 `σ : H → G`、
有限可換 `p′`-部分群 `Q ≤ G`、`y ∈ Q` が存在して `σ(P₀)` が `Q` を正規化し
`σ(P₀)^y` が `σ(U)` を正規化する。**`G` の有限性は要求されない**。

`p = 2` はこの hypothesis を実現する (Glauberman–Norton Example 10 = `SL(2,2^q)`、
Example 11 = `Sz(2^q)`)。`p ≥ 5` は GN が Prop 7 で排除している (Prop 7 自体は
[issue 0179](../../issues/closed/0179-bg-appc-remark-iv-glauberman-norton.md) で形式化済;
(B) ⟹ `E = E⁻¹` の抽象版は [issue 0151](../../issues/0151-appc-lemma-c3-abstract-hypothesis-b.md) で進行中)。
残っていたのが `p = 3` で、1993 年の提出以来 33 年間、解決を主張する公刊物は無かった
(OpenAlex / Semantic Scholar の被引用 0 は書籍からの引用を拾わないだけで、BG 1994 自身は
GN 1993 を引用している)。

> **主定理 (2026-08-13).** `p = 3` のとき、**すべての奇素数 `q`** に対し hypothesis (B) を
> 満たす `(G, σ, Q, y)` は存在しない (**`G` は無限でもよい**)。**答えは NO**。

紙上の解決と同日中に **Lean での完全機械検証**まで完了した:

```lean
theorem hypothesisB_false (data : FieldNormalizerData p q G) (hp : p = 3) : False
-- variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]
```

([`OddOrder/BG/AppC_Problem1SkewEndgame.lean`](../../OddOrder/BG/AppC_Problem1SkewEndgame.lean):1251、
追加仮定ゼロ・axiom-clean・AxiomsCheck 登録済)。着手 (2026-08-09、issue 0180 起票) から
決着まで 4 日、紙上の全面解決 (08-13 15:05) から機械検証完成 (同日 19:32) まで 4.5 時間。

## 2. 証明の骨格

`g := σ(P₀)^y` の生成元が `σ(U)` に誘導する指数を `e` (`e³ ≡ 1 mod n`, `n = (3^q−1)/2`) とする。

- **`e ∈ ⟨3⟩` (Frobenius 冪)**: `s ↦ s^e` が加法的になり、関係式族 3 本の消去で
  `[x, x^g] = 1` ⟹ `c := x⁻¹g = 1` ⟹ `g = x` で Frobenius 性に矛盾 (**定理 1**、
  `false_of_centralizing` + `false_of_frobenius_exponent`)。**`q = 3` は位数 3 の指数が
  すべて `⟨3⟩` に入る** (`e³ ≡ 1 mod 13` の解 = `{1,3,9}` = `⟨3⟩`、Lean では `decide`)
  のでここで完結。
- **`q ≠ 3`**: **ケース木** (`false_of_witness`)。witness から層 `a, b, d` (体 `F = 𝔽_{3^q}`
  の忠実加法コピー、`g`-共役で巡回) と Paley 集合 `T` 上の写像 `D, K` を作り、7 段で殺す:
  1. 衝突 (`D(p) = D(r)`) があれば **Part I (B2)-elim** `false_of_collisionPair` で死
     (chain reversal C3 + Frobenius 加群の巡回性 — トレース条件等の付帯条件ゼロ)。
  2. 衝突が無くても `T²` の**任意の**順序対が **skew 辺**になり (Part II)、非退化な重みの
     閉 loop が 1 つでもあれば Frobenius 族経由 `false_of_conjPair_frobenius_family` で死。
  3.–7. 全 loop の重みが消える「共謀」の世界 (Part III endgame): same-slot 2-loop で
     κ-定数 ⟹ 可換子 loop で交換関係 (EX) ⟹ anchor 論法で **master formula**
     `K(p) = λ_{χ(δ₀)}δ₀^e − λ_{χ(δ₁)}δ₁^e` に崩壊 (唯一の例外 = 実現クラスが単集合
     `{−1}` の人口で、これは fwd-fwd 2-loop が別途撃破) ⟹ 4 枝 (`Δ=0` / `Σ̄=0` /
     `λ∉𝔽₃` / `𝔽₃` 残 4 候補) がすべて初等的に矛盾。

使用仮説は `χ(−1) = −1`・`e` 奇・`z^{e³} = z`・`K ≠ 0`・`|T| ≥ 4` のみ (全部 witness から
出る)。**equidistribution・Weil 評価・Davenport・鳩の巣は最終版では一切不要**。
(B1)「衝突が存在する」の証明も不要になった — 一時は未解決の APN 分類予想に寄りかかる
位置と診断されていたが、skew calculus が (B1) そのものを迂回した。

## 3. タイムライン (2026-08-09 → 08-13)

| 日時 | 出来事 |
|---|---|
| 08-09 夕 | issue 0180 起票 (e302bc785)。還元 R1–R4・文献調査・GAP 探索開始・ChatGPT #1 (未完走) |
| 08-10 未明 | `q = 3` 合同枚挙 (24 ケース中 9 否定)、`Γ^ab` の解明 |
| 08-10 昼 | ChatGPT #2 完走 → **万能完備化 `Γ_e`**。こちらで語の恒等式に分解し **部分解決** (12:46: `q = 3` 完全決着 + 中心化の場合は全 `q`)。**定理 2** + 補題 D (13:14–13:17) → witness は非可解 = 可解群・有限奇位数群は不可 |
| 08-10 午後〜夜 | 定理 1・2 の Lean 化 (capstone 14:24、無条件化 22:49 / 23:15)。ChatGPT #3 投入 |
| 08-11 | **collision-span 判定法** (ChatGPT Work 由来、全検証) で `q = 13, 19, 29` 決着 + 完全 Lean 化。夜: **トレース障害** (衝突 1 個 + `Tr S ≠ 0`) + Lean 化、`q = 31` も GAP で決着 |
| 08-12 日中 | `q = 41` 決着 (C 実装、GAP 比 70 倍速) ⟹ **`q ≤ 43` 全部**。**(B1) の正体 = APN** と診断し per-q 方針を撤回 (16:28)。ChatGPT #4 投入 (17:23) |
| 08-12 夜 | #4 完走 (240 分) → **Theorem A (gcd 判定)・Theorem B (同一剰余類)** を全検証 + Lean 化。`q = 53, 79, 101` も決着 |
| 08-13 未明 | **合成計算** (ConjPair・C1/C2・不動点原理・N1–N3) + 閉包実験 (escape 全滅) |
| 08-13 昼 | **(B2) 完全消去** (13:58、chain reversal C3) → **skew calculus** (14:38) → **endgame CLOSED = 紙上の全面解決** (15:05) → assembly 監査 (15:29) → 統合証明文書 (15:42) |
| 08-13 夕〜夜 | Part II/III の Lean 化 (issue 0181; 17:29–18:55 capstone `false_of_exotic`) → 統合 glue → **`hypothesisB_false` (19:32) = 完全機械検証** → issue 0181 close (19:33) |

## 4. 鍵になった着想 (壁と、それを壊したもの)

1. **万能完備化 `Γ_e`** (ChatGPT #2 由来): witness の有限枚挙を捨て、任意の witness が商になる
   有限表示群を見る — `G` の有限性が議論から消えた。こちらで語の恒等式
   `[x⁻¹g, (x⁻¹g)^x] = (gx)³` に分解し、`Γ_e` すら経由しない `G` 内完結の証明に。
2. **補題 D (関係格子)**: `e ∉ ⟨3⟩` ⟺ `L_e = V³` (冪単項式の Dedekind 独立性)。定理 1
   (加法的な場合) と定理 2 (非可解性) がちょうど相補的になった。
3. **per-q 証明書のエスカレーションと限界認識**: collision-span → トレース障害 →
   gcd 判定・同一剰余類、と判定は 3 段階で弱まったが、「`q` を 1 つずつ潰しても証明には
   ならない」(奇素数は無限) — 2026-08-12 に (B1) = APN の壁と診断して per-q を撤回。
   **この撤回が一般証明への集中を生んだ**。
4. **合成計算** (こちら独自): ChatGPT #4 が「射影比に依存する閉包定理が必要 (open)」と
   明言した問題を、衝突関係式の正規形 `ConjPair` と合成定理 C1/C2 で解決。
5. **chain reversal C3** (こちら独自): 標数 3 の 3 行の恒等式
   `ConjPair(s,s′) ∧ ConjPair(s′,s″) ⟹ ConjPair(s″,s)` + Frobenius 加群の巡回性
   (`x^q − 1` squarefree ⟺ `q ≠ 3`) で **(B2) が定理として完全消滅** — 衝突 1 個で
   witness は無条件に死ぬ。
6. **skew calculus** (こちら独自): 衝突 = 「比 1 の辺」にすぎず、**衝突が無くても `T²` の
   全対が辺になる** — (B1) を証明する代わりに**迂回**した。閉 loop の重みが Frobenius 族を
   供給して Part I の一般化 capstone に流れ込む。
7. **endgame** (こちら独自): 敵の最後の逃げ場 = 「全 loop の重みが消える共謀」を、可換子
   loop の交換関係 (EX) と anchor 論法で 2 定数の master formula に圧縮し、4 枝すべてを
   初等矛盾 (swap 対称性・`e`-冪単射性・`|T| ≥ 4` の out-degree 勘定) で撃破。

## 5. AI 協働の内訳

**ChatGPT 相談 4 回** (Chrome MCP 経由; 運用正本 =
[`notes/meta/chatgpt_consult_via_chrome.md`](../meta/chatgpt_consult_via_chrome.md)):

| # | 日付 | サーフェス / モデル / 思考 | 結果 |
|---|---|---|---|
| 1 | 08-09 | Chat / GPT-5.6 Sol / Pro | **未完走** ×2 (2.5h network error / 4h+)。成果ゼロ、運用知見のみ |
| 2 | 08-10 | Work / GPT-5.6 Sol / ウルトラ | 完走 47 分。**万能完備化 `Γ_e`** (こちらで GAP 独立再現: `\|Γ_e\| = 28431`、`z` の位数 3)。被引用 0 の訂正 |
| 3 | 08-10 夜 | Work / GPT-5.6 Sol / ウルトラ | 残ケース専用。**collision-span 障害**の着想 (→ 08-11 `q = 13` 決着)、トレース障害へ追撃 |
| 4 | 08-12 | Chat / GPT-5.6 Sol / Pro | 完走 240 分。**Theorem A (gcd 判定)・Theorem B (同一剰余類 + Hua の恒等式)**。一般 (B1)/(B2) は open と明言 |

**由来の区別** (すべて全ステップこちらで検証してから採用; 未検証の主張は「決着」と
書かない運用を貫徹):

- **ChatGPT 由来**: 万能完備化 / collision-span の着想 / トレース追撃 / Theorem A・B。
- **こちら独自**: 語の恒等式 / 補題 D / 還元 R1–R4 / GAP・C 実装 / `E ↔ E²` 共役 (点ごと版は
  #4 回答の回収前に独立証明) / `δ ∈ U` 条件の消滅 / 合成計算 C1/C2・不動点原理・N1–N3 /
  **chain reversal C3** / Frobenius 巡回加群 / **skew calculus 全体** / **endgame 全体** /
  統合 glue / **全 Lean 形式化** / 全検証。

最終証明に生き残った ChatGPT 由来の部品は **1 つ** — #4 Theorem B の証明核 (交換関係の
解空間 `W` が `s ↦ s^{−E}` の 3 回反復で反転閉包になるトリック + Hua の恒等式による
部分体二分法; Lean = `inv_mem_commSubgroup` + `Algebra/InverseClosedSubgroup.lean`)。
これはケース木の全枝が経由する不動点原理の終端 kill (`false_of_conjPair_self` →
`false_of_mem_commSubgroup_ne_zero`) の中で現役に働いている — Theorem B の「文」は
superseded だが証明核は生存。一方、**万能完備化は最終形から完全に消えた** (語の恒等式に
置換; 14 leaf に有限表示群への参照ゼロを grep で確認)。Theorem A も superseded。
また collision-span → trace → 合成計算 → C3 というエスカレーションの起点は #3 であり、
#4 の「閉包定理が必要」という open 宣言が合成計算の直接の動機になった —
**壁の名指しが前進を駆動した**。

## 6. 検証態勢

三段構え (敵対的検証 / 数値悉皆 / Lean) で、紙の誤りを 3 回実際に捕まえた
(κ/κ̂ の捻れ取り違え = lens A が検出 / 「swap-反対称で即死」の過剰主張 = 初稿自己検出 /
`σ` twist 案の誤り = Lean 化が検出)。

- **敵対的検証 9 レンズ、全 CONFIRMED・fatal 0**: Part I = 3 (group / module / history、
  `q = 3` 反例 `a₀ = x` で squarefree の必要箇所が正確なことも確認)、Part II/III = 6
  (Steps 1–6 の 3 + lens A 可換子 loop 4000/4000 + lens B 枝撃破 + 最終 assembly 監査
  (effort max、スポットチェック 45/45 × 2 指数))。
- **数値悉皆 (GF(3⁷) 両 exotic 指数ほか)**: same-slot 対 10,154,844 / 10,146,444 件で
  kill 率 100% / 閉包実験 101,592 衝突 (q = 7, 13) 全滅 / 可換子 loop 重み公式
  1010/1010 + 4000/4000 / master fit 3/2000 (偶然水準)・𝔽₃ 候補 ≤ 5/500 /
  dream-world defect 500/500 非零。スクリプト正本 = [`notes/meta/c/`](../meta/c/)。
- **Lean**: 本アークで新設した leaf は **14 本 ≈ 8,660 行** (BG 8 本 6,489 行 + Algebra
  6 本 2,171 行; 証明の全周辺には既存の `AppC_HypothesisB.lean` (witness 構造) や
  `AppC_LemmaC3*` も含まれ、いずれも sorry 0)。14 本とも生 grep で sorry 出現ゼロ、
  AxiomsCheck に `Problem1.*` 153 定数 (定理 + def) 登録、すべて axiom-clean。
  フルビルド green・--strict 警告ゼロ。

| leaf | 行数 | 内容 |
|---|---|---|
| `BG/AppC_Problem1.lean` | 1070 | 層構造・定理 1 (`false_of_centralizing`) |
| `BG/AppC_Problem1Lattice.lean` | 1060 | 定理 2 (`not_isSolvable_of_exp`)・関係格子移送 |
| `BG/AppC_Problem1Trace.lean` | 454 | トレース障害 (判定は superseded; 衝突 packaging `exists_collisionPair_of_sub_ne_zero` は現役) |
| `BG/AppC_Problem1SameCoset.lean` | 530 | Theorem B・同一剰余類 (判定は superseded; 不動点原理の終端 kill はケース木全枝が経由する現役部品) |
| `BG/AppC_Problem1PairComposition.lean` | 983 | **Part I capstone `false_of_collisionPair`**・C3・family capstone |
| `BG/AppC_Problem1SkewCalculus.lean` | 727 | Part II: SkewPair・FrobFam・辺・loop kill |
| `BG/AppC_Problem1SkewEndgame.lean` | 1293 | Part III: (EX)・master・4 枝・**`false_of_exotic`・`hypothesisB_false`** |
| `BG/AppC_Problem1Exponent.lean` | 372 | 統合 glue: 指数抽出・`false_of_frobenius_exponent` |
| `Algebra/PaleySpanning.lean` | 1176 | Paley 集合の張り生成・`\|T\|` 下界・`E↔E²` ブリッジ |
| `Algebra/RelationLattice.lean` | 167 | 補題 D (トレース双対性) |
| `Algebra/PowerMonomialIndependence.lean` | 125 | 冪単項式の Dedekind 独立性 |
| `Algebra/FrobeniusCyclicModule.lean` | 251 | Frobenius 加群の巡回性 (Part I の核) |
| `Algebra/InverseClosedSubgroup.lean` | 246 | Hua の恒等式 → 部分体二分法 (Theorem B の核) |
| `Algebra/FrobeniusStableHyperplane.lean` | 206 | `ker Tr` = 唯一の Frobenius 安定超平面 |

形式化は紙の証明を 4 点で**簡約**した (逆方向の寄与): layer (0,1) 構築で `g`-共役が不要 /
anchor の 2 段 pinning が不要 / `(Q)` + swap-(Q) の和で `μ₋ = −μ₊` が即出 /
3-冪単射が Frobenius 単射性から無料。

## 7. superseded された部品 (定理としては残る)

最終証明はケース木 (§2) だけで閉じるため、以下は certificate として不要になった。
削除はしない (定理として保持、per-q の歴史記録):

- **per-q 証明書**: `q ≤ 43` 全部 (定理 1 / collision-span / trace / C 探索) +
  `q = 53, 79, 101` (gcd 判定、ブロック列挙の完全性検証済) + `q = 47, 73` の部分結果。
- **判定法の系譜**: collision-span (`S` が `F` を張る) → トレース障害 (衝突 1 個 +
  `Tr S ≠ 0`) → Theorem A/B (gcd・同一剰余類) → N1/N2/N3 (合成計算) → 全部 Part I
  (`false_of_collisionPair`、付帯条件ゼロ) が吸収。
- **効かなかった攻め筋の記録** (partial_resolution.md; 同じ道を再探索しない):
  APN 分類予想 / Sidon・planar 関数 / 素朴な数え上げ / 合同枚挙のアーベル化 /
  Gersten–Stallings / 原始置換群の掃引 / `q` 個別撃破そのもの。

## 8. 文書地図

| ファイル | 内容 |
|---|---|
| [`appC_problem1_resolution.md`](appC_problem1_resolution.md) | **統合証明文書 (数学的正本)** — 主定理 + 完全証明 + Lean 対応表 + 検証記録 |
| 本 note (`appC_problem1_summary.md`) | 俯瞰: 結果・経緯・方法論・地図 |
| [`appC_problem1_skew_calculus.md`](appC_problem1_skew_calculus.md) | Part II/III の発見記録 (辺 calculus・endgame ケース木・検証 wave) |
| [`appC_problem1_pair_composition.md`](appC_problem1_pair_composition.md) | Part I の発見記録 (ConjPair 合成計算; §9 = (B2)-elim) |
| [`appC_problem1_partial_resolution.md`](appC_problem1_partial_resolution.md) | 定理 1・2、per-q 証明書時代、行き止まりの記録 |
| [`appC_problem1_chatgpt_answer.md`](appC_problem1_chatgpt_answer.md) / [`_b1.md`](appC_problem1_chatgpt_answer_b1.md) | 相談 #2 / #4 の回答と検証 (prompt 全文は `appC_problem1_chatgpt_prompt*.md`) |
| [issue 0180](../../issues/closed/0180-bg-appc-problem1-p-eq-three.md) | 経緯の全記録 (親 issue、最終総括付き) |
| [issue 0181](../../issues/closed/0181-skew-calculus-lean-formalization.md) | Part II/III + glue の Lean 化記録 |
| [`notes/meta/c/`](../meta/c/) | 検証スクリプト (skew_cycles / endgame_check / lensA・lensB / assembly_spotcheck / chain_closure / collision_impact / gf3_collision.c) |
| [`notes/meta/gap/`](../meta/gap/) | GAP スクリプト (verify_gn.g / verify_trace_obstruction.g ほか) |
| [`references/glauberman-norton/`](../../references/glauberman-norton/) | 原論文 (pp.1093–1094 = Prop 9 と Problem) |

## 9. 教訓

1. **未解決問題も通常の規律で落ちた**: 上流優先・実測・issue 駆動・「検証していない主張は
   採用しない」という本リポジトリの通常運転のまま、教科書の外の 33 年 open な問題が
   4 日で決着した。特別なモードは要らなかった。
2. **証明する代わりに迂回する自由**: (B1) は「APN 分類予想級」の壁と正しく診断されたが、
   最終証明はそれを**証明せずに迂回**した。壁の正体を突き止める作業 (§4-3) 自体が
   迂回路の発見 (衝突 = 比 1 の辺、という埋め込み) を可能にした。
3. **per-q 撃破は証明に寄与しない** — 探索が桁で速くなっても論理は変わらない
   (ユーザー指摘)。撤回の決断が一般証明への集中を生んだ。
4. **検証の三段構え** (敵対的レンズ / 数値悉皆 / Lean) は飾りではなく、紙の誤りを
   3 回実際に捕まえた。特に「同日中の Lean 化」は最後の glue の設計ミス (`σ` twist) を
   その日のうちに炙り出した。
5. **AI 協働の型**: 外部モデルには (a) 検証済み入力を明示して問題を絞る、(b) 部分報告と
   PROVED/COMPUTED/HEURISTIC の区別を要求する、(c) 回答は全ステップ再検証し、open と
   名指しされた壁を自前の道具で攻める — この型 (#4 → 合成計算) が決定打になった。
