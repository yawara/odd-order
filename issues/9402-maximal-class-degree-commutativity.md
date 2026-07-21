---
id: 9402
slug: maximal-class-degree-commutativity
title: "CLAIM: maximal-class p群 (class<p) の positive degree of commutativity — BG E.4 の唯一の gap"
created: 2026-07-21
---

# CLAIM (shared infra): maximal-class p-group の degree of commutativity ≥ 1

**claim 主体**: lane c。**leaf**: 新規 `OddOrder/GroupTheory/MaximalClassPGroup.lean`
(未着手、`RegularPGroup.lean` の class<p 域の sibling)。
**consumer**: `OddOrder/BG/AppE_*.lean` の **BG Prop E.4 abelian clause** (issue 3021、
`AppE_FurtherResults.lean:1657` の sorry)。将来 §16 の maximal-class 論法も候補。

## 何を証明するか

有限 p 群 `S` (p 奇素数) が **maximal class**、かつ **class n < p** のとき、
lower central series `γ_i = S.lowerCentralSeries (i-1)` について
> **positive degree of commutativity**: `⁅γ_i, γ_j⁆ ≤ γ_{i+j+1}` (∀ i,j ≥ 2)
(weight bound `⁅γ_i,γ_j⁆ ≤ γ_{i+j}` を 1 段改善)。

repo の H-indexing (`H_m = iterCommutator T ⊤ m = γ_{m+1}`, T = `C_S(Ω₁(Z₂ S))`) では
`⁅H_a, H_b⁆ ≤ H_{a+b+2}` (a,b ≥ 1)。

## なぜ必要か (issue 3021 (51))

BG Prop E.4 の β 側 eigenvalue supply (E.23) `wᵢ^β ≡ wᵢ^{t₀tⁱ}` は各 level で
`⁅H_{i-1}, T⁆ ≤ H_{i+1}` (= **2-step centralizer relation**) を要する。これは次の
**3-subgroups 帰納**で degree of commutativity に還元される (3021 (51) ②):
`base a=1` = weight bound; `step` は `⁅⁅T,H_{a-1}⁆,⊤⁆ ≤ H_{a+2}` (IH) と
`⁅⁅⊤,T⁆,H_{a-1}⁆ = ⁅H_1,H_{a-1}⁆ ≤ H_{a+2}` (degree of commutativity)。
soft な commutator calculus は `⁅R₀,T⁆ = H_1` の off-by-one で全ルート閉じない (確認済)。

## claim-before-build の事前検索 (2026-07-21)

- repo grep: `IsMaximalClass` / `maximalClass` / `uniserial` / `degreeOfCommut` / `two.?step`
  いずれも**なし** (Explore agent 全数確認)。
- 在るのは: `iterCommutator_eq_lowerCentralSeries` (鎖=lcs, E.8)、weight bound
  (`Mann.lean:791`)、`[S:T]=p`、`γ₂≤T`、coset-counting device
  (`S05_NarrowAutomorphisms.lean:344,421`) — degree of commutativity 本体は未形式化。
- mathlib に maximal class / degree of commutativity なし。
- Coq math-comp/odd-order は App.E 相当を持たない (grep 確認)。
- open 9xxx に重複 claim なし (9400=RegularPGroup E.2, 9401=pRank≤2 は別物)。

⟹ 未構築の genuine shared infra。

## 数学的背景 (⚠ 3021 (52) で精密化 — 下記は (51) の旧見立て)

- 一般の positive dc は **Blackburn 1958** の hard 定理 (associated graded Lie 環の構造定数
  γ_{i,j} が最上反対角 i+j=n で自由、消すのに p odd を使う非線形関係が要る)。**soft でない**。
- ~~class < p ⟹ dc≥1 がクリーン~~ ← **(52) で否定**。class の大小でなく機構が違う。

## ⚠⚠ 2026-07-21 (3021 (52) 由来): gap の真の機構 = **regular B 作用 + Jacobi**

- dc は **H_0=T 込みの `⁅H_a,H_b⁆≤H_{a+b+2}` (∀a,b≥0) が丸ごと本体** (soft な小 core 還元なし)。
- ⭐ **B 作用 (abelian regular, 相異なる固有指標 χ_Q≠χ_T on S/S')** が各 level の
  **clean な二者択一** (Case A `t·` / Case B `t₀·`) を eigenvalue 論だけで与える (Jacobi 不要、
  形式化可能)。
- ⚠ 但し「全 level Case A (dc≥1)」の解決 = 「no switch」は **Jacobi と絡む hard core**。
  distinct-eigenvalue + Jacobi ⟹ dc≥1 が成り立つ**らしい** (dc=0 構成が全て Jacobi 違反、
  3021 (52) ③で実例確認) が clean proof 未確立。Blackburn の dc=0 群が regular B 作用を
  許さないのが真相と思われる。
- ⟹ **class<p は理由でない**。authoritative input (Blackburn 分類 / FT1991 原論文 / 最強モデル) 待ち。

## 構造定数 setup (Lie 環、形式化の設計候補)

`L = ⊕ Lⱼ`、`L₁ = ⟨a,b⟩` (a = uniserial 生成元 v̄, b = w̄₀ = T 方向)、`Lⱼ = ⟨eⱼ⟩` (j≥2, 1 次元)。
`eⱼ = (ad a)^{j-1}(b)` (e₁:=b), `⁅a, eⱼ⁆ = e_{j+1}` (uniserial)、`⁅eᵢ,eⱼ⁆ = γ_{i,j} e_{i+j}`。
- (R1) `γ_{i,j} = γ_{i+1,j} + γ_{i,j+1}` (ad a derivation), i,j≥1。
- (R2) `γ_{i,j} = -γ_{j,i}` (antisymmetry)。
- (R4) `γ_{i,j}·γ_{1,i+j} = γ_{1,i}·γ_{i+1,j} + γ_{1,j}·γ_{i,j+1}` (ad b derivation, 非線形)。
- boundary `γ_{i,j}=0` (i+j>n)。goal: `γ_{i,j}=0` (i,j≥2) ⟺ `γ_{2,j}=0` (j≥2、R1+R2 で伝播)。

⚠ 形式化は Lie 環を建てるより **群の iterCommutator で直接** `⁅H_a,H_b⁆≤H_{a+b+2}` を
証明する方が軽い可能性 (associated graded Lie ring infra を作らずに済む)。着手時に決める。

## 進め方

1. **[最強モデルで clean proof 確認]** class<p (p≥2n+3) の dc≥1 の proof strategy を
   ChatGPT (最強モデル、Chrome MCP) で確定 ([[feedback-ask-chatgpt-for-elided-gaps]])。
   数学は未解決でなく (dc≥1 は本 setup で真)、正しい・形式化しやすい proof の確定待ち。
2. **[群で直接 or Lie 環]** dc≥1 = `⁅H_a,H_b⁆≤H_{a+b+2}` を形式化。
3. **[還元]** 3-subgroups 帰納で `⁅T,H_a⁆≤H_{a+2}` (3021 (51) ②)。
4. **[assemble]** `caseA_eigenvalue_step` を base+step で帰納 → `hβsupply` →
   `commutator_centralizer_eq_bot_of_beta_supply` → E.4 abelian clause (3021 の残 sorry)。

## 完了条件

`⁅H_a,H_b⁆≤H_{a+b+2}` (a,b≥1、maximal class + class<p) が sorry-free / axiom-clean。
下流 3021 の E.4 abelian clause が解錠。本 claim を close。

## ✅ hub 重複検査 (2026-07-21 02:41 tick) — claim 承認 ⚠ **(53) で目標差し替え、下記参照**

claim-before-build 協定に基づき hub が重複を検査:
- **grep 実測**: `degreeCommutativity|degree_of_commutativity|degreeOfCommutativity` は repo に 0 件 → 既存実装なし (再構築でない)。
- **subband**: 9400 = lane c (正)。
- **近接 claim との非重複**: 9400 (BG Prop E.2 induction, leaf `RegularPGroup.lean`) とはドメイン (class<p) が隣接するが結果が別 (E.2 帰納 vs degree of commutativity)。9402 は新 sibling `MaximalClassPGroup.lean`。9401 (pRank) は無関係。
- **consumer 実在**: `AppE_FurtherResults.lean:1657` の E.4 abelian clause sorry (issue 3021)。

⟹ **claim 承認**。lane c は `OddOrder/GroupTheory/MaximalClassPGroup.lean` を新設してよい
(新 leaf は同 commit で `OddOrder.lean` に配線すること)。degree of commutativity は
maximal-class p 群論の標準結果 (Blackburn/Leedham-Green) で、E.4 β-supply の正当な reduction target。

## ⚠⚠ 2026-07-21 (53 由来): claim の目標が変わった — dc≥1 は仮説では**強制されない** (反例確定)

GPT-5.6 Sol Pro + 親計算検証で **dc≥1 は E.4 の印刷仮説から従わない**ことが確定 (反例 Q₆、
正本 `notes/bg/appE_e4_counterexample_2026_07_21.md`、issue 3021 (53))。
⟹ 本 claim の「dc≥1 を証明する」は**不可能** (偽)。目標を差し替え:

1. **clean Lemma を形式化** (真・Jacobi のみ): graded Lie 環 `dim(2,1,1,…,1)` で
   `[Lᵢ,Lⱼ]=0 ∀i,j≥2 ⟺ 全 2-step centralizer Cᵢ 一致`。`MaximalClassPGroup.lean` に置く。
   これは genuine 再利用 infra。
2. **E.4 は `hdc` (dc≥1 = 2-step 一致) を追加仮説にして**真にし証明 (assembly は既存 scaffold)。
   BG 印刷版が偽であることを docstring 明示。
3. E.5 も同様に gated (dc≥1 供給が要る)。

⚠ 「dc≥1 を maximal-class + fpf B から出す」路線 (旧 claim) は**放棄** (偽ゆえ)。

## 2026-07-21 (第 2 セッション): 文献照合で概念名が確定 — **exceptional** (Leedham-Green–McKay)

- 「2-step centralizer が全て一致」は maximal class 理論の標準概念 **non-exceptional** そのもの
  (exceptional ⟺ ∃i, `C_G(γᵢ/γ_{i+2}) ≠ G₁`; **dc>0 ⟺ non-exceptional** (n≥5) は standard fact)。
  Blackburn: `n > p+1 ⟹ dc>0`。Q₆ は n=6 の既知 exceptional クラスの実例。
- ⟹ leaf `MaximalClassPGroup.lean` の語彙はこれに合わせる (`IsExceptional` 系 or 2-step 述語 +
  dc 同値)。clean Lemma = この同値の形式化 (群レベル、iterCommutator + Hall–Witt; Lie ring 不要)。
- E.4 側の hdc は **2-step centralizer 形** (`∀ a, ⁅H_a,T⁆ ≤ H_{a+2}`) で statement に足す
  (consumer 直結)。詳細正本 = `notes/bg/appE_e4_counterexample_2026_07_21.md` §形式化方針。

## 2026-07-21 (lane c): Tier 2 完了 → 本 issue が次 frontier。E.4-hdc 組立の入口

**Tier 2 (issue 3027) landing 済** — `printed_propE4_false` (AppE_FiliformRefutation.lean) で
「印刷版 E.4 は偽」が repo statement の否定として機械検証された。⟹ 残りは本 issue の
**corrected E.4** (優先) + clean Lemma。

### E.4-hdc 組立の実測入口 (2026-07-21 調査済)

- **abelian-clause engine は証明済・sorry-free**:
  `RegularOperatorSetup.commutator_centralizer_eq_bot_of_beta_supply`
  (`AppE_EigenvalueCombinatorics.lean:860`)。⚠ 同 file の `grep sorry` 1 件は docstring 汚染
  (L618「all sorry-free」) で実 sorry は 0。
- engine の入力: α 側 chain data (`hr`/`hr₀`/`hr0r`/`hrq`/`hr1`)、`σβ` + **`hβsupply`** (= E.23 形)、
  `t,t₀` unit + `t₀ ≠ t`。供給側 (E.19)/(E.20)/(E.21) 両半は `AppE_AbelianCentralizer.lean`
  に sorry-free で存在 (L114/L522/L652)。
- **残作業** = (1) E.4 statement (`AppE_FurtherResults.lean:1645`) に `hdc` (2-step centralizer 形
  `∀ a, ⁅H_a, T⁆ ≤ H_{a+2}`) を追加、(2) `hdc` → `hβsupply` を `caseA_eigenvalue_step`
  (`AppE_EigenvalueCombinatorics.lean:787`) + `caseB_excluded` (L766) の帰納で構成、
  (3) α/β 固有値データを (E.19)-(E.22) pieces から実引数化、(4) engine に投入。
  index-p clause は無条件のまま (証明済 scaffold)。
- 組立レシピの正本 = issue 3021 (43)/(51)/(52) 節。

## ✅ 2026-07-21 (lane c): corrected E.4 landed — 目標 2・3 完了

- **(2) hdc→hβsupply 帰納**: `OddOrder/BG/AppE_BetaSupply.lean` (新 leaf, sorry-free) —
  `scale_zpow_of_scale` + `scale_iterCommutator_of_two_step` (commit 3b89360e3)。
- **(1)(3)(4) statement 改訂 + 実引数化 + engine 投入**: `OddOrder/BG/AppE_PropE4.lean`
  (新 leaf, ~340 行) — `RegularOperatorSetup.centralizer_upperCentralSeries_abelian_index_p`
  (corrected E.4) が **axiom-clean で完全証明** (AxiomsCheck 登録済、commit 2e6b7829c)。
  - α 側: `exists_zpow_eq_act_of_mem_A`/`zpow_exponent_ne_one`/`exists_zpow_eq_mod_chain`
    /`dvd_sub_eigenvalues` (r₀≡r)。β 側: operator Maschke complement + eigenvalue 抽出 +
    `not_dvd_sub_eigenvalues_of_not_fixes` (t≠t₀)。S'=H₁ 橋 = `commutator_eq_and_card_quotient`。
  - 旧 sorried (偽) E.4 statement は AppE_FurtherResults から削除 (E.3(b)-(d) 型コメント化)。
- **E.5 statement 改訂済**: halt = `(i) ∨ ((ii) ∧ hdc)` (AppE_FurtherResults、skeleton のまま)。

### 残り (本 claim の残余スコープ)

1. **clean Lemma** (`MaximalClassPGroup.lean` 未作成): 「2-step centralizer 全一致 ⟺ dc≥1」
   の群レベル同値 (iterCommutator + Hall–Witt)。現時点で直接 consumer なし (E.4 の hdc は
   2-step 形で直接 state 済) — genuine infra だが優先度は下がった。
2. **E.5 側 hdc 供給の調査**: FT の実適用 (S = Ω₁(O_p(M)), K₁, E) が hdc を満たすか
   (Q₆ 型 exceptional が実際に現れうるか)。E.5 本体の §14 counting gate と合わせて次段。

## ✅ 2026-07-22 (lane c): 残余スコープ (2) の調査完了 — E.5 の hdc は局所 discharge 不能 (負の結論)

**問い**: E.5 (ii) 分岐の追加データ (FT 文脈) が hdc を強制するか (= corrected E.5 から
hdc を落として印刷版に戻せるか)。**答え: 局所データでは不能** — Q₆ 反例は E.5 適用時の
追加制約もすべて満たす:

- **rank-2 制約の射程**: BG p.165 の "Since p ∈ τ₂(N), r(R)=2" (印刷 τ₂(M) は typo、repo
  `e5_R_noncyclic` docstring 参照) は **R = O_p(M) ⊓ N = C_{O_p(M)}(x)** についてであり、
  (E.31) より R = R₀ × (R∩E₀) (p × cyclic) で**構造的に rank ≤ 2 が自動**。
  S = Ω₁(O_p(M)) 全体には rank 制約が無い (p ∈ σ(M) 側は rank 無制約)。
- **(ii) ⟹ |S| ≥ p⁵**: exponent-p 群は位数 ≤ p⁴ なら必ず正規 abelian index-p 部分群を持つ
  (p³: abelian or Heisenberg の maximal は abelian; p⁴: class ≤ 3 の各 case で
  C_S(γ₂) or C_S(x) が abelian 正規 index p)。書籍の "Hence, by (ii), |S| > p⁴" の実体。
  Q₆ は |S| = p⁶ で通過。
- **その他の局所データも Q₆ が満たす**: C_S(x) = R₀×R₁ = p² (narrow centralizer ✓)、
  maximal class ✓、B = C₄₉ cyclic (E cyclic ✓)、A = ⟨β⁷⟩ order 7 prime (= |K₁| ✓)、
  |S| = p⁶ ≤ p⁷ = p^q ✓、全部 odd ✓。
- **書籍 E.5 の (ii) 分岐の論理構造の注記**: E.4 の結論 T = C_S(Z₂(S)) abelian index p は
  T char S ⟹ 正規なので **(ii) と直接矛盾**する (書籍の "E = K₁ ⟹ (i)" 経路と別に、
  (ii)∧E.4 ⟹ False ⟹ (i) の短絡もある)。いずれにせよ corrected E.4 経由で hdc が要る。

⟹ **corrected E.5 (halt = (i) ∨ ((ii) ∧ hdc)) が honest な最終形として確定**。印刷版へ
戻すには「regular B 作用 (+FT 大域文脈) が exceptional (dc=0) を排除する」深い問い
(前記 authoritative input 待ち) の解決が必要で、局所論法では閉じない。App.E は
"Further Results" で repo 内 consumer 無し — これ以上の強化は低優先繰延。

### 残余スコープ (1) = clean Lemma が本 issue の唯一の残作業

`MaximalClassPGroup.lean` (hub 承認済 leaf): 「2-step centralizer 全一致 ⟺ dc≥1」の
群レベル同値 (iterCommutator + Hall–Witt/three-subgroups)。次 iteration で着手。
