# BG App.E Prop E.4 は印刷どおりでは**偽** — 検証済み反例 (2026-07-21, lane c)

**結論**: Bender–Glauberman *Local Analysis for the Odd Order Theorem* の **Proposition E.4
(および (E.23)) は、印刷された仮説のもとでは偽**。GPT-5.6 Sol Pro (41分推論) が明示反例を提示し、
lane c が **F_197 上で全主張を計算検証** (`scratchpad/verify_q6.py`、全 Jacobi・fpf・固有値・dc=0・
T 非可換をチェック; 全 pass)。

## 反例 = Vergne の例外 filiform Lie 環 Q₆ の Lazard 群

- `k = F_197`, `p = 197` (素数)。6 次元 graded Lie 環 `L = L₁⊕…⊕L₅`,
  `L₁ = ⟨a,b⟩`, `Lᵢ = ⟨eᵢ⟩` (2≤i≤5)。**非零 bracket は 5 本のみ**:
  `[a,b]=e₂`, `[b,e₂]=e₃`, `[b,e₃]=e₄`, `[a,e₄]=e₅`, `[e₂,e₃]=e₅`。
- **Jacobi 全成立** (検証済; 唯一非自明な triple (a,b,e₃) で `[a,e₄]+[e₃,e₂] = e₅−e₅ = 0`。
  ⚠ 非構造 bracket `[e₂,e₃]=e₅` は Jacobi を破らず、逆に `[a,[b,e₃]]=e₅` を相殺する)。
- maximal class: dim 2,1,1,1,1、class 5、`|L|=p⁶`。`class 5 < p=197` ⟹ **Lazard 対応**で
  exponent-p 群 `S = Exp(L)`、`|S|=p⁶`、maximal class、`γᵢ(S)=Exp(Fᵢ)`。
- **dc(S)=0**: `[F₂,F₃] ∋ [e₂,e₃]=e₅ ≠ 0`、しかし weight bound の目標 `F_{2+3+1}=F₆=0`。
  ⟹ `[γ₂,γ₃] ⊄ γ₆`。(n=5 が dc=0 の最小 class。n≤4 では `[L₂,L₂]` は 1 次元交代ゆえ 0。
  ⚠ **親の旧「n=6 で Jacobi 矛盾」観察は誤誘導**: 真の反例は n=5=Q₆。n=6 の switch は別理由で不整合。)

## fpf regular B 作用 (全仮説を満たす)

- `ζ = 16 ∈ F_197ˣ`, **ord(ζ)=49** (検証: 16⁴⁹=1, 16⁷=104≠1)。
- 対角自己同型 β, weights on (a,b,e₂,e₃,e₄,e₅) = **(1,8,9,17,25,26) mod 49**。
  5 本の bracket と weight 加法が一致 (1+8=9, 8+9=17, 8+17=25, 1+25=26, 9+17=26) ⟹ **β は Lie 自己同型**。
- **fpf**: 全 6 weight が mod 49 の unit (7 の倍数でない) ⟹ 任意 1≤m≤48 で `ζ^{mw}=1` は `49|m` を要し不可
  ⟹ `C_S(β^m)=1`。`B=⟨β⟩≅C₄₉` abelian, `197∤|B|`。
- **α=β⁷ (order 7) は S/γ₂ 上スカラー** `r=ζ⁷=104` (a,b 両方 104)。
- **β は S/γ₂ 上相異なる固有値** `t=ζ=16` (Q=ka), `t₀=ζ⁸=88` (T=kb)、`t≠t₀` (`ζ⁷≠1`)。
- `n=5 < 197`, `5 ≤ (197−3)/2 = 97`。⟹ **Q1 の全仮説を満たす**。

## E.3/E.4 の centralizer setup も満たすが T 非可換

- `v=a+b`, `R₀=Exp(kv)` (order p), `R₁=Exp(ke₅)` (order p, central cyclic)。`α(v)=rv`。
- **`C_R(R₀) = R₀ × R₁`** (検証: `C_L(v) = k(a+b) ⊕ ke₅`) = E.3 の narrow 仮説そのもの。
- `Φ(S)=S'=γ₂`。`R₀Φ(S) mod γ₂ = k(a+b)`、`β(a+b)=ζa+ζ⁸b` は非比例 ⟹ **β は R₀Φ を固定しない** (E.4 の仮説)。
- `Z(L)=ke₅`, `Z₂(L)=ke₄⊕ke₅` (=γ₄), exponent-p ゆえ `Ω₁(Z₂)=Z₂`。
- **`T = C_S(Z₂(S)) = Exp(kb ⊕ F₂)`**, 指数 p、しかし **`[b,e₂]=e₃≠0` ⟹ T 非可換**。
  ⟹ E.4 の結論「C_S(Z₂(S)) は指数 p のアーベル」に**真っ向から反する**。✅ 反例確定。

## (E.23) が明示的に破れる

`w̄₀=b (weight 8), w̄₁=[b,v]=−e₂ (9), w̄₂=e₃ (17), w̄₃=−e₄ (25), w̄₄=e₅ (26)`。
(E.23) の予言 `tᵢ=t₀tⁱ`= exponent `8+i`: 8,9,**10**,11,12。実際: 8,9,**17**,25,26。
`i=2` で実 `ζ¹⁷` vs 予言 `ζ¹⁰` (差 `ζ⁷≠1`)。⟹ **(E.23) は偽**。
一方 (E.22) (α 側) は実 weight `ζ⁷,ζ¹⁴,…,ζ³⁵ = r,r²,…,r⁵` で予言と一致 ⟹ **α 側は正しい**。
switch: 2-step centralizer 線 `C₂=C₃=ka` だが `C₄=kb=T/γ₂` ⟹ **1 回 switch**、これが dc=0 の正体。

## ⭐ 真に欠けている仮説 = **全 2-step centralizer の一致** (= dc≥1、clean Lemma)

GPT が与えた**clean な equivalence** (親検算済、Jacobi のみ、three-subgroups 不要):

> **Lemma**. graded Lie 環 `L=L₁⊕…⊕Lₙ`, `dim L₁=2, dim Lᵢ=1 (i≥2), [L₁,Lᵢ]=L_{i+1}`。
> `Cᵢ = {x∈L₁ : [x,Lᵢ]=0}` (各 1 次元) とすると、次は同値:
> (1) `[Lᵢ,Lⱼ]=0` ∀i,j≥2 (= dc≥1)。 (2) `C₂=C₃=…=C_{n-1}`。
>
> **証明 (1⟹2)**: `c∈Cᵢ, x∈L₁∖Cᵢ, z∈Lᵢ` に Jacobi `[c,[x,z]]=[[c,x],z]+[x,[c,z]]`。
> `[c,z]=0`, `[c,x]∈L₂` ゆえ `[[c,x],z]∈[L₂,Lᵢ]=0` (条件1) ⟹ `[c,[x,z]]=0`。
> `[x,z]` が `L_{i+1}` を張るので `c∈C_{i+1}`。1 次元ゆえ `Cᵢ=C_{i+1}`。
> **(2⟹1)**: 共通値 `C`、`c∈C, x∉C`、`eᵢ` を `x` で生成。`[c,eᵢ]=0 (i≥2)`。
> `[e₂,eⱼ]=[[c,x],eⱼ]=[c,[x,eⱼ]]−[x,[c,eⱼ]]=0`、以下 i に帰納で `[eᵢ,eⱼ]=0`。∎

**maximal class では `T/γ₂ = C_{n-1}`** (T が `Z₂=γ_{n-1}` を中心化)。weight bound から
`[T,γᵢ]≤γ_{i+2} ⟺ τ=Cᵢ`。⟹ **(E.23) 全 level 成立 ⟺ `Cᵢ=τ` ∀i ⟺ dc(S)≥1**。
これが (E.23) に必要な唯一の追加仮説。Q₆ 反例はこれを満たさない (`C₂=C₃≠C₄`)。

## ⟹ 形式化への含意

- **E.4 (`centralizer_upperCentralSeries_abelian_index_p`, AppE_FurtherResults:1657) は印刷仮説では
  証明不能 (偽)**。honest な選択肢:
  1. **追加仮説** `hdc : dc(S)≥1` (or 同値な 2-step centralizer 一致 / (E.23)) を statement に加えて
     真にし、assembly で証明。BG が省いた仮説を docstring で明示。下流 E.5 が供給する必要。
  2. E.5 (Cor E.5) の application が dc≥1 を**深い理由で**満たすか調査 (Q₆ が FT の
     `S=Ω₁(R)` として実際に現れるか)。App.E は "Further Results of Feit and Thompson" ゆえ
     FT critical path 外の可能性が高く、Coq odd-order も App.E を持たない。
- **clean Lemma (dc≥1 ⟺ 2-step centralizer 一致) は真・形式化可能な genuine 再利用 infra**
  (`MaximalClassPGroup.lean`、issue 9402)。Jacobi だけで出る。
- ⚠ 反例は「BG に本当に gap がある」ことを示す。これは形式化で BG より踏み込む必要がある稀なケース。

## 出典・検証

- ChatGPT GPT-5.6 Sol Pro 回答全文: chat `6a5e66c0`、プロンプト = `notes/bg/appE_e4_dc_chatgpt_prompt.md`。
- 計算検証スクリプト: `scratchpad/verify_q6.py` (全 pass)。Vergne classification (Numdam) 引用は
  未検証だが、反例自体は F_197 上で自己完結に検証済ゆえ classification 定理は不要。
- ⚠ GPT 回答は鵜呑みにせず全 step を親が独立検証した (Jacobi 手計算 + Python 全数)。

## 2026-07-21 (第 2 セッション): 影響の全数調査 + 文献照合 + 形式化方針の確定

### 独立再検証 (再現性確認)

bracket table から書き直した別スクリプト (session scratchpad `verify_q6_recheck.py`) で
**12/12 PASS**: Jacobi 全 triple / lcs dims (6,4,3,2,1,0) = maximal class 5 / dc=0 /
ord(16)=49 mod 197 / β 自己同型 (weight 加法性) / fpf (全 weight が mod 49 unit) /
α=β⁷ スカラー r=104 / C_L(v)=k(a+b)⊕ke₅ / β(v)∉kv / Z₁=ke₅, Z₂=ke₄⊕ke₅,
T=C_L(Z₂)=⟨b,e₂..e₅⟩ 指数 p 非可換 / (E.23) の破れ (実 weight 8,9,17,25,26 vs 予言 8,9,10,11,12) /
197≡1 (mod 49)。前セッションの検証と独立に一致。

### 被引用の全数調査 — E.4 は書籍全体で 1 箇所しか使われない

- **BG 本文 (§1–§16)**: Prop E.4 / Cor E.5 への引用 **0 件** (pdftotext 全文 grep)。
  App.E 自身の序文も「could lead to further reductions in the proof of the Odd Order
  Theorem」— 将来の簡約化のための *prospective* な付録で、本文はどこも依存しない。
- **書籍内の唯一の消費点** = Cor E.5 の証明 (p.164-165, pdftotext L8333-8337) の
  **(ii)⟹(i) 段のみ、対偶形で**: (ii)「Ω₁(O_p(M)) に指数 p の正規アーベル部分群なし」+
  E regular のもとで、もし E が R₀ を固定しないなら E.4 の結論 (T char S がアーベル指数 p)
  が (ii) と矛盾 ⟹ E は R₀ を固定 ⟹ E=K₁ ⟹ (i)。**Q₆ は (ii) を満たす**
  (指数 p 部分群は全て Φ(S)=γ₂ ⊇ ⟨e₂,e₃⟩ を含み、[e₂,e₃]=e₅≠0 ゆえ全部非可換) ので、
  この対偶は印刷版のままでは通らない。
- **E.5 の (i) 側は無傷**: E.3/E.4 は (ii)⟹(i) の還元にしか使われず、還元後の本体
  ((E.33)(E.34) + §14 counting) は (i) だけから走る。**壊れているのは (ii) 枝のみ**。
- **Peterfalvi 全章**: "Appendix E"/"E.4" 引用 0 件 (pdftotext grep)。
- **Coq odd-order**: `BGappendixAB.v` / `BGappendixC.v` のみ。App.E は形式化されていない (ls 確認)。
- **FT spine**: BG §16 からは Prop 16.1 のみ消費 (settled)。App.E は完全に terminal。

### 出典の確定 — App.E は Feit–Thompson の未発表結果 (照合すべき原論文が無い)

BG 序文 (pdftotext L537-539): "For permission to include **unpublished work**, we thank …
especially Walter Feit and John G. Thompson (Theorem 15.8, Corollary 15.9, **Appendix E**)."
Cambridge の紹介文も "a recent (1991) significant improvement by Feit and Thompson" と表現。
⟹ **(E.23) を照合できる公刊原文は存在しない**。BG 印刷文が唯一の公開ソースであり、
反例により偽と確定した以上、これは *published erratum が存在しない新発見の誤り*。
web 検索でも本書のエラータ集・本 gap への言及は見つからず (2026-07-21)。

### ⭐ 文献照合 — 欠けている仮説は標準概念 **exceptional** (Leedham-Green–McKay)

maximal class p 群の標準理論に完全に対応する語彙があった:

- **exceptional** の標準定義: maximal class `G` (位数 pⁿ, n≥5) が exceptional ⟺ ある
  `3 ≤ i ≤ n-2` で **2-step centralizer** `C_G(γᵢ/γ_{i+2}) ≠ G₁` (= `C_G(γ₂/γ₄)`)。
- **dc > 0 ⟺ non-exceptional** (n≥5; Leedham-Green–McKay の教科書、
  "On the degree of commutativity of p-groups of maximal class" 系の文献)。
- **Blackburn**: `n > p+1` ⟹ dc > 0 (exceptional は `n ≤ p+1` にのみ存在)。
  Q₆ は n=6 ≤ p+1=198 の exceptional 群 — 既知クラスの実例で、病的な新奇物ではない。

⟹ **erratum の正確な言明**: Prop E.4 には「`S = Ω₁(R)` が **non-exceptional**
(同値: 全 2-step centralizer が一致 ⟺ dc(S) ≥ 1)」という仮説が欠けている。
E.4 の固有値機構 (fpf regular B) は exceptional 群を排除しない (Q₆ が実証)。
GPT の clean Lemma は「dc≥1 ⟺ 2-step centralizer 一致」の同値の graded Lie 環版で、
文献の standard fact と整合する (n≥5 の maximal class に相当する次元列で)。

### 形式化方針 (確定; issue 9402 の rev.53 プランを精密化)

1. **E.4**: 追加仮説 `hdc` は **2-step centralizer 形** (`∀ a, ⁅H_a, T⁆ ≤ H_{a+2}`、
   正確な添字は既存 consumer `caseA_eigenvalue_step` が固定する) で statement に加える。
   assembly が直接消費する形であり、文献の non-exceptional と一致する。
   - **index-p clause は無条件のまま** (反例でも `|S:T|=p` は成立、scaffold で証明済)。
     hdc で gate するのは abelian clause のみ。
   - docstring: 印刷版が偽であること・反例 Q₆・欠落仮説 = non-exceptional・本 note への
     参照を明記 (トレーサビリティ 3 層の範囲内)。
2. **clean Lemma** (dc≥1 ⟺ 2-step 一致) は `MaximalClassPGroup.lean` に**群レベル**
   (iterCommutator + Hall–Witt/three-subgroups) で形式化。graded Lie ring infra は建てない。
   E.4 自体には必須でない (hdc を 2-step 形で取るので) が、供給側の橋 + genuine 再利用 infra。
3. **E.5**: 印刷版の `(i) ∨ (ii)` は維持できない。**(ii) を `(ii) ∧ hdc(Ω₁(O_p(M)))` に
   置換**して形式化する (= (ii)⟹(i) 段が corrected E.4 で通る)。docstring に「印刷版 (ii)
   枝の証明は E.4 gap で壊れている; statement 自体は IsMinimalSimpleOdd が空ゆえ vacuously
   true だが、feitThompson cite で閉じるのは BG 形式化として無意味なのでやらない」を明記。
4. **反例の Lean 形式化 — 2 層に分割 (ユーザー要請 2026-07-21 で方針更新)**:
   - ✅ **Tier 1 (Lie 環レベル) = 完了** (`OddOrder/BG/AppE_FiliformCounterexample.lean`、
     下記セクション参照)。反例の数学的核心 (Jacobi・fpf・中心化群構造・(E.23) の破れ) を
     機械検証済。残る散文ギャップは Lazard 対応 (class 5 < p、古典定理) のみ。
   - ✅ **Tier 2 (群レベル) = 完了 (2026-07-21、issue 3027)**: 当初の semidirect 案でなく
     **直接多項式法則** (rescale `diag(1,1,2,12,24,720)` で整数係数化した truncated BCH、
     全恒等式が素の `ring` で閉じる) を採用。下記セクション参照。
   - **corrected E.4 の健全性は反例の正否に依存しない** (仮説追加は定理を弱めるだけ) という
     非対称性は不変 — Tier 2 は erratum 公表時の確度向上が主目的。
5. **エラータ報告はユーザー判断事項** (外向き action)。Glauberman (Chicago) 存命。
   公表エラータ・既知言及は無いので、報告するなら新規。

## ✅ 2026-07-21: PDF ページ画像で確認 (pdftotext でなく原典画像、ユーザー要請)

`references/bg/local-analysis.pdf` の PDF page 171-172 (book p.158-159 = Thm E.3) と
PDF page 175-176 (book p.162-163 = Prop E.4) を**画像で精読**。pdftotext は忠実で、
**落ちた仮説は無い**ことを確認。反例は E.3/E.4 の印刷仮説を**全て**満たす:

**Thm E.3 (p.158) の印刷仮説** (画像で確認): 「p,q distinct odd primes, R a p-group,
R₀,R₁ nonidentity subgroups of R, B an operator group on R, A a subgroup of B. Assume
p ∤ |B| and **|A|=q, |R₀|=p, R₁ is cyclic, C_R(R₀)=R₀×R₁**, and A fixes R₀ and acts
regularly on R.」— 追加仮説なし。
- 反例照合: p=197,q=7 (distinct odd ✓); R=S=Q₆群 (exp p ⟹ Ω₁(R)=R); R₀=⟨v⟩(|R₀|=p✓),
  R₁=⟨e₅⟩(cyclic✓); B=C₄₉, A=⟨β⁷⟩(|A|=7=q✓, p∤49✓); **C_R(R₀)=R₀×R₁✓**(計算検証済);
  A が R₀ 固定(α(v)=rv)+ fpf✓。⟹ **E.3 の全仮説成立**。

**Prop E.4 (p.162) の印刷文** (画像で確認): 「Assume the situation of Theorem E.3 and let
S=Ω₁(R). Suppose **|S|≥p⁴** (⚠ pdftotext は ">p⁴" だが原典は "≥p⁴"; 反例 p⁶≥p⁴ で無影響),
B acts regularly on R, and B does not fix R₀. Then C_S(Z₂(S)) is abelian and has index p
in S.」— 追加仮説なし。反例は |S|=p⁶≥p⁴, B regular, B が R₀ 非固定 を全て満たす。

**(E.23) (p.163) の画像**: 「Similarly one can show that (E.23) wᵢ^β ≡ wᵢ^{tᵢ} (mod H_{i+1})
for tᵢ=t₀tⁱ」— **証明なし**、"Similarly one can show" のみ。(E.22) (α側) は (E.16)+(E.19) から
導出と明記されるが、(E.23) は類推だけ。

⟹ **PDF 画像レベルで確定**: BG Prop E.4 は印刷どおりでは偽。gap は未証明の (E.23)。
pdftotext に依存した誤読ではない (ユーザーの懐疑に対する直接確認)。

## ✅ 2026-07-21: 反例の Lie 環核心を Lean で形式化 (Tier 1 完了)

**`OddOrder/BG/AppE_FiliformCounterexample.lean`** (leaf build green・全定理 axiom-clean
`[propext, Classical.choice, Quot.sound]`、AxiomsCheck 登録済・OddOrder.lean 配線済)。
mathlib import のみの自己完結 leaf。`V = Fin 6 → ZMod 197` 上の明示 bracket `br` で:

| 定理 | 内容 |
|---|---|
| `br_leibniz` (+双線形性・`br_self`) | **Jacobi 恒等式** — 反例の最も繊細な主張 |
| `lcs_five_eq_bot` + `e5_mem_lcs_four` | lcs 次元列 (6,4,3,2,1,0) = class ちょうど 5 (< p) |
| `degree_of_commutativity_zero` | `e₂∈γ₂, e₃∈γ₃, [e₂,e₃]≠0, γ₆=⊥` = **dc(L)=0** (exceptional) |
| `br_beta` / `beta_iterate_card` / `beta_iterate_fixed_eq_zero` | β は bracket 自己同型・β⁴⁹=1・**全非自明冪 fpf** (B regular) |
| `centralizer_v_iff` | **`C_L(v) = K·v ⊕ K·e₅`** (E.3 の narrow 仮説) |
| `alpha_smul_v` | α=β⁷ は K·v 上スカラー ζ⁷ (A fixes R₀、(E.22) α側は正しい) |
| `beta_not_fixes_v` | **B は R₀ を固定しない** (E.4 仮説) |
| `memT_iff` + `T_not_abelian` | `T=C_L(Z₂)` = 超平面 `{x₀=0}` (指数 p 節は生存) だが **非可換** |
| `e23_fails_at_two` | **(E.23) は i=2 で偽**: 実固有値 ζ¹⁷ vs 予言 ζ¹⁰ (ζ⁷≠1) |
| `bg_propE4_lie_counterexample` | 上記のヘッドライン束 |

**証明技法**: 具体計算は全て kernel `decide` (native_decide 不使用 = axiom-clean 維持)、
一般恒等式は `funext + fin_cases + simp + ring` の座標分解。ZMod 197 の体 instance は
`Mathlib.Algebra.Field.ZMod`、素数判定 norm_num は `Mathlib.Tactic.NormNum.Prime` (要 import)。

**確度の主張**: これで「BG 印刷版 E.4 は偽」の信頼性は、(i) Lie 環反例の実在と全仮説成立
= **Lean 検証済**、(ii) 印刷文の転記 = PDF ページ画像で照合済、(iii) Lie→群の Lazard 転送
= 未形式化の古典定理 (class < p)、の 3 点に分解され、実質的な誤りリスクは (iii) の適用ミス
のみに局所化された。(iii) も潰すのが Tier 2 (上記)。

## ✅ 2026-07-21: Tier 2 完了 — printed E.4 の否定を Lean で証明 (issue 3027)

Lazard 転送の散文ギャップも消え、**「BG 印刷版 E.4 は偽」が repo の E.4 statement
そのものの否定として機械検証された**。leaf 2 枚 (いずれも green・axiom-clean・
AxiomsCheck 登録済・OddOrder.lean 配線済):

1. **`OddOrder/BG/AppE_FiliformGroup.lean`** (WP2-4): `V = Fin 6 → ZMod 197` 上の
   rescaled truncated BCH 法則 `gmul` で群 `Q6` を実構築 (`Group.ofLeftAxioms`、
   assoc は整数係数多項式恒等式 = `ring`)。`|S|=197⁶`、exponent 197 (`co_pow`)、
   Z(S) = e₅-line、**C_S(⟨v⟩) = ⟨v⟩ ⊔ ⟨e₅⟩** (E.3 の narrow 仮説)、Z₂(S) = e₄–e₅ 平面、
   **T = C_S(Z₂(S)) = {x₀=0} 非可換** (bg·e2g ≠ e2g·bg)。β の MulAut 化 + 
   `act : Multiplicative (ZMod 49) →* MulAut Q6` + fpf (`act_regular`) +
   A = ⟨ofAdd 7⟩ が R₀ 固定 / B は非固定。
   - 証明技法メモ: Z₂ 下界は **`plane_mul_comm`** (平面元 x に対し
     `x * y = ⟨(-30·x₄·y₀)•e₅⟩ * (y * x)`、中心補正を**左に**置く) で
     ⁅x,y⁆ = 補正 が `mul_inv_cancel_right` 一発になり、4 重 BCH 展開を完全回避。
     上界は ⁅x, a⁆/⁅x, b⁆ ∈ e₅-line の座標 2..4 から linear_combination で三角 solve。
2. **`OddOrder/BG/AppE_FiliformRefutation.lean`** (WP5): 
   **`q6Setup : RegularOperatorSetup Q6 (Multiplicative (ZMod 49)) 197 7`** (全 field
   実データ、opaque/sorry 無し)、`Ω₁(S) = ⊤`、`197⁴ ≤ |Ω₁(S)|`、comap 転送
   (`Subgroup.comap_upperCentralSeries` + `MulEquiv.subgroupCongr`+`topEquiv`)、
   `q6_centralizer_not_mulCommutative`、**headline `printed_propE4_false`**:
   sorried `RegularOperatorSetup.centralizer_upperCentralSeries_abelian_index_p` と
   同形の全称文 (universe 0) の否定。

**確度の 3 分解は 2 点に縮んだ**: (i) 反例の実在+全仮説成立 = Lean 検証済 (群レベル)、
(ii) 印刷文転記 = PDF 画像照合済。(iii) Lazard 転送は**不要になった** (群を直接構築)。
残作業: corrected E.4 (hdc 追加版) の証明 = issue 9402 (別トラック)。
