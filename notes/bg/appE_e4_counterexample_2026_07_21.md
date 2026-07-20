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
