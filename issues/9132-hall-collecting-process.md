---
id: 9132
slug: hall-collecting-process
title: "CLAIM: Hall's collecting process (一般 class ≤ p−1) — BG App.E 全体の unlock"
created: 2026-07-18
---

# CLAIM (shared infra): Hall's collecting process — 一般 class ≤ p−1

**claim 主体**: lane c。**予定 leaf**: `OddOrder/GroupTheory/HallCollection.lean` (新規)。

## claim-before-build の事前検索 (2026-07-18 実施)

- repo 内で `Hall.*[Pp]etrescu` / `collecting process` / `hallCollection` / `collection_formula` を grep:
  ヒットは **`GroupTheory/CriticalSubgroup.lean` (class≤2 特殊例)** と `BG/AppE_FurtherResults.lean`
  (本 issue が unlock する側)、`AxiomsCheck.lean` (登録) のみ。**一般形は不在**。
- mathlib (`Mathlib/GroupTheory/`) に `Petrescu`/`collecting` のヒット **なし**。
- open 9000 issue に重複 claim なし (9109/9111/9130/9131 は無関係)。

⟹ **未構築の genuine shared infra**。重複再構築の恐れなし。

## なぜ本丸か: App.E の依存グラフの単一の根

```
E.1 (Hall's collecting process, 一般 class ≤ p−1)  ← ★根。前提なし・自己完結
 └─ E.2 Step1 → E.2(a) → E.2(b) → E.3(b)(c) → E.3(d) → E.4 → E.5
```
`OddOrder/BG/AppE_FurtherResults.lean` の **9 sorry を一括で開く唯一の unlock**。
App.E が BG §4/§5/§14/§15/§16 から要する他の前提は**全て repo に在る** (issue 3021 で確認済)。

## 内容

BG App.E の E.1 (Hall collection 公式) の一般形。現在 `AppE_FurtherResults.lean` に
**honest statement + sorry** で置いてある `hallCollection`:
> `∃ c : ℕ → G`, `(∀ r, 2 ≤ r → r ≤ n → c r ∈ γ_{r−1}(G))` かつ
> `x^n * y^n = (x*y)^n * collectionTail c n`、ここで `collectionTail` は順序付き積
> `c₂^{e₂}⋯cₙ^{eₙ}` (`List.prod` over `List.range' 2 (n-1)`、`eᵣ = n.choose r`)。
> 書籍の `Gᵣ` = `lowerCentralSeries (r−1)`。

これを一般 class ≤ p−1 で証明する。純粋な交換子計算で**上流依存なし**。

## 出発点 (既存の特殊例 — 再証明せず再利用/一般化)

- `GroupTheory.mul_pow_eq_commutator_pow_mul_of_class_le_two` (`CriticalSubgroup.lean:657`) — class≤2。
- `AppE.hallCollection_of_class_le_two` (本 session で証明済、上記に接続) — E.1 の class≤2 版。
- `GroupTheory.Omega.pow_eq_one_of_class_le_two`、class≤3 collection 公式 (`S04_SmallRankBasic.lean`)。
- `Isaacs/Ch04_Commutators/CommutatorBasics.lean` の交換子基本補題群。

## 進捗 (2026-07-18): 枠組み + class ≤ 3 まで landing、一般形は障害を特定して継続中

**新 leaf `OddOrder/GroupTheory/HallCollection.lean` (249 行、sorry 0、全 axiom-clean)**:
- `hallTail` — 順序付き尾部 `c₂^{C(n,2)}⋯cₙ^{C(n,n)}` (旧 `AppE.collectionTail` と**定義が字面まで同一**)。
  崩壊/吸収補題: `hallTail_block_eq_one` / `_eq_of_eq_one_of_three_le` / `_eq_of_eq_one_of_four_le` /
  `hallTail_eq_prefix_mul_top` (最上位スロットの指数は `C(n,n)=1`)。
- **`pow_succ_collect`** — 収集の 1 ステップ漸化式 (エンジン):
  `x^n y^n = (xy)^n T ⟹ x^(n+1) y^(n+1) = (xy)^(n+1) * (⁅x⁻¹,((xy)^n)⁻¹⁆ * T)^y`。**公理は propext のみ**。
- 深さ管理: `conj_mem_lowerCentralSeries` / `pow_succ_collect_mem` /
  `commutatorElement_mem_lowerCentralSeries_add` (`[γᵢ,γⱼ] ≤ γ_{i+j}`)。
- **`exists_hallCollection_of_residue`** — 固定 `n` の E.1 は `γ_n` を法とする合同そのもの
  (最上位スロットが残差を吸収)。⟹ **隠れた exactness を仮定していないことの保証**。

**`AppE.hallCollection_of_class_le_three`** — `γ₃ = 1` なら **全 `n` について E.1** が成立。
既存 class≤2 を真に包含。`c₂ = ⁅y,x⁆⁻¹(d₁d₂²)⁻¹`, `c₃ = (d₁d₂²)⁻¹`, `cᵣ=1 (r≥4)` と明示。
repo の `BG.Ch1.S04.mul_pow_eq_collect_of_triple_central` を走らせ、その weight-3 指数
`C(n+1,3)`, `2C(n+1,3)` を **Pascal 分割 `C(n+1,3) = C(n,2)+C(n,3)`** で Hall の形に変換
(= weight 3 で二項係数が正しく出る理由)。

⚠ **`hallCollection` (一般形) の statement は完全に不変** (diff で逐語一致を確認済) — 弱化なし。
repo 全体 sorry 22 → 22 (偽の削減なし)。AxiomsCheck に 3 件登録。

### 残る唯一の障害 (docstring にも記載)

枠組みにより E.1 は weight 帰納に帰着した。開いているのは:
> weight `2..k−1` を収集した残差 `w(n) ∈ γ_k` が、`γ_k/γ_{k+1}` の中で **`C(n,k)` 乗**であることを示す段。

これに必要なのは **(i) 自由冪零群と各 `γ_k/γ_{k+1}` の basic-commutator 基底**、
**(ii) 収集係数の `n` に関する多項式性 (Hall 多項式 / Lazard)**。
mathlib には `FreeGroup` はあるが**自由冪零商も basic commutator も無く**、`Petrescu`/`collecting` も皆無。
class ≤ 3 が回避できるのは、残差が中心 `γ₃` に落ち生成元が 2 つと明示できるため。

⟹ 次段は (i)(ii) の形式化。いずれも独立した shared infra で、これ自体が相当量。

## 完了条件

`HallCollection.lean` で一般形を book strength・sorry-free・axiom-clean で証明 →
`AppE_FurtherResults.lean` の `hallCollection` を接続 → E.2 以降を順に解錠。
AxiomsCheck 登録、survey 更新、本 claim を close。
(現状: 枠組み + class≤3 済。一般形は上記 (i)(ii) 待ち。)

## 参照
- issue 3021 (App.E de-opacify 済 + 依存グラフ)、`OddOrder/BG/AppE_FurtherResults.lean`。
- ⚠ shared infra (`OddOrder/GroupTheory/**`) ゆえ他レーンは着手前に本 claim を確認のこと。

## 出典調査 (2026-07-19、App.D 完了後に実測)

**BG は E.1 を証明していない** — 本文は引用のみ (PDF p.157):
> "The following result was proved by Philip Hall ... using his commutator collecting process.
> It may be found on pp. 37-41 of [26] and in many other books (e.g., [17, pp. 315-318])."

- `[26]` = **Suzuki, _Group Theory II_** (Grundlehren 248, 1986) — `references/` に無い。
- `[17]` = **Huppert, _Endliche Gruppen I_** (Grundlehren 134, 1967) — `references/` に無い。
- **Gorenstein には無い** (唯一の追加参照可能書): Ch.5 は §1 Frattini / §2-§3 p'-自己同型 /
  §4 p-groups of small depth / §5 extra-special / §6 associated Lie ring。
  regular p-group も collection formula も節が無く、`grep "collection\|regular p-group"` も空振り。
- **mathlib に無し** (`grep -rl "Petrescu\|collecting\|collection formula" Mathlib/GroupTheory/` = 空)。
- **Coq math-comp/odd-order にも無し** (`coq/theories/` に `BGappendixD/E` 自体が存在しない —
  App.D/E は FT 経路外ゆえ Coq 形式化の対象外)。

⟹ **参照可能な証明本体がどこにも無い**。自前で古典証明を再構成する (impasse なら
[[feedback-ask-chatgpt-for-elided-gaps]] の手順)。CLAUDE.md の「文献引用のみで本文に証明が
無い結果は恒久対象外にせず低優先繰延」に該当するが、**BG の残 sorry は App.E の 9 件のみ**
なので lane c の frontier としては live。

## 障害の正確な形 (2026-07-19 に独立検証)

repo の `exists_hallCollection_of_residue` により、E.1 は「weight `k` ごとに `γ_{k+1}` を法として
合わせる」帰納に帰着している (最上位スロットの指数 `C(n,n)=1` が残差を吸収するため)。
その帰納段で必要なのは:

> 残差 `R ∈ γ_k` の `γ_k/γ_{k+1}` (アーベル) における類が、**ある固定元 `c` の `C(n,k)` 乗**であること。

アーベル群の元が一般に `C(n,k)` 乗であるとは限らないので、これは自動でない。成立する理由は
`F = F(x,y)` の中で `γ_k(F)/γ_{k+1}(F)` が **weight `k` の basic commutator を基底とする自由
アーベル群**であり、収集係数が `n` の整数値多項式で、weight `k` 成分がちょうど `C(n,k)` の定数倍に
なること (Hall 多項式)。⟹ issue 記載の (i)(ii) が本当に要る、という当初評価を**再確認**した。

なお `⁅a, bⁿ⁆ ≡ ∏_i ⁅a,b;i⁆^{C(n,i)}` (左正規化交換子の 1 変数収集) は `n` の帰納で
独立に証明でき、weight 2 の係数が `C(n,1)=n` → Pascal で `C(n+1,2)` を出す仕組みそのもの。
**次段の最初の一歩はこれ** (自由群不要・自己完結)。

## ⭐ 進捗 (2026-07-19 夜〜): 骨格が全部そろい、組み立ての式が閉じた

`HallCollection.lean` 249 → 578 行 (sorry 0、全 axiom-clean)。3 commit:

1. **1 変数収集** `commutatorElement_pow_right_eq_prod_pow_choose`
   `d 1 = ⁅a,b⁆`, `d(i+1) = ⁅b, d i⁆`, `d i` が互いに可換 ⟹
   `⁅a, bⁿ⁆ = d₁^C(n,1) ⋯ dₙ^C(n,n)`。n の帰納 + Pascal。
   **自由群も basic commutator も不要**。`hallIter` (鎖の具体構成) と
   `hallIter_mem_lowerCentralSeries` (γ を降りる) つき。
   逆スロット版 `conj_pow_eq_prod_pow_choose`:
   `(y^i)⁻¹ z y^i = (e₁^C(i,1)⋯e_i^C(i,i))⁻¹ z`。
2. **展開 (仮説ゼロ)** `pow_mul_pow_eq_pow_mul_prod_collectionCommutator`
   `xⁿyⁿ = (xy)ⁿ · ∏_{i=1}^{n-1} (y^i)⁻¹ · w_{n-i} · y^i`,
   `w_m = collectionCommutator x y m = ⁅x⁻¹, ((xy)^m)⁻¹⁆`。
   `collectionCommutator_eq_commutatorElement_pow` により **w は固定文字
   `b = (xy)⁻¹` に対する単一族 `⁅x⁻¹, b^m⁆`** なので、1 変数収集が
   **m に依らない因子 `d_j = hallIter x⁻¹ (xy)⁻¹ j`** で全ステップを一括展開。
3. **二項畳み込み** `Nat.sum_range_choose_mul_choose`:
   `∑_{i≤n} C(i,l)C(n−i,j) = C(n+1,l+j+1)` (+ hockey stick の range 版)。

### 組み立ての計算 (紙の上で完了、γ₂ アーベルの場合)

`A := γ₂` がアーベルなら全因子が A に入り自由に並べ替えられる。A 上で y による
共役を作用素 `Y`、`N := Y − 1` (加法的自己準同型) と書くと `Y^i = ∑_l C(i,l)N^l`
(binomial、N の冪零性は不要 — C(i,l)=0 for l>i)。加法記法で

  T_n = ∑_{i=1}^{n-1} Y^i(w_{n-i}),  w_m = ∑_{j≥1} C(m,j) d_j
      = ∑_{l,j} (∑_{i=1}^{n-1} C(i,l)C(n−i,j)) N^l d_j.

畳み込みで内側の和は **l=0 のとき `C(n,j+1)`** (hockey stick)、
**l≥1 のとき `C(n+1,l+j+1)` = `C(n,l+j+1) + C(n,l+j)`** (Pascal)。⟹

  T_n = ∑_{j≥1} C(n,j+1)·d_j + ∑_{j,l≥1} [C(n,l+j+1)+C(n,l+j)]·N^l d_j
      = ∑_{r≥2} C(n,r)·c_r,
  c_r = d_{r−1} + ∑_{l+j=r−1, l,j≥1} N^l d_j + ∑_{l+j=r, l,j≥1} N^l d_j.

**weight が合う**: `d_j ∈ γ_{j+1}`, `N^l d_j ∈ γ_{j+l+1}` なので
`l+j=r−1 ⟹ γ_r`、`l+j=r ⟹ γ_{r+1} ⊆ γ_r`、`d_{r−1} ∈ γ_r`。全部 `c_r ∈ γ_r` ✓。
`r > n` の項は `C(n,r)=0` で消えるので尾部は `r = 2..n` に収まる ✓。
**`c_r` は n に依らない** (有限和)。⟹ **E.1 が metabelian で完全に出る**。

### これは当初評価 ((i) 自由冪零群 + (ii) Hall 多項式が要る) の更新

metabelian (= `γ₂` アーベル) は **class ≤ 3 を真に含み、どの class 上界にも
含まれない**大きなクラス。ここまでは自由群も basic commutator も Hall 多項式も
**一切要らない**ことが上の計算で確定した (要るのは畳み込み恒等式だけ)。
一般 class ≤ p−1 は metabelian に含まれないので E.1 一般形にはまだ届かないが、
一般形も **同じ計算を `γ_k/γ_{k+1}` の各アーベル切断で class について帰納**する
形になる見込み。次段はまず metabelian 版を Lean 化する。

### 次段の TODO (順に)

- [ ] `A = γ₂` アーベルのとき `↥A` に `CommGroup` を立て、`Additive ↥A` 上で
      y-共役を `AddEquiv` として取り出す (A は normal ゆえ well-defined)。
- [ ] `Y^i = ∑_l C(i,l) N^l` (`Commute.add_pow`; 有限和は `Finset.range (i+1)`)。
- [ ] 1 変数収集 (List.prod) を `Finset.sum` へ渡す橋。
- [ ] 展開式 → 二重和 → `Finset.sum_comm` → 畳み込み → Pascal → `c_r` の定義。
- [ ] `AppE.hallCollection` の metabelian 特殊化を接続 (一般形の sorry は残す)。

## ⚠ 2026-07-19 深夜: 文献調査で方針転換 — Lazard–Leibman ルートへ

subagent 2 本で「最短既知証明」と「既存形式化」を調査。**本 issue の従来の記述に
誤りが 2 つ**あったので訂正する。

### 訂正 1: 「自由冪零群 + basic commutator + Hall 多項式が要る」は誤り

**Mann の初等証明**が存在する: Dixon–du Sautoy–**Mann**–Segal, _Analytic Pro-p Groups_
2nd ed. (CUP 1999) **Appendix A, pp. 355-357** (2.5 頁)。公開 PDF:
`https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/ddsms.pdf`
(PDF p.374-376)。二項係数は **`{1..n}` の t 元部分集合の個数**という純粋な数え上げ
から出る (Hall 多項式の「多項式性」を経由しない)。
筋: `2n` 文字の自由群 `F` で `P_A := (∏_{j∈A} z₁ⱼ)(∏_{j∈A} z₂ⱼ)` を collection し、
`P_A = ∏_{∅≠B⊆A} Q_B` (`Q_S` は S の全ブロックに触れる交換子の積 ⟹ `Q_S ∈ γ_{|S|}`)
を作ってから `z₁ⱼ ↦ x, z₂ⱼ ↦ y` に特殊化する。同じサイズの `B` が `C(t,s)` 個ある
ことがそのまま指数になる。⚠ **`Q_S` の定義を再帰にすれば分解も support 性質も
自動**なので、**全内容は `Q_S ∈ γ_{|S|}(F)` 一点**に落ちる (自由積 `A₁∗⋯∗Aₙ` で
`⋂ⱼ ker(ブロック j を潰す) ≤ γₙ`)。

### 訂正 2: 「Petrescu 1977」は幻

実体は **J. Petresco, _Sur les commutateurs_, Math. Z. 61 (1954) 348-356**。
BG の文献表に Petresco/Petrescu の項目は無い (grep 済; BG は Huppert [17] と
Suzuki [26] のみ引用)。以後 **Hall–Petresco** と綴る。

### 既存形式化の状況 (2026-07-19 実測)

- **mathlib4 / Coq mathcomp / Isabelle AFP / Metamath / HOL Light / Mizar /
  agda-unimath: すべて無し。**
- mathcomp は weight 2 のみ (`solvable/commutator.v:126` `expMg_Rmul`)。
  **`coq/theories/BGsection4.v:62-89` は weight 3 を証明ローカルの `have expMR_fg`
  で手書き**しており、名前付き補題にしていない (= Gonthier らも regular p-group 理論を
  作らず必要な低 class 切り詰めをその場で証明した)。
- **`plby/Erdos90`** (Lean 4, 2026-06) に `petresco_two_generators` として完全形式化が
  存在する、と subagent が報告 (⚠ **以下は subagent 報告のままで未検証** — 私は
  リポジトリを開いていない。行数・sorry 有無・ライセンス表記はいずれも要確認):
  Magnus 埋め込み + basic commutator の重いルート (Hall 部分だけで ~6k 行、
  import closure 25k 行) を採っているとのこと。**軽いルート (Lazard–Leibman) を
  選ぶ判断を支持する規模感の材料**として記録する。
  **扱い (ユーザー裁定 2026-07-19): 参照してよい。コピペしなければよい。**
  = `coq/` submodule と同じ posture (戦略のヒント・前提の所在確認に読む、
  Lean へ直訳しない)。詳細は CLAUDE.md「外部形式化の参照」節。
- mathlib には **`⁅γᵢ,γⱼ⁆ ≤ γ_{i+j}` すら無い** (本 repo は
  `Isaacs.Ch04.commutator_lowerCentralSeries_le` として保有)。

### 訂正 3: metabelian ルートは critical path 外 (前節の計画を撤回)

`[γ₂,γ₂] ≤ γ₄` ゆえ **class ≤ 3 ⟹ metabelian**。逆は偽で metabelian は真に広いが、
**最初の非 metabelian ケースが class 4** で、BG が要る class ≤ p−1 (p ≥ 5) を含まない。
⟹ metabelian 版は genuine な定理だが **E.1 を unlock しない**。前節の組み立て計算は
正しいが、一般形の前に書く価値は低い。**採用しない**。

### 採用ルート = Lazard–Leibman (多項式列)

`∂_h f(n) := f(n+h)·f(n)⁻¹`。`f ∈ poly(Γ_•)` ⟺ k 重差分が常に `Γ_k` に入る。

1. ✅ **済 (2026-07-19)**: `n ↦ aⁿbⁿ` が多項式列であることの**閉じた形**
   (`OddOrder/GroupTheory/PolynomialSequences.lean`, 184 行, sorry 0):
   `∂_{h_k}⋯∂_{h_1}(aᵐbᵐ)(n) = ⁅a^{h_k},⁅…,⁅a^{h_2},b^{h_1}⁆…⁆⁆^{a^{n+h₁}}`。
   ⟹ `mulFwdDiffList_pow_mul_pow_mem`: k 重差分 ∈ γ_k。
   **これが Hall–Petresco のうち `aⁿbⁿ` 固有の内容の全部**。
2. [ ] `n ↦ a^{C(n,i)}` (`a ∈ Γᵢ`) が多項式列 (差分は `⟨a⟩` 内に留まり、指数は
   `C(n,i)` の有限差分)。
3. [ ] `Γ_{c+1} = 1`, `h ∈ poly`, `h(0)=⋯=h(c)=1` ⟹ `h ≡ 1`
   (`∂₁h ∈ poly(Γ_{•+1})` で c の帰納)。
4. [ ] ★ **Lazard–Leibman**: `poly(Γ_•)` が点ごとの積で閉じる。Leibniz 則
   `∂_h(fg) = (∂_h f)·(∂_h g)^{f}` + `⁅poly(Γ_{•+i}), poly(Γ_{•+j})⁆ ⊆ poly(Γ_{•+i+j})`。
   **唯一の重い部品** (~300-600 行見込み)。純代数で自由群もリストも不要、**再利用可能**。
5. [ ] Taylor 展開: `c_t := (∏_{s<t} c_s^{C(t,s)})⁻¹ g(t)` (Newton 再帰) と置くと
   2+4 より `h(n) := (∏_{s<t}c_s^{C(n,s)})⁻¹ g(n)` が多項式列で `h(0)=…=h(t−1)=1`、
   3 の議論 (`(∂₁)^t h(0)` が `h(t)^{±1}` に潰れる) から `c_t ∈ Γ_t`。⟹ E.1。
   ※ 本 repo の `exists_hallCollection_of_residue` (E.1 は γ_n を法とする合同)
   がちょうどこの Newton 形の別表現。

fallback = Mann ルート (段 4 の代わりに collection process 本体; リスト書き換え +
入れ子の整礎停止で ~300-700 行、単発使い捨て)。

## ⭐ 2026-07-19 深夜 (2): Erdos90 を実読 → **Mann ルートに決定** (ユーザー承認)

`references/erdos90` を submodule として取り込み、**自分で実読**した。前節で
subagent 報告に基づき書いた「Erdos90 は Magnus + basic commutator の重いルート」は
**誤り**。実際は **Mann/DDMS の support 論法そのもの**だった ⟹ 「重いルートを避けて
Lazard–Leibman」という前節の判断根拠が消えたので、評価をやり直して **Mann に切替**。

### Erdos90 の構造 (実測)

- `petrescoTerm x (w+1) = (∏_{j<w} petrescoTerm x (j+1)^C(w+1,j+1))⁻¹ · (∏ xᵢ^{w+1})`
  — **Newton 再帰で定義** ⟹ 恒等式は定義から自明。内容は全部
  `petresco_lower_series : petrescoTerm x w ∈ γ_w` に集約 (本 repo の
  `exists_hallCollection_of_residue` と同じ見立て)。
- 変数 = `G × Fin w` (生成元 × コピースロット)、`FormalCommutator X = FreeMagma X`、
  `formalWeight = 葉の個数`。形式語の積を **slot-support の濃度順にブロック分けして整列**し、
  ブロックの support がちょうど `S` なら weight ≥ |S|。
- ⭐ **整列の停止性を fuel で回避** (`collectFormalAux : ℕ → List → List`)。停止性の内容が
  「1 パスで selected 因子が 1 個減る」という**数え上げ補題**に落ちる。交換で生じる補正
  `⁅u,v⁆` の support は和集合 ⟹ 濃度順に処理していれば真に大きく selected でない、が効く。
- `petresco_collected_term` (collected value が |S| にしか依らない) = Mann Step 3。
  strong induction on |S| + 部分集合の個数 `C(|S|,k)` + Newton 再帰。
- 分量: `HallEmbeddings.lean` 12,167 行のうち **先頭 ~2,400 行**が Petresco 用
  (support ~380 / 収集エンジン ~900 / projected 版 ~380 / Petresco 固有 ~450)。
  ⚠ **厳密 support 版と projected 版の両方**を持っているが、**Hall には projected 版だけで足りる**。
- ⚠ **LICENSE 無し ⟹ コピペ不可**。Mann の数学的論証から自分で書く
  (fuel は Lean の定石であって彼らの表現ではない)。

### 両ルートの再評価

| | **Mann (support 論法)** | Lazard–Leibman |
|---|---|---|
| 分量見積 | 800–1,000 行 | 800–1,300 行 |
| リスク | **低** (完全実装が現存 ⟹ 閉じることが確認済、各段は初等的リスト操作、fuel で停止性リスク消滅) | **中〜高** (crux = 積で閉じることは**どの証明支援系にも例が無い**; Leibman 原論文 ~30 頁) |
| 再利用性 | 低 (Hall 専用) | 高いが**本 repo に他の需要が無い** ⟹ 実質の利点薄 |
| 一般性 | **m 生成元版がそのまま出る** (CLAUDE.md「特殊化債務は一般化する」に合致) | 2 生成元のみ |

⟹ **Mann 採用** (ユーザー承認 2026-07-19)。決め手は「分量同等・片方だけリスクが実測で潰れている」
＋ m 生成元版が副産物。

### 実装計画 (Mann)

新 leaf `OddOrder/GroupTheory/FormalCommutator.lean` + `HallCollectionCore.lean` 予定。

- [ ] `FormalCommutator X := FreeMagma X`、`weight = length`、`support`/`projSupport`、
      評価 `evalFC f (mul u v) = ⁅(evalFC u)⁻¹, (evalFC v)⁻¹⁆`
      (**古典規約 `[a,b]=a⁻¹b⁻¹ab`**; mathlib 規約だと交換恒等式に逆元が入るため。
      `E(u)·E(v) = E(v)·E(u)·E(⁅u,v⁆_formal)` が無条件で成り立つ形を選ぶ)。
- [ ] weight ≥ |projSupport| (葉の個数 ≥ ラベル像の濃度) / `evalFC c ∈ γ_{weight c}`。
- [ ] 収集エンジン: `extract`(fuel) → `collect` → support ごとの `split` → 濃度順の
      `splitSubsets`。不変量 = 「残りの因子の support 濃度は ≥ |S|」。
- [ ] Petresco 固有: 展開語 (生成元 × スロット) → 収集 → `collectedValue w S`。
- [ ] `collectedValue w S = hallTerm xs |S|` (strong induction on |S| + `C(|S|,k)` 個数)。
- [ ] `hallTerm xs w ∈ γ_w` ⟹ `AppE.hallCollection` を接続 (2 生成元は `xs = [x,y]`)。

### 併せて訂正するもの

- `AppE_FurtherResults.lean` の `hallCollection` docstring (~L105-125) が
  「(i) 自由冪零群 + basic commutator、(ii) Hall 多項式が両方とも不在なのが本当の障害」と
  書いているが**反証済**。Mann ルートはどちらも要らない。
- `PolynomialSequences.lean` (184 行、sorry 0、axiom-clean) は**残す** —
  「`n ↦ aⁿbⁿ` は多項式列」は独立した本物の結果。ただし Mann ルートでは critical path 外に
  なるので docstring にその旨を明記する。

## ✅ 2026-07-20: 完了 — Mann ルートで Thm E.1 を証明 (sorry-free / axiom-clean)

`AppE.hallCollection` の sorry が消えた。AppE sorry 9 → 8。**App.E 依存グラフの唯一の根が閉じた**。

### 成果物 (全て sorry 0、公理は propext / Classical.choice / Quot.sound のみ)

| leaf | 行数 | 内容 |
|---|---|---|
| `GroupTheory/FormalCommutator.lean` | 269 | 形式的交換子 (`FreeMagma X`)、weight/support、評価 (古典規約 `[a,b]=a⁻¹b⁻¹ab`)、交換恒等式 `E u·E v = E v·E u·E (u*v)`、`card_support_le_weight`、代入補題 |
| `GroupTheory/FormalCollection.lean` | 470 | 収集エンジン: fuel 付き `extract` → `collect_split` (1 パス) → `split_level` (濃度 k) → `split_levels` → `exists_split_supports` |
| `GroupTheory/HallPetresco.lean` | 400 | 展開語、スロット代入、レベルごとの数え上げ、`blockValue_eq_of_card_eq`、`prod_pow_card_eq_prod_hallValue`、`hallValue_mem_lowerCentralSeries`、`exists_hallPetresco` |

⟹ 合計 ~1,140 行。**当初見積り 800–1,000 行とほぼ一致**。

### 主定理 (m 生成元の一般形)

`OddOrder.GroupTheory.HallPetresco.exists_hallPetresco (xs : List G) (hn : 1 ≤ n)`:

    ∃ τ : ℕ → G, (∀ k, 1 ≤ k → k ≤ n → τ k ∈ γ_k) ∧ τ 1 = x₁⋯x_m ∧
      x₁ⁿ⋯x_mⁿ = τ₁^C(n,1)·τ₂^C(n,2)⋯τₙ^C(n,n)

**冪零性の仮定なし・class の上界なし・群に制限なし**。BG の 2 生成元形
(`AppE.hallCollection`) はこの系。CLAUDE.md の「特殊化債務は一般化する」に沿って
最初から m 生成元で作った。

### 証明の要 (Mann / DDMS App.A)

`xⁿyⁿ` を直に収集すると各交換子の出現回数を数える必要が生じ、そこで
「収集係数が `C(n,k)` で割れる ℤ-多項式」= Hall 多項式が要る。代わりに
**n 個のコピーそれぞれに固有のスロットを与えた展開語を 1 回だけ収集**し、各因子が
触れるスロット集合でブロック分けする。スロット集合 A の代入 (A の外の文字を 1 に潰す)
で **support ⊄ A のブロックが消え、残りは A を知らない** ので、
`x₁^{|A|}⋯x_m^{|A|} = ∏_{∅≠S⊆A} blockValue S`。左辺は |A| にしか依らないので
|A| の強帰納で **blockValue は |S| にしか依らない**。二項係数は
**n 元集合の k 元部分集合の個数**として現れる。
⟹ **自由冪零群も basic commutator も Hall 多項式も不要**。

技術的な要点 2 つ:
- 収集の停止性は **fuel 付き反復 + 数え上げ補題**に落ちる (整礎再帰を書かない)。
  交換で生じるブラケットは support が真に大きくなるので、濃度順に処理すれば
  「そのパスで選ばれる因子」が 1 回ごとにちょうど 1 個減る。
- 分解の出力は **support → ブロックの関数**でなければならない (`Forall₂` の対リスト
  では blocks が assignment に依存しうる)。1 つの分解を全ての A で使うのが Mann の肝。

### 本 claim は close 相当

残るのは E.2 以降 (AppE の 8 sorry) で、これは本 issue のスコープ外 (issue 3021)。
