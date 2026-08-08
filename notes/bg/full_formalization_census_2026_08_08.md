# BG 完全形式化 — 番号 census と逐条監査 (2026-08-08 開始)

tracker = [issue 0177](../../issues/0177-bg-full-formalization.md)。
前身 = [0172 Peterfalvi (284 件)](../../issues/closed/0172-peterfalvi-full-formalization.md)
/ [0176 Isaacs (305 件)](../../issues/closed/0176-isaacs-full-formalization.md)、いずれも完了。

## 1. ⚠ BG は番号体系が前 2 冊と違う

Isaacs / Peterfalvi は `N.M.` を行頭に置く形式だったが、**BG は 2 系統ある**:

1. **`(N.M)` を単独行に置くラベル** — **証明内の主張ラベル**であって定理番号ではない。
   §3 の証明中に `(3.6)` `(3.7)` `(3.8)` が並び、後段が「by (3.6)」と参照する。
   ⚠ **これを定理番号と取り違えると件数が数倍に膨らむ**。
2. **`Kind N.M.` / `Kind N.M (帰属).`** — こちらが番号付き結果。
   `Theorem` / `Proposition` / `Lemma` / `Corollary` の 4 種。

さらに **Theorems A–E** (章番号を持たない主定理、`Theorem A` のように単独行) と
**Appendix A–E** (`Kind X.N` 形式) を持つ。

### 抽出パターン

```python
def sp(w): return r'\s*'.join(w)          # OCR が T h e o r e m と分解するため
kinds = "|".join(sp(w) for w in ["Theorem","Proposition","Lemma","Corollary"])
pat = re.compile(r'^\s*(' + kinds + r')\s+(\d(?:\s*\d)?)\s*\.\s*(\d(?:\s*\d)?)(?!\s*\.\s*\d)')
```

⚠ **`(?!\s*\.\s*\d)` が必須** — `Theorem 6.4.1` のような **Gorenstein の引用**を除外する
(BG は "**G**, Thm X.Y.Z" 形式で Gorenstein を多用する)。

## 2. 実測ベースライン (2026-08-08)

| 節 | 件数 | 備考 |
|---|---|---|
| §1 | 22 | |
| §2 | 7 | |
| §3 | 10 | |
| §4 | **20** | ⚠ 4.1 は OCR が `Lemma-4.1.` (ハイフン) と書き出しており空白許容パターンでも漏れる |
| §5 | 7 | |
| §6 | 7 | |
| §7 | 6 | ⚠ 7.1 は OCR が `L e m m a 7.1.` (文字分解) |
| §8 | 1 | |
| §9 | 6 | |
| §10 | 14 | |
| §11 | 7 | |
| §12 | 19 | |
| §13 | 13 | |
| §14 | **13** | ✅ **14.11 解決 (2026-08-08)** — 下記 |
| §15 | 9 | |
| §16 | 1 | |
| **小計** | **162** | (§1-§16 の番号付き結果、確定) |

### ✅ 14.11 が「未発見」だった理由 — header が前段落の行末に貼り付いていた

ページ画像は不要だった。pdftotext L6051 は

```
related to those of type ^ 2 Lemma 14.11. Suppose that M G ^ j r , E is a complement of MG in M,
```

で、**`Lemma 14.11.` が前の段落の最終行の末尾に続いている**。抽出パターンは
`^\s*(Kind)` と**行頭アンカー**なので原理的に取れない。

⟹ 非アンカー版で **BG 全文を再走査**したところ、**この 1 件だけ**が行頭アンカーで漏れていた
(他の 15 節に glued header は無い)。よって §1-§16 の総数は **162 件**で確定。

**Lem 14.11 の statement**: `M ∈ 𝓜_𝒫`, `E` を `M_σ` の `M` 内補群、`q ∈ π(E)`,
`Q ∈ ℰ_q¹(E)`, `Q ⊄ F(E)` ⟹ ある `M* ∈ 𝓜` が存在して
(1) `q ∈ τ₂(M*)` かつ `𝓜(C_G(Q)) = {M*}`、または (2) `q ∈ κ(M*)` かつ `M* ∈ 𝓜_𝒫`。
実体 = `S14_TypePCounting/KappaHallCommutator.lean` (`BG Lemma 14.11` 記載あり)。

⚠ **誤判定様式**: 行頭アンカーの機械抽出は「番号付き結果の見出しが常に行頭にある」ことを
仮定している。OCR (や組版) はこれを破る。**「欠番」を見つけたら非アンカー再走査を先にやる**
(ページ画像より安い)。

**Theorems A–E**: 5 件 (`Theorem A` L6615 / `B` L6602 / `C` L6653 / `D` L6669 / `E` L6692)。

**補章**: `Kind X.N` が 14 件 (A: 2-5 / B: 2-4 / C: 2-3 / D: 2 / E: 2-5)。
⬜ **各補章の `.1` が未発見** — 補章の第 1 結果は別形式 (章タイトル直後など) の可能性。要確認。

⟹ **暫定合計 ≈ 180 件** (§1-§16 の 161-162 + Theorems A-E の 5 + 補章 14+)。

## 3. ⚠ この census が測っていないもの (0172 / 0176 と同じ)

1. **特殊化債務** — 書籍より狭い仮説
2. **部分被覆** — 多条項の一部だけ / TFAE の条項数不足
3. **packaging 差** — 条項はすべて在るが書籍の statement の形になっていない
4. **mathlib 被覆の未記録** — Isaacs で主役だった型。BG は FT 固有の内容が多いので前 2 冊より
   少ないと予想されるが、**§1 (Preliminary Results) は標準的な有限群論**なので要確認。

## 4. 逐条監査

### §1 Preliminary Results (22 件、書籍 pp.1-30) — **監査完了 (2026-08-08)**、補充ゼロ

**22/22 参照あり**。`S01_FrattiniBurnside.lean` の file header が §1A-§1G の全番号を
Isaacs / mathlib / 本 repo の 3 列で対応づける**マスター対応表**を持っており、それを
実体で裏取りした。

⚠ **stale 注記を 2 件訂正** — 対応表に「**Phase 1 待ち**」のまま残っていた:

| 番号 | 表の記載 | 実体 |
|---|---|---|
| **Thm 1.8** (Burnside, operator on `p`-group) | 「mathlib: (Ch.1 §1B TODO) / 本ファイル: **Phase 1 待ち**」 | ✅ `S01_BurnsideOperator.burnside_operator` (元形も :153) |
| **Thm 1.11** | 「mathlib: Phase 1 Ch.4 §4D / 本ファイル: **Phase 1 待ち**」 | ✅ `Isaacs/Ch04_Commutators/Main/BaerTrick.lean:254` (docstring が「= BG Thm 1.11」と明記) |

🚨 **1.8 は同一ファイル内で矛盾していた** — :63 の表が「Phase 1 待ち」なのに、
**同じファイルの :152** が `Thm 1.8` `burnside_operator` ⭐ sorry-free` と記録していた。
⟹ **1 つの file 内でも注記どうしが食い違う**。Isaacs 監査で「注記は判定の証拠ではない」を
確立したが、BG ではさらに強く「**同じ file の別の注記とすら一致しない**」ことがある。

⚠ **1.11 は Isaacs 側のディレクトリに在る** — owner chapter 規則。BG のディレクトリだけ
見ると「未形式化」と誤判定する (Isaacs 2.20 / 3.15 / 3.23 と同じ型で通算 4 回目)。

その他の §1 は mathlib 被覆と repo 実装が対応表どおり:
`Lem 1.7` は 4 条項 (a)/(b)(c⇒)(d⊇)/(c⇐)/(d⇐) に分けて全て sorry-free、
`Thm 1.13` = `GroupTheory.CriticalSubgroup` の `thompson_critical_omega`、
§1F (`Thm 1.17`/`1.18`/`Cor 1.19`/`Thm 1.20`) は **mathlib 直接**。

⟹ **§1 全 22 件被覆・補充ゼロ**。

### §2 Representation Theory (7 件) — **監査中 (2026-08-08)**

書籍の 7 件:

| BG | 書籍の主張 |
|---|---|
| Prop 2.1 | `M` 既約 `FG`-加群 ⟹ (a) 絶対既約 ⟺ `Hom_{FG}(M,M) = F` ほか |
| Prop 2.2 | `H ⊴ G`、`G/H` 巡回、`F` 代数閉、`M` 既約 `FH`-加群で `M ≇ M^x` ⟹ … |
| Lem 2.3 | `G` 可解、`M` 絶対既約 ⟹ `dim M ∣ \|G\|` (Fong–Swan) |
| Prop 2.4 | `dim V = q > 2`、`g` が位数 `n > 2` の可逆線形変換 ⟹ … |
| Thm 2.5 | extraspecial `p`-群 `P` (位数 `p^{2n+1}`) と巡回群 `H` の半直積 ⟹ … |
| Thm 2.6 | 奇位数 `G` が 2 次元 `FG`-加群に忠実に作用 ⟹ (a)(b) |
| Lem 2.7 | `P`, `Q` が位数 `p²`, `q²` の基本可換群、`Q ⊆ Aut(P)` ⟹ (a) `q ∣ p−1` ほか |

**確認済**:

* **Prop 2.1** = `BG.Ch1.S02.absolutely_irreducible_iff_hom_eq_F`
  (`S02_RepresentationPropositions.lean:84`)
* **Thm 2.6** = (a) `odd_two_dim_abelian` / (b) `isPGroup_commutator_of_faithful_two_dim_charP`
  (`S04_PGroupsSmallRank.lean` から 2 条項とも引用されている)

**`S02_RepresentationPropositions.lean` は 286 行あるが top-level `theorem` は §2A の 1 本だけ**。
§2B-§2E は**方針を記した見出しだけ**で、実体は shared module に置かれている (または未実装)。
各見出しの記載と実体を突合した結果:

| BG | 見出しの記載 | 実体 |
|---|---|---|
| **Prop 2.2** | 「**形式化状態 (2026-07-18 更新, 旧 docstring は stale だった)**: 両パートとも形式化済み・sorry-free」 | ✅ `RepresentationTheory/CliffordMultiplicityOne.lean` / `CyclicExtension.lean` / `CyclicCharacterExtension.lean` |
| **Lem 2.3** (Fong–Swan) | 「形式化方針」+ **「(stub 未配置: forward dependent 不在のため §2 完成後または…)」** | ⚠ **注記が stale** — 実体は `RepresentationTheory.finrank_dvd_card_of_isAbsolutelyIrreducible` で **AxiomsCheck 登録済** (`AxiomsCheck.lean:6325`) |
| **Prop 2.4** | 「形式化方針」+ **「(stub 未配置: 10 部を個別 lemma 化, shared module 作成後.)」** | ⚠ **注記が stale** — `GroupTheory/RepresentationTheory/EigenspaceUnderCyclicAction.lean` は**既に存在する** |
| **Thm 2.5** | 「形式化方針」+ **「(stub 未配置: 依存定理多数, foundation 整備後に着手.)」** | ⚠ **注記が stale** — 実体は `RepresentationTheory/ExtraspecialThm25Final.lean` の `finrank_modEq_of_extraspecial` (:63) / `finrank_eq_sub_one_of_extraspecial` (:89)。**ファイル名に `Thm25` が入っている**のに計画表が追随していなかった。消費点 `S03d_Thm34.lean:31` も「keystone consumer of BG Theorem 2.5」と明記 |

✅ **Thm 2.5 は実体あり (2026-08-08 確定)** — 計画表が挙げる `AutElementaryAbelian.lean` は
存在しないが、実体は **`ExtraspecialThm25Final.lean`** に別名で在った。
消費点 `S03d_Thm34.lean` (BG §3 Thm 3.4) が「keystone consumer of BG Theorem 2.5」と
明記しており、そこから辿れた。⟹ **消費点から辿るのが確実**。

🟢 **Lem 2.7 は既に形式化済だった (2026-08-08 に自己訂正)**

⚠ **この節は最初「Lem 2.7 = BG §1-§2 で唯一の真の未形式化」と誤判定していた。**
実体は **2 系統・独立に 2 回**形式化されていた:

| 実体 | 場所 | 由来 |
|---|---|---|
| `elemAbelian_aut_action` (a)(b) 一括 | `GroupTheory/RepresentationTheory/ElemAbelianAutAction.lean` | issue **3009** (2026-07-18, 「book strength」と明記して close) |
| `prime_dvd_sub_one_of_faithful_rank_two` (a) / `exists_powerMap_of_faithful_rank_two` (b) | `GroupTheory/RepresentationTheory/SingerReducibility.lean` | issue **0150** |
| crux = **G** Thm 3.2.3 | 同 `isCyclic_of_faithful_isIrreducible` | 3009 |

いずれも sorry-free・AxiomsCheck 登録済 (`AxiomsCheck.lean:4737` / `:4744` / `:6362`)。

### 🚨 なぜ「無い」と誤判定したか — 誤判定様式の実例 4 つ

1. **書籍ラベルで grep した** — `Lem 2.7` / `Lemma 2.7` を引くと Isaacs の Lemma 2.7 が当たり、
   BG の実体は当たらない。実体のファイル名は `ElemAbelianAutAction` / `SingerReducibility` で、
   **結論の形 (概念名)** でしか引けない。[[grep-concept-names-not-book-notation]]
2. **`AxiomsCheck.lean` を走査しなかった** — そこには「**BG Lemma 2.7(a)**」「**BG Lemma 2.7(b)**」
   と*明示的に*書かれていた。**AxiomsCheck は書籍番号 ↔ 実体の最良の索引**であり、
   逐条監査では最初に引くべき。
3. **`issues/closed/` を走査しなかった** — `0150-bg-lemma-2-7-rank-two-action.md` と
   `3009-lem27-elem-abelian-aut.md` が両方 close 済で残っていた。
4. **§2 の計画表 (`S02_RepresentationsBasic.lean`) が §2A-§2F の 6 件しか追っていない**という
   観察は**正しかった**が、そこから「repo に実体が無い」と結論したのが誤り。
   **計画表の欠落 ≠ 実体の欠落** (実体は BG ディレクトリの外に置かれていた)。

⟹ **逐条監査の走査対象を確定**: (i) `AxiomsCheck.lean` の番号コメント、
(ii) `issues/closed/`、(iii) 結論の形での repo 全体 grep、(iv) 節ディレクトリ。
(iv) だけでは足りない。

### ✅ 本監査の実収穫 — packaging 差 1 件を解消

書籍の statement は **群** `P`, `Q` (基本可換, 位数 `p²`, `q²`) と `Q ⊆ Aut(P)` だが、
既存の 2 実装はいずれも **加群形** (`[Module (ZMod p) P]` + `finrank = 2` +
faithful `Representation`)。`ElemAbelianAutAction.lean` の docstring は
「これは `Q ⊆ Aut(P)` の忠実な表現である」と**散文で主張**していたが、
その rendering 自体は形式化されていなかった (= 監査基準の「packaging 差」)。

⟹ 追加 (2026-08-08) = **新規 leaf 1 本のみ**
`OddOrder/BG/Ch1_Preliminary/S02_Lemma27Group.lean` (~130 行):

* `elemAbelian_aut_action_ofModule` — 群形 (加群構造は**インスタンス引数**のまま)
* `bgLemma27` — **書籍どおりの形**:
  `hPea : IsElementaryAbelian p P`, `Nat.card P = p^2`, `φ : Q →* MulAut P` 単射 ⟹
  `q ∣ p - 1` ∧ `∃ a ≠ 1, ∃ r : ℕ, (∀ x, φ a x = x ^ r) ∧ r^q ≡ 1 [MOD p] ∧ ¬(r ≡ 1 [MOD p])`

数学は既存の `elemAbelian_aut_action` に委譲 (再証明していない)。
橋渡しも**既存のものだけ**を使う:
`IsElementaryAbelian.zmodModule` (PRank) / `OddOrder.BG.Ch1_Preliminary.mulAutToEnd`
(OperatorMaschke) / `OddOrder.GroupTheory.zmod_smul_ofMul` (CommGroupAut)。

### 🚨 補助 def も「無い」と思ったら 3 個あった

最初 `mulAutToEnd` (`MulAut E →* Module.End (ZMod p) (Additive E)`) と
「スカラー倍 = 冪」補題を**新規に PRank へ足した**が、どちらも既存だった:

| 実体 | 場所 |
|---|---|
| `mulAutToEnd` (public, 10+ 箇所で使用) | `BG/Ch1_Preliminary/OperatorMaschke.lean:140` |
| 同 (private の重複) | `BG/AppA_PStability.lean:143` — **2026-08-08 に削除し共有版へ寄せた** |
| `zmod_smul_ofMul` | `GroupTheory/CommGroupAut.lean:111` |

しかも新設した `mulAutToEnd` は `ExtraspecialSinger.lean` で**名前解決の曖昧化を起こして
ビルドを壊した** (引数順が違う `(p) {E}` vs `(E) (p)` なので型エラーとして出た)。
⟹ **汎用の小さい def を足す前に、名前と「型の形」の両方で grep する**
([[grep-abbreviations-not-just-full-names]] [[grep-before-writing-transport-defs]])。
✅ `AppA_PStability.lean` の private 複製は**同日中に除去**し `OperatorMaschke` の共有版へ寄せた
(`def mulAutToEnd` は repo 全体で 1 本)。`OperatorMaschke` 側の docstring に
「共有版・4 つ目を新設しないこと」と今回の破壊事例を明記した。

### ⚠ 加群構造は `letI` でなくインスタンス引数で渡す

`IsElementaryAbelian.zmodModule` を `letI` で束縛すると `Additive P` の
`Module.Finite` / `FunLike` 合成が詰まる (PRank の `addAutEquivGL` docstring に既出の罠)。
実際に `ρ b (Additive.ofMul x)` が **"Function expected"** で落ちた。
⟹ 加群を使う補題は `[Module (ZMod p) (Additive P)]` を**インスタンス引数**に取り、
`letI` は最外殻 (`elemAbelian_aut_action_group`) だけに置く。

### 書籍の statement (L1329、2 条項)

> `p`, `q` を相異なる素数、`P`, `Q` をそれぞれ位数 `p²`, `q²` の基本可換群、
> `Q ⊆ Aut(P)` とする。このとき
> **(a)** `q ∣ (p − 1)`、
> **(b)** ある `a ∈ Q^#` と整数 `r` が存在して、**すべての** `x ∈ P` で `x^a = x^r`、
> かつ `r^q ≡ 1 (mod p)`、`r ≢ 1 (mod p)`。

⚠ **OCR の罠 3 種がこの 1 文に同居している** (statement 確定時に踏んだ):
* `(/ divides` = `q divides` (`q` が `(/` に化ける)
* `a £ Q^` = `a ∈ Q^#` (`∈` が `£` に化ける)
* **`rq = 1 (mod p)` は `r^q ≡ 1 (mod p)`** — [[pdftotext-drops-superscripts]] そのもの。
  **添字に「文字+文字」を見たら指数を疑う**。ここを `r·q ≡ 1` と読むと別の (偽の) 主張になる。

⚠ `AppE_CentralizerDecomposition.lean:106` の「`q ∣ p − 1`」は **BG Thm E.3(a)** であって
Lem 2.7 ではない (結論の字面が同じなので取り違えやすい)。
### 🚨 §2 の所見 2 — 「番号の抜け」は計画表の区分からも起きる

repo の §2 計画は **§2A(2.1) / §2B(2.2) / §2C(2.3) / §2D(2.4) / §2E(2.5) / §2F(2.6)** と
**書籍の 6 件に節記号を割り当てる形**で作られており、7 件目の **Lem 2.7 に対応する節記号が無い**。
⟹ **節記号ベースの計画表は「書籍の番号を全部数えたか」を保証しない**。
本キャンペーンのように**書籍側から機械抽出した番号リストと突合**しないと発見できない型。
(Peterfalvi/Isaacs では計画表が番号ベースだったのでこの型は出なかった。)

### 🚨 §2 の所見 — 「stub 未配置」注記が信用できない

§2 の 4 つの「形式化方針」見出しのうち **2 つ (Lem 2.3 / Prop 2.4) の「stub 未配置」が stale**
だった。しかも **Prop 2.2 の見出し自身が「旧 docstring は stale だった」と書いている** —
つまりこのファイルは**過去に一度同じ問題を起こして直した履歴を持ちながら、隣の項目が
また stale になっている**。

⟹ BG の「stub 未配置」「foundation 整備後に着手」「Phase 1 待ち」といった**未着手を示す
注記は、一律に実体で裏を取る**。§1 の Thm 1.8 / 1.11 と合わせて、BG だけで既に 4 件。

### ⚠ 書籍間の番号衝突 (2026-08-08 に踏んだ)

`2.6` を repo 全体で grep すると **Isaacs の Thm 2.6** (`Ch02.isMinimalNormal_le_normalizer_of_isSubnormal`)
が先に当たる。BG / Isaacs / Peterfalvi は `1.x`-`16.x` の範囲で番号が全面的に衝突するので、
**BG の監査では検索を BG 文脈 (パス `/BG/` か行内の "BG" マーカー) に絞る必要がある**。
⚠ ただし owner chapter 規則で **BG の結果が Isaacs 側に置かれている**ことがある
(BG Thm 1.11 = `Isaacs/Ch04_Commutators/Main/BaerTrick.lean`)。
⟹ **絞って引いた後、ゼロ件のものだけ repo 全体を「BG」マーカー込みで再検索する**という
2 段構えが要る。

## §3 (Actions of Frobenius Groups and Related Results) — 進行中

書籍 10 件: Lem 3.1 / Lem 3.2 / Lem 3.3 / Thm 3.4 / Thm 3.5 / Thm 3.6 / Thm 3.7 / Thm 3.8 /
Prop 3.9 / Thm 3.10。**未形式化ゼロ** (全 10 件に実体あり)。

### 走査は新しい順序で実施 (AxiomsCheck → issues/closed → 結論の形 → 節ディレクトリ)

§2 の失敗を受けて順序を変えた結果、**番号 grep では出ない 2 件が第 1 手/第 3 手で出た**:

| BG | 実体 | どう見つけたか |
|---|---|---|
| **Lem 3.1** | `isFrobeniusGroup_iff_complement_centralizer_inf_kernel_eq_bot` (`S03_FrobeniusActions.lean:81`) | **結論の形** (`IsFrobeniusGroup … ↔`) で grep。宣言名にも docstring 以外にも「3.1」は無い |
| **Thm 3.7** | `IsFrobeniusGroup.isNilpotent_kernel` (`Isaacs/Ch06_FrobeniusActions/KernelNilpotent.lean`) | owner chapter 規則で **Isaacs 側**に在った (通算 5 回目) |
| Lem 3.2 | `isFrobeniusGroup_quotient_of_normal_not_le_kernel` ほか 2 本 | AxiomsCheck:6746-6748 |
| Lem 3.3 | `S03b_Lemma33.lean` (Wielandt) | 節ディレクトリ |
| Thm 3.4/3.5/3.6 | `S03d_Thm34` / `S03e_Thm35` / `S03f_Thm36` | AxiomsCheck:6490/6575/6687 |
| Thm 3.8 / Prop 3.9 / Thm 3.10 | `S03h_Thm38.thm38` / `isCyclic_of_isPGroup_of_isFrobeniusAction` / `S03g_Thm310*` | AxiomsCheck:6749/6691/6352+ |

### ✅ Lem 3.1 は書籍強度で一致 (ページ画像で確定)

⚠ **pdftotext は (b) の行を丸ごと落としていた** (`(b)` の後が空行)。
`references/bg/pages/bg-p017.png` (PDF p.30 = 書籍 p.17、offset **+13**) を読んで確定:

> **(b)** `C_K(x) = 1` for all `x ∈ R^#`

repo の `iff` は仮説 (`K ⊴ G` / `IsComplement' K R` = `KR = G ∧ K ∩ R = 1` / `K ≠ ⊥` / `R ≠ ⊥`)
も両条項も一致。⟹ **書籍強度 OK**。
⟹ **条項が OCR で消えることがある** — 「(a)(b) の (b) が見当たらない」ときは欠番でなく
**OCR 落ち**を疑い、ページ画像で確認する。

### 🔴 実収穫: 特殊化債務 2 件 — 書籍自身が「不要」と書いている仮説

**書籍の Note を読まずに statement だけ写すと入る**型。BG は Lem 3.2 と Thm 3.5 の直後に
**同じ Note** を置いている:

> **Note.** Since Thompson's Thesis … implies that the kernel of a Frobenius group is nilpotent,
> the assumption that `K` is solvable is unnecessary.

しかし repo の 5 宣言はすべて `IsSolvable ↥K` を仮説に持っていた (= Note **以前**の形):

  S03.inf_complement_eq_bot_of_normal_not_le_kernel   (hSolvK : IsSolvable ↥K)
  S03.normal_le_kernel_of_not_le                      (hSolvK : IsSolvable ↥K)
  S03.isFrobeniusGroup_quotient_of_normal_not_le_kernel (hSolvK : IsSolvable ↥K)
  S03e.thm35_algClosed                                (hKsolv : IsSolvable ↥K)
  S03e.thm35                                          (hKsolv : IsSolvable ↥K)

しかも **Thompson は repo に在る** (`IsFrobeniusGroup.isNilpotent_kernel`) ので、
仮説は機械的に discharge できる。⟹ 新 leaf
`OddOrder/BG/Ch1_Preliminary/S03_WithoutSolvableKernel.lean`:

* `isSolvable_kernel_of_isFrobeniusGroup` — Note そのもの (Thompson + nilpotent ⟹ solvable)
* `bgLemma32` (a)+(b) / `normal_le_kernel_of_not_le'` / `inf_complement_eq_bot_..._'`
* `bgThm35` / `bgThm35_algClosed`

### ⚠ なぜ「その場で一般化」でなく別 leaf か (import cycle)

`KernelNilpotent` (Thompson) は `BG.Ch1_Preliminary.S03c_Thm37` を import し、
それが `S03_FrobeniusActions` を import する。よって `S03_FrobeniusActions` で
Thompson を使うと **cycle**。⟹ 一般形は両者の下流に置く。
`IsSolvable` 付きの旧版は §3 の内部エンジンとして残す (そこでは solvability が既に手元にある)。
⚠ CLAUDE.md の「一般版を証明 → 旧版をその特殊化に置換」は、
**依存階層がそれを許すときだけ**在place でできる。

### ✅ 残り 6 件の条項照合 (2026-08-08 完了)

| BG | repo の endpoint | 照合結果 |
|---|---|---|
| **Lem 3.3** | `S03b.centralizer_ne_bot_of_nontrivial_kernel` | ✅ 一致 (`char F ∤ \|K\|` = `(Nat.card K : F) ≠ 0`、結論 `∃ v ≠ 0, ∀ r ∈ R, ρ r v = v`) |
| **Thm 3.4** | `S03.thm34` (一般体) / `thm34_algClosed` | ✅ 一致。`FiniteDimensional` は**書籍の大域規約**であり債務でない (下記) |
| **Thm 3.6** | `S03f.thm36` | ✅ 一致 (`R₀ ≤ R` 素数位数・`C_H(R₀)` が Z-群 ⟹ `⁅H,R⁆` は全素数 `p` で `p`-length one) |
| **Thm 3.8** | `S03h.thm38` | ✅ 一致 (3 条件そのまま、結論 `⁅K,R⁆ ≤ F(K)`) |
| **Prop 3.9** | `S03.isCyclic_of_isPGroup_of_isFrobeniusAction` | ✅ **書籍より強い** — 書籍の「`H` は `p'`-群」を落としている (docstring に明記済) |
| **Thm 3.10** | `S03g.bgThm310` (新設) | 🔴 **部分被覆だった** — 下記で解消 |

### 🔴 実収穫 2: Thm 3.10 の (a) が group level に無かった (部分被覆)

**症状**: `bgThm310_nilpotent` (一般 nilpotent `M` の capstone) の結論は **(b)+(c) のみ**で、
docstring も「Part (a) (`R` of prime order) is `M`-independent and is **provided elsewhere**」と
書いていた。しかし "elsewhere" = `prime_card_complement_of_frobenius_conj` は
**Frobenius kernel が可換**という仮説付き (§14.2(g) 専用の共役形) で、書籍の (a) を満たさない。

⚠ **AxiomsCheck の注記は (a) を「在る」と読ませる形だった** — `6712` が
「BG Theorem 3.10 **(a)+(b)**, general (non-abelian) kernel」、`6734` が
「(a)+(b), elementary-abelian **GROUP** case, general kernel」と書いており、番号 grep でも
注記読みでも「(a) は在る」と見える。実際そこに在るのは **module leaf**
(`prime_card_and_finrank_of_elemAbelian_general`) までで、**group form の
`bgThm310_elemAbelian_group` は (b)+(c) しか返していなかった** (= (a) を捨てていた)。
⟹ **注記の "(a)+(b)" は「その周辺で (a) も証明済」の意であって、
endpoint の結論に (a) が入っている保証ではない**。結論の型を読むこと。

**解消 (2026-08-08)**:

1. `S03g_Thm310GroupForm.bgThm310_elemAbelian_group` — 結論に (a) を追加
   (`∃ p', p'.Prime ∧ Nat.card ↥R = p'`)。証明は既存の module leaf
   `prime_card_and_finrank_of_elemAbelian_general` を、既に組んである仮説翻訳
   (`hCK'` / `hcond3'` / `hIsFrob.conj_frobenius`) にそのまま食わせるだけ。
2. `S03g_Thm310Nilpotent.bgThm310_nilpotent_aux` / `bgThm310_nilpotent` — (a) を dévissage に通す。
   **base case** は 1 で得た (a) をそのまま、**step case** は `resN.1`
   (`N ◁ M` への帰納法仮説) をそのまま返す — (a) は `M` に依らないので step は無証明。
3. `S03g_Thm310Nilpotent.bgThm310` — **書籍どおりのパッケージを新設**:

   ```
   ∃ p, p.Prime ∧ Nat.card ↥R = p ∧ IsCyclic ↥R ∧
     Nat.card M = Nat.card ↥C_M(R) ^ p ∧
     (IsCyclic ↥C_M(R) → ∀ g ∈ ⁅K,K⁆, ∀ m, g • m = m)
   ```

   * (a) が書籍の「`R` is **cyclic** of prime order」まで含む (`isCyclic_of_prime_card`)
   * (b) の指数が書籍どおり `p` (`|R|` でなく)
   * `hRne` / `hKne` を**仮説から除去** — `IsFrobeniusGroup` の `ne_bot_kernel` /
     `ne_bot_complement` フィールドから取れる (書籍も Frobenius 群の定義に含めている)

⟹ AxiomsCheck に `bgThm310` を登録 (axiom-clean 確認済)。

### 📌 BG の大域規約 2 本 (監査の判定に効く — 全節で有効)

書籍を読み直して確定 (これを知らないと**偽の特殊化債務**を起票してしまう):

| 規約 | 出典 | 監査上の意味 |
|---|---|---|
| 「All groups considered in this work will be **finite** except when explicitly stated otherwise」 | 書籍 p.4 (L612) | `[Finite G]` は書籍強度 |
| 「In this section, we consider representations … by **finite-dimensional** linear transformations. … By module we will always mean **finite-dimensional** right module」 | 書籍 p.9, §2 冒頭 (L961-967) | **`[FiniteDimensional F V]` は書籍強度** — Thm 3.4 / Thm 3.5 等の module 系 statement に付いていても債務でない |

⚠ Thm 3.4 は書籍の statement 本体に「finite-dimensional」と書いていないので、
**§2 冒頭の規約を読まないと「repo が書籍より狭い」と誤判定する**。
[[repo-stronger-hypothesis-is-specialization-not-gap]] の逆向きの罠。

### ✅ §3 = 全 10 件・書籍強度で被覆 (2026-08-08 完了)

未形式化ゼロ / 部分被覆ゼロ / 特殊化債務ゼロ (Lem 3.2・Thm 3.5 の可解性は
`S03_WithoutSolvableKernel.lean` で解消、Thm 3.10 (a) は上記で解消)。

## §4 (p-Groups of Small Rank、20 件 = 4.1-4.20) — 進行中

### 第 1 走査: 20/20 に候補あり (2026-08-08)

`OddOrder/BG/Ch1_Preliminary/S04*.lean` (17 file) の docstring から番号を機械抽出すると
**4.2-4.20 の 19 件**が当たる。**4.1 だけがディレクトリに無い**が、これは
「`G/Z(G)` 巡回 ⟹ `G` 可換」で **mathlib 被覆** (`commutative_of_cyclic_center_quotient`,
`Mathlib/GroupTheory/SpecificGroups/Cyclic.lean`)。BG 自身も証明を書かず
**G** Thm 1.3.4 に投げている。

| 番号 | 実体 |
|---|---|
| 4.1 | mathlib `commutative_of_cyclic_center_quotient` |
| 4.2 / 4.3 / 4.16 | `S04_CommutatorCollection.lean` / `S04f_Blackburn*.lean` / `S04f_Omega1.lean` |
| 4.4 | (a) `GroupTheory/SCN.lean` / (b) `S04_Prop44b.lean` |
| 4.5 / 4.6 | `S04_Lem45c_Prop46.lean` / `S04_SmallRankBasic.lean` |
| 4.7 | `S04d_GorThm415.lean` / `S04f_AutOrderConstraints.lean` |
| 4.8 / 4.9 / 4.17 | `S04_PGroupsSmallRank.lean` |
| 4.10 / 4.12 | `S04_SmallRankBasic.lean` / `S04b_Thm412.lean` |
| 4.11 | `S04c_Prop411.lean` |
| 4.13 / 4.14 | `S04e_GorThm37.lean` / `S04f_AutOrderConstraints.lean` |
| 4.15 | `S04_ExtraspecialCommutator.lean` |
| 4.18 / 4.19 / 4.20 | `S04g_Thm418*.lean` / `S04g_Cor419.lean` |

### 条項照合 (文書順)

* **4.1** ✅ mathlib 被覆。書籍も **G** Thm 1.3.4 引用のみ。
* **4.2** ✅ 一致。(a) は左右両スロット
  (`commutatorElement_pow_left_of_central` / `_right_of_central`)、
  (b) は `mul_pow_eq_mul_commutator_pow_of_central`
  (`(x*y)^n = x^n y^n ⁅y,x⁆^(n.choose 2)` — 書籍の二項係数の形そのまま)。
* **4.3** ✅ **(a)(b) とも完全形式化済** (`S04_CommutatorCollection.lean`):
  `omega1_pow_eq_one` (a) / `pow_mul_eq_mul_pow_of_commutator_le_omega1` (b)。
  どちらも仮説が書籍どおりの選言 `cl(R) ≤ 2 ∨ (p > 3 ∧ cl(R) ≤ 3)`。
  🚨 **stale 注記 1 件を訂正** — 同ファイルの §4A 節 docstring が
  「`cl ≤ 3` の collection bookkeeping と `|R|`-induction は **remain to be assembled**」
  と書き、存在しない名前 `Omega.pow_eq_one_of_class_le_three` を挙げていた。
  実体は同じファイルの下方に両方揃っている。**BG での stale 注記は通算 8 件目**
  (§1 が 2、§2 が 4、§3 が 1、§4 が 1)。
* **4.4** ✅ (a) `GroupTheory/SCN.lean` の `isSCN_iff_isMaximalAbelianNormal`
  (両方向: `IsSCN.isMaximalAbelianNormal` / `IsMaximalAbelianNormal.isSCN`)、
  (b) `S04_Prop44b.lean`。
* **4.5** ✅ (a)(b)(c) 全条項。
  (a) 無条件形 = `S04_SmallRankBasic.exists_normal_isElementaryAbelian_card_prime_sq_of_not_isCyclic`、
  (b) `isElementaryAbelian_omega1_of_isCyclic_index_prime` (書籍どおり抽象巡回部分群 `H` を取る形)、
  (c) `omega1UpperCentralTwo_not_isCyclic_and_card_prime_sq_le_of_not_isCyclic` (書籍より強く order 下界付き)。
  🚨 **stale 注記 2 件を訂正** (下記)。
* **4.6** ✅ `exists_normal_isElementaryAbelian_card_prime_sq_le_of_normal_not_isCyclic`。
* **4.7** ✅ 両方向 (`scn3_empty_of_pRank_le_two` / `pRank_le_two_of_scn3_empty`)。
* **4.8** ✅ (a) `card_le_prime_cube_of_pRank_le_two_of_exponent_prime` /
  (b) `omega1_pow_eq_one_of_pRank_le_two_of_three_lt`。
* **4.9** ✅ `card_omega1_quotient_le_prime_sq`。
* **4.10** ✅ `isElementaryAbelian_omega1_of_isMetacyclic`。
* **4.11** ✅ `isMetacyclic_of_omega1_card_le_prime_sq`。
* **4.12** 🔴 **部分被覆 2 件だった** → 解消 (下記)。
* **4.13** ✅ `dvd_prime_sq_sub_one_and_lt_of_prime_dvd_aut_of_scn3_empty` (`q ∣ p²−1 ∧ q < p`)。
* **4.14** ✅ `dvd_half_prime_add_or_sub_of_prime_dvd_aut_of_scn3_empty`。
* **4.15** ✅ `mul_centralizer_eq_top_of_isExtraspecial`。**書籍より強い** — `p` 奇の仮説を落とし
  `p`-一般 (docstring に明記)。
* **4.16** (Blackburn) ✅ `blackburnRankTwoClassification` — `3 < p ∧ (R 可換 ∨ 中心積の場合)`。
* **4.17** ✅ `isPGroup_commutator_of_mulAut_odd_of_pRank_le_two`。**書籍より強い** — 書籍の
  「`A` は可解」を落としている (§2 エンジンが odd だけで回るため)。
* **4.18** ✅ `solvable_structure_of_pRank_le_two` — **(a)-(e) の 5 条項が 1 statement**。
* **4.19** ✅ `commutator_le_chiefFactorCentralizer_of_rank_le_two_of_le_normal`。
* **4.20** ✅ (a)(b)(c) 全条項。
  (a) `S05.derived_le_fitting_of_rank_fitting_le_two` — 書籍は「`G'` は冪零」だが
  repo は **より強い `G' ≤ F(G)`**、
  (b) `S05.characteristic_le_derived_normal_of_rank_fitting_le_two`、
  (c) `S05.exists_characteristicSylowSeriesPackage_of_rank_fitting_le_two`
  (`CharacteristicSylowSeriesPackage` = 書籍の characteristic Sylow series)。
  ⚠ **3 条項とも S04 でなく S05 に在る** — 節ディレクトリに絞ると全滅する
  (owner chapter 規則、BG での通算 6 回目)。書籍の仮説「`r(G) ≤ 2` **または** `r(F(G)) ≤ 2`」は
  `r(F(G)) ≤ 2` 側が一般 (`F(G) ≤ G` ゆえ) なので repo の単一仮説で両方を被覆。

### 🔴 実収穫 1: Thm 4.12 の (a) 一般形と (b) の積分解が無かった (部分被覆 2 件)

| 書籍の条項 | repo にあったもの | 判定 |
|---|---|---|
| **(a)** `[R,A]` は可換 | `isMulCommutative_of_metacyclic_actionCommutator_eq_top` = **`[R,A] = R` の場合のみ** (結論も `R` 可換) | 🔴 特殊形のみ |
| **(b)** `R = [R,A]·C_R(A)` **かつ** `[R,A] ∩ C_R(A) = 1` | `actionCommutator_inf_fixedPoints_eq_bot` = **交わりのみ** | 🔴 積分解が欠落 |
| **(c)** | `actionCommutator_isCyclic_and_fixedPoints_isCyclic_and_commutator_le` | ✅ (しかも書籍より一般) |

⚠ **どちらも証明の内部には既に在った** — (a) の一般形は `actionCommutator_inf_fixedPoints_eq_bot`
の証明が冒頭 8 行で作っており (「Part (a) applied to `T` ⇒ `T` abelian」)、積分解は (c) の証明が
Prop 1.6(a) (`fixedPoints_sup_actionCommutator_eq_top`) で引いている。
**endpoint に出ていないだけ**だった。⟹ **「証明の中にある」は被覆でない**。

解消 (2026-08-08、`S04b_Thm412.lean`):

* `isMulCommutative_actionCommutator` — 書籍どおりの (a) (`[R,A]` が可換、側条件なし)。
  既存の特殊形を `T = [R,A]` に適用するだけ (`[T,A] = T` は Prop 1.6(b))。
* `bgThm412` — **書籍パッケージ (a)+(b)+(c)**。(c) は書籍の「`R` が非可換」から
  `T ≠ ⊤` を (a) 経由で導き (`T = ⊤` なら (a) が `R` を可換にする)、
  `C ≠ ⊥` を `R = T ⊔ C` と `T ≠ ⊤` から導いて、書籍の
  「`[R,A]` と `C_R(A)` は**非単位**巡回群」を完全に返す。

⚠ 既存の (c) endpoint は `T ≠ ⊥ ∧ T ≠ ⊤` でパラメータ化されており **書籍より一般**
(`R` 可換でも使える)。`bgThm412` はそれを書籍の仮説に特殊化したもので、置換ではない。

### 🚨 実収穫 2: Lem 4.5(a) の stale 注記 2 件 (同一ファイル内矛盾)

`S04_SmallRankBasic.lean` は **同じファイルの中で** 4.5(a) について 3 通りのことを言っていた:

| 行 | 記載 | 実体 |
|---|---|---|
| :142 | 「**BG Lemma 4.5(a)** (existence half, **normality deferred**)」 | 正規性なし版 (これ自体は正しい) |
| :~181 | 「これが repo が clean に証明できる 4.5(a) の場合。一般 (巡回中心, 例えば extraspecial) の場合は Gorenstein 5.4.10 で **deferred**」 | ❌ 誤り |
| **:921** | 「**BG Lemma 4.5(a)** (= Gorenstein 5.4.10, odd-`p` case). …**unconditional form**」 | ✅ **無条件形が同じファイルに在る** |

⟹ §1 の Thm 1.8 と**同型** (同一ファイル内で注記どうしが矛盾)。両方の注記に
「無条件形は本ファイル後方」と明記して訂正。**BG での stale 注記は通算 10 件目**
(§1: 2 / §2: 4 / §3: 1 / §4: 3)。

## §5 (Narrow p-Groups、7 件 = 5.1-5.7) — 監査完了 (2026-08-08)

全 7 件被覆・**未形式化ゼロ**。実体は `S05_NarrowSCN` / `S05_NarrowCharacterization` /
`S05_NarrowAutomorphisms` / `S05_NarrowPGroups` の 4 file。

| BG | repo の endpoint | 照合 |
|---|---|---|
| **5.1** | (a) `scn3_nonempty_of_three_le_pRank` / (b) `mem_scn3_of_normal_isElementaryAbelian_card_prime_sq` | ✅ |
| **5.2** | `lemma52` — **(a)(b)(c) が 1 statement** | ✅ |
| **5.3** | 同値 = `narrow_iff_exists_maximalElementaryAbelian_card_prime_sq` / (d) = `narrow_centralizer_decomp` / (a)(b)(c) = `lemma52` 経由 | 🔴 **packaging 差** → `bgThm53` 新設 |
| **5.4** | `narrow_iff_exists_card_prime_centralizer_pRank_le_two` | ✅ |
| **5.5** | `solvableAut_of_narrow` — **(a)(b)(c) が 1 statement** | ✅ |
| **5.6** | `narrow_sylow_solvable_structure` — **(a)-(e) が 1 statement** | ✅ |
| **5.7** | `derived_le_fitting_of_centralizer_rank_le_two` | ✅ |

### 🔴 実収穫: Thm 5.3 の packaging 差

書籍の 5.3 は「**同値 + narrow のときの (a)(b)(c)(d)**」という 1 つの結果だが、repo では

* 同値と (d) は endpoint に在る、
* しかし **(a)(b)(c) は `lemma52` (= Lem 5.2) 経由でしか取れず、`lemma52` は
  `E ∈ ℰ²(R) ∩ ℰ*(R)` を明示引数に要求する** — 「`R` が narrow」からその `E` を作る一手
  (`narrow_iff_…` の `.1`) が endpoint に無かった。

⚠ 書籍自身が「By Lemma 5.2, we obtain (a), (b), and (c)」と書いており、repo もその通りに
実装されている。**欠けていたのは数学でなく「narrow ⟹ E 存在」を挟んだ書籍の形**。

⟹ `bgThm53` (`S05_NarrowCharacterization.lean`) を新設。あわせて

* **(a) を全称形にした** — 書籍は「**no element** of `ℰ²(R) ∩ ℰ*(R)` is contained in `T`」。
  `lemma52` は渡した `E` についてしか言わないが、その `E` は `ℰ²∩ℰ*` を走るので
  全称形が無償で出る (narrow すら不要)。
* **(c) の characteristic 半分を明示** — `lemma52` は index しか返しておらず、
  characteristic は `GroupTheory/NarrowPGroup.lean` の instance
  `centralizer_omega1UpperCentralTwo_characteristic` に在った (別 file)。
  書籍の (c) は「characteristic subgroup of index `p`」なので両方要る。

### 🚨 stale 注記 1 件 (§4 の余波)

`S05_NarrowSCN.lean` の `omega1UpperCentralTwo_not_isCyclic_of_three_le_pRank` docstring が
「**still-deferred** general Lemma 4.5(a) を避けるため」と書いていた。4.5(a) は無条件形が
`S04_SmallRankBasic.lean:921` に在る (§4 監査で確定)。⟹ 「4.5(a) は在るが、この経路は
位数 `p³` を直接くれるので残す」と訂正。**BG での stale 注記は通算 11 件目**。

## §6 (Additional Results、7 件 = 6.1-6.7) — 監査完了 (2026-08-08)

全 7 件被覆・**未形式化ゼロ**・**stale 注記ゼロ** (BG で初)。

| BG | repo の endpoint | 照合 |
|---|---|---|
| **6.1** (Hall–Higman) | `AppA.thmA4b` + §6 側 (issue 3025、`p ≠ 2` の空虚な仮説を落とした版) | ✅ BG 自身が 6.1 = Thm A.4(b) と同定 |
| **6.2** | `AppB.zCenter_lOdd_sup_oPiCore_normal` (Puig `L(S)` 版 = 書籍 Thm B.4) **かつ** `S06.zCenterThompsonJAbelian_sup_oPiCore_normal` (**literal `J(S)`**) | ✅ 両方 |
| **6.3** | (a) 2 条項 / (b) `lemma63b` | 🔴 (a) が非対称 → `lemma63a` 新設 |
| **6.4** | `exists_centralizing_conj_sup_isPiGroup_of_normalHall` | ✅ |
| **6.5** | (a) `inf_commutator_eq_of_coprime` / (b) `normalizer_eq_centralizerK_mul_normalizerU` / (c) `exists_mem_centralizerK_mul_of_conj_le` | ✅ 3 条項 |
| **6.6** | (a) `oPiPrimePiCore_eq_oPiPrimeCore_sup_sylow` + `top_eq_oPiPrimeCore_sup_normalizer_sylow` / (b) `sylow_le_commutator_normalizer_of_le_commutator` / (c) `exists_mem_centralizer_mul_normalizer_of_conj_subset_sylow` / (d) `exists_mem_centralizer_inf_conj_le_sylow` | ✅ 4 条項 |
| **6.7** | `le_oPiPrimeCore_of_normalized_by_maximalElementaryAbelian` | ✅ |

### ✅ Thm 6.2 は書籍の両版を持っている (誤判定しかけた)

書籍 6.2 は **Thompson の `J(S)`** で `Z(J(S))·O_{p'}(G) ⊴ G` と述べ、証明は **G** に投げる。
直後の Remark が「**代替** (Thm B.4) を Appendix B で Puig の `L(S)` を使って証明する」と書く。

⚠ AxiomsCheck の登録コメントは `L(S)` 版を「**BG Thm 6.2 一般形**」と呼んでおり、
それだけ見ると「literal `J(S)` 版は無い = 書籍の 6.2 は未被覆」と読める。実際には
`S06_Thm62JS.lean` が **2026-07-21 に literal `J(S)` 版を無条件で完成**させている
(Gorenstein 版 abelian Thompson subgroup + `GroupTheory/GlaubermanZJ.lean` の Glauberman
`Z(J)`-定理本体 + 商の p-stability + p-constraint)。⟹ **両版とも在る**。

### 🔴 実収穫: Lem 6.3(a) の 2 条項が非対称だった

書籍 6.3(a) は「`H = [H,K]` **かつ** `C_H(K) ⊆ H'`」で 1 つの主張。repo は 2 定理に分かれており、
**同じ節の (b) は `lemma63b` として束ねられている**という非対称があった。
⟹ `lemma63a` を新設 (`S06_ConjugationBridges.lean`)。

⚠ 第 1 条項 `commutator_eq_self_of_isComplement'_le_commutator` は**書籍より強い** —
有限性も coprimality (= Hall) も要らない。`lemma63a` の docstring にその旨を明記し、
Hall が無い場面では直接 cite するよう案内した (束ねたことで一般形が隠れないようにする)。

### 📌 6.7 の Remark は「低優先繰延」であって特殊化債務でない

BG 6.7 の直後の Remark は「`p`-length one の仮定は Thompson の定理 [18, Thm X.1.12] により不要」
と書く。⚠ **§3 の Lem 3.2 / Thm 3.5 と同じ形だが結論は逆** — §3 の Note が挙げた Thompson
(Frobenius kernel nilpotency) は repo に在ったので仮説を落とせたが、**6.7 の Thompson は
[18] = Huppert–Blackwell 系の外部文献**で 3 冊スコープ外。BG 自身も証明を書いていない。
⟹ repo が `hasPLengthOne` を保持しているのは**書籍の証明どおり**で正しい
([[feedback-generalize-specialized-fully]] の「文献引用のみは低優先繰延」に該当)。

## §7 (The Transitivity Theorem、6 件 = 7.1-7.6) — 監査完了 (2026-08-08)

全 6 件被覆・**未形式化ゼロ・packaging 差ゼロ・stale 注記ゼロ** (BG で初の「補充ゼロ」節)。

| BG | repo の endpoint | 照合 |
|---|---|---|
| **Lem 7.1** (Inductive Lemma) | `S07.inductiveLemma` 系 (AxiomsCheck:3347) | ✅ |
| **Thm 7.2** (`m(Z(A)) ≥ 3`) | AxiomsCheck:3360 | ✅ |
| **Thm 7.3** (`m(Z(A)) ≥ 2` + `q ∈ π(C_G(A))`) | AxiomsCheck:3354 | ✅ |
| **Thm 7.4** (Propagation) | `S07.transitivity_propagates` — **(a)(b)(c)(d) が 1 statement** | ✅ |
| **Prop 7.5** | `S07.hypothesis71_of_scn2_or_pLengthOne` — **両分岐 (1)(2) が 1 statement** | ✅ |
| **Thm 7.6** (Thompson Transitivity) | `S07.thompsonTransitivity` | ✅ |

### ⚠ Hypothesis 7.1(2) の式は pdftotext が丸ごと落としていた

`Hypothesis 7.1` の (2) は pdftotext で

> (2) Whenever `X` is a proper subgroup of `G` that contains `A`, we have

と**結論の式のところで切れている** (Lem 3.1(b) と同じ型)。ページ画像
`references/bg/pages/bg-p056.png` (PDF = 書籍 + 13 = p.69) で確定:

> **(2)** Whenever `X` is a proper subgroup of `G` that contains `A`, we have
> `⟨ℋ_X(A;π')⟩ = O_{π'}(X)`.

⟹ repo の `Hypothesis71.generated_eq`
(`sSup (hInvariant X A (primesOf A)ᶜ) = opiCoreInG (primesOf A)ᶜ X`) と**完全一致**。
同ページで Lem 7.1 の statement も確認 (`A ⊆ H`, `H ∩ Q₁ ≠ 1`, `H ∩ Q₂ ≠ 1` ⟹ `Q₂ = Q₁^k`)。
⟹ **BG では「条項/式が OCR で消える」が 2 例目**。番号付き結果だけでなく
**Hypothesis の定義文**も同じ危険がある。

### 📌 Ch.II の standing hypothesis は `IsMinimalSimpleOdd`

書籍 p.55 (L3267-3269): 「We now assume that the main theorem is false. Henceforth in these
notes we let `G` denote a fixed **counterexample of minimal order**. Of course `G` is a
nonabelian simple group.」⟹ repo の `IsMinimalSimpleOdd G` を §7 以降の全 statement が
仮説に持つのは書籍どおり (§1-§6 が `G` 一般なのと対照的)。

### 📌 7.4(d) の積表示

書籍の (d) 後半は `N_G(P) = O_{π'}(C_G(P))·(N_G(P) ∩ N_G(Q))` (集合積)。repo は
`∀ n ∈ N_G(P), ∃ c ∈ O_{π'}(C_G(P)), ∃ m ∈ N_G(P) ⊓ N_G(Q), n = c*m` (⊆ 方向のみ) と
書いているが、`C_G(P) ≤ N_G(P)` ゆえ ⊇ は自明で**同値**。

## §8 (The Fitting Subgroup of a Maximal Subgroup、1 件 = 8.1) — 監査完了 (2026-08-08)

書籍 §8 の番号付き結果は **Thm 8.1 の 1 件のみ** (2 条項)。両方とも AxiomsCheck 登録済:

* (a) `S08.cFitting_isUniquelyMaximal_of_not_pGroup` — `F(M)` が `p`-群でなければ
  `C_{F(M)}(A₀) ∈ 𝒰`
* (b) `S08.sylow_isSylow_and_scn3_isUniquelyMaximal_of_pGroup` — `F(M)` が `p`-群なら
  `M` の Sylow `p` は `G` の Sylow、かつ `SCN₃(P)` の各元は `F(M)` に含まれ `𝒰` に属す

⟹ **補充ゼロ**。(§8 の分量が大きいのは、1 定理の証明が長いため。)

## §9 (The Uniqueness Theorem、6 件 = 9.1-9.6) — 監査完了 (2026-08-08)

全 6 件被覆・**未形式化ゼロ・packaging 差ゼロ・stale 注記ゼロ**。

| BG | repo の endpoint | 照合 |
|---|---|---|
| **Thm 9.1** | `S09.noncyclic_isUniquelyMaximal_of_centralizer_le` | ✅ **書籍の (a)/(b) を選言で保持** |
| **Cor 9.2** | `S09.isUniquelyMaximal_of_le_centralizer_of_two_le_rank` | ✅ |
| **Cor 9.3** | `S09.isUniquelyMaximal_of_abelian_rank_three` | ✅ |
| **Lem 9.4** | `S09.abelian_rank_three_isUniquelyMaximal_of_fitting` | ✅ |
| **Lem 9.5** | `S09.scn3_isUniquelyMaximal` | ✅ |
| **Thm 9.6** (Uniqueness) | `S09.uniquenessTheorem` + **"In particular" 条項** `S09.isUniquelyMaximal_of_mem_e2_not_maximal` | ✅ |

### 🔴 実収穫: §9 が AxiomsCheck に 1 件も登録されていなかった

数学は全部在ったが、**書籍番号 ↔ 実体の索引 (AxiomsCheck) に §9 の entry がゼロ**だった。
CLAUDE.md は AxiomsCheck を「**書籍番号 ↔ Lean 実体の最良の索引**」と位置づけ、本監査の
走査手順もその第 1 手に置いている (§2 の Lem 2.7 誤判定の再発防止策)。**Uniqueness Theorem
という BG 第 II 章の主結果が索引に無い**のは、後続の監査・再開セッションを誤判定させる。

⟹ 7 件 (9.1-9.6 + 9.6 の "In particular") を登録。axiom-clean も同時に検証される。

⚠ **「AxiomsCheck に無い ⟹ 未形式化」ではない** (§9 がその反例)。逆に
**「実体が在る ⟹ 索引にも在る」も成り立たない**。索引の欠落は**索引の欠陥**として直す。

### ✅ Thm 9.6 の "In particular" は取りこぼされていなかった

前 2 冊の監査で「**"In particular" 欠落**」は誤判定様式の 1 つだった (memory
[[textbook-coverage-audit-failure-modes]])。9.6 の「In particular, if `A ∈ ℰ²(G) − ℰ*(G)`,
then `A ∈ 𝒰`」は `isUniquelyMaximal_of_mem_e2_not_maximal` として独立の public theorem に
なっており、private helper `three_le_rank_centralizer_of_mem_e2_not_maximal` が
「`ℰ²` かつ非極大 ⟹ `r(C_G(A)) ≥ 3`」を供給している。

## §10 (The Subgroups M_α and M_σ、14 件 = 10.1-10.14) — 監査完了 (2026-08-08)

全 14 件被覆・**未形式化ゼロ**。実収穫 = **packaging 差 2 件** (Thm 10.2 / Prop 10.11)。

| BG | 条項数 | repo | 照合 |
|---|---|---|---|
| **10.1** | (a)-(e) | `fusion_control_of_mem_sigma` | ✅ **5 条項が 1 statement** |
| **10.2** | (a)-(e) | `isHall_Msigma_Malpha` | 🔴 **(d) 欠落** → `bgThm102` |
| **10.3** | 1 | `centralizer_isUniquelyMaximal_of_two_le_rank` | ✅ `α(M)'` 正しい |
| **10.4** | (a)(b)(c) | `alpha_criterion` (a)(c) + `exists_mem_omega1_center_zgroupCentralizer` (b) | ✅ |
| **10.5** | 1 (3 結論) | `pRank_eq_two_of_normalizer_le` | ✅ |
| **10.6** | 1 | `proper_hasPLengthOne` | ✅ |
| **10.7** | (a)-(e) | `sylow_structure` | ✅ **5 条項が 1 statement** |
| **10.8** | (a)(b)(c) | `isHall_Mbeta` | ✅ 3 条項 |
| **10.9** | (a)(1)(2)(3) + (b) | `beta_complement_centralizes` / `beta_complement_normalizer_derived_contains_sylow` / `beta_factorization_of_sylow_normalizer_in_intersection` | ✅ **分離が正しい** (下記) |
| **10.10** | (a)(b)(c) | `normalizer_factorization` | ✅ 3 条項 |
| **10.11** | (a)(b)(c)(d) | (a)(b)(c) 束 + (d) 別 | 🔴 → `bgProp1011` |
| **10.12** | (a)(b) | `disjoint_of_not_conj` | ✅ 2 条項 |
| **10.13** | (a)(b)(c) | `nonabelian_pSubgroup_rankTwo_elemAbelian_structure` | ✅ 3 条項 |
| **10.14** | (a)(b)(c)(d) | (a)(b)(c) 束 + (d) 別 | ✅ **分離が正しい** (下記) |

### 🔴 実収穫 1: Thm 10.2 の (d) が束から落ちていた

`isHall_Msigma_Malpha` は (a)(b)(c)(e) を持つが **(d)** (`r(M/M_α) ≤ 2` かつ `M'/M_α` nilpotent)
を欠いていた。docstring は「quotient 型の `Normal` instance 整備後に**追加予定**」と書いていたが
**stale** — (d) 自体は `rank_quotient_Malpha_le_two_of_isHall` /
`derived_quotient_Malpha_le_fitting` として既に形式化されていた。

⟹ `bgThm102` (5 条項を書籍の順で)。(a)(b) の「`M` の Hall でもある」半分も
`Ch03.isHallSubgroup_subgroupOf_of_le` から補った。`M'/M_α` の冪零性は
`(M/M_α)' ≤ F(M/M_α)` から (`Ch03.isNilpotent_of_le`)。そのため
`HallNilpotent` / `NilpotentInjector.PiParts` の import を追加 (フルビルドで cascade 無し確認)。
⚠ 行数増で `AxiomsCheck.lean` の longFile stamp を 20700 → 20800 に更新。

### 🔴 実収穫 2: Prop 10.11 の (d) が束から分離していた

(a)(b)(c) は `sigma_complement_rank_le_one` に束ねられ、(d) は
`sigma_complement_commutator_cyclic_normal` に別置き。**(d) の仮説は (a)(b)(c) の仮説への
追加**なので、書籍どおり含意として束ねられる ⟹ `bgProp1011`。

### 📌 束ねない判断 — 10.9 と 10.14

**条項ごとに仮説が別物のときは束ねない**という線を引いた:

* **10.9**: (a) は「`p,q ∈ β(M)'` distinct, `X` が `M` の `q`-部分群, `X ⊆ M'` または `p<q`」、
  (b) は「`H ∈ ℳ − {M}` と `N_G(S) ⊆ H ⊓ M`」。**共有仮説は `M ∈ ℳ` だけ**。
* **10.14**: (a)(b)(c) は「`p ∈ β(G)`, `P ∈ Syl_p(G)`」だが、**(d) は `M ∈ ℳ` を使う** —
  書籍の (d) は Prop 10.14 の仮説に登場しない `M` を参照しており、書籍側が緩い書き方をしている。

⟹ 束ねると人工的な statement になるので分離のまま。**判断基準**:
**条項が statement の仮説を共有する (追加の側条件は可) なら束ねる。書籍が番号だけを共有する
別々の主張を並べているなら束ねない。**

## §11 (Exceptional Maximal Subgroups、7 件 = 11.1-11.7) — 監査完了 (2026-08-08)

全 7 件被覆・**未形式化ゼロ・stale 注記ゼロ**。実収穫 = **packaging 差 1 件** (Cor 11.6)。

| BG | repo の endpoint | 照合 |
|---|---|---|
| **Lem 11.1** | `invariant_sylow_disjoint` | ✅ (a)(b) |
| **Cor 11.2** | `Msigma_meet_conjugate` | ✅ (a)(b) |
| **Thm 11.3** | `Msigma_isNilpotent` | ✅ |
| **Cor 11.4** | `eq_of_Msigma_meet_Hsigma` | ✅ |
| **Thm 11.5** | `sylow_p_isCommutative` | ✅ |
| **Cor 11.6** | (a)(b) `omega1_eq_and_centralizer_trivial` + (c) `exists_distinct_conj_lines` | 🔴 → `bgCor116` |
| **Thm 11.7** | `MsigmaA_normal` | ✅ |

### 📌 §11 は standing hypothesis を structure 化してある

書籍 §11 は冒頭に **Hypothesis 11.1** (`M ∈ ℳ`, `p ∈ σ(M)'`, `A₀ ∈ ℰ_p¹(M)`, `N_G(A₀) ⊆ M`、
そこから導かれる `r_p(M)=2` / `A₀ ⊆ A ∈ ℰ_p²(M)` / `A ⊆ P ∈ Syl_p(M)` / `N_G(P) ⊄ M` /
`C_G(A) ⊆ M`) を置き、7 結果すべてがそれを仮定する。repo は `Hypothesis111 M p A₀ A P` という
**structure** にしてあり、全 endpoint が `(h : Hypothesis111 …)` を取る。⟹ §7 の
`Hypothesis71` と同じ設計で、書籍の節構造がそのまま Lean に写っている。

### 🔴 実収穫: Cor 11.6 の (c) が別置きだった

(a)(b) と (c) は **Hypothesis 11.1 以外に仮説を持たない** (完全に共有) ので、
§10 で確立した基準では束ねるべき。⟹ `bgCor116` (3 条項)。
(a)(b) の docstring は「(原典 (c): … — **後続**。)」と書いており、(c) が同じファイルに
実装された後も更新されていなかった (軽度の stale) ので訂正した。

## §12 (The Subgroup E、19 件 = 12.1-12.19、BG 最大の節) — 監査完了 (2026-08-08)

全 19 件被覆・**未形式化ゼロ・packaging 差ゼロ・特殊化債務ゼロ**。
実収穫 = **stale 注記 2 件** (どちらも `S12_E.lean` のファイルヘッダ)。

**多条項がすべて既に 1 statement に揃っていた** — §12 は BG 最大の節だが最も整っている:

| BG | 条項数 | repo の endpoint |
|---|---|---|
| **Lem 12.1** | **(a)-(g) の 7 条項** | `S12_ECore.subgroupE_basic` |
| **Thm 12.5** | **(a)-(f) の 6 条項** | `S12_Theorem125.Msigma_nilpotent_of_tau2` |
| **Cor 12.10** | (a)-(d) | `S12_Corollary1210.nilpotent_sigmaComplement_abelian` |
| **Thm 12.12** | (a)(b) | `S12_Theorem1212c.frobenius_factorization_of_regular` (`FrobFactConclusion`) |
| **Cor 12.16** | (a)(b) | `sigma_subgroup_pRank_normalizer_le_one` / `sigma_subgroup_not_mem_primeFactors_derived_of_tau1` |

`grep sorry` (コメント除去後) で §12 の全 21 file が **実 sorry ゼロ**。

### 🚨 実収穫: `S12_E.lean` ヘッダの「deferred」注記 2 件が stale

| 注記 | 実体 |
|---|---|
| 「Theorem 12.12 … 内部の cyclic `Z_p` 構成は **remains deferred**」 | ✅ `frobenius_factorization_of_regular` が 3 ケースすべてを処理済。abelian-Sylow ケースの `Z_p` 構成は `exists_regular_cyclic_of_mem_tau2` / `exists_tau2_product` |
| 「**Corollary 12.16(b) remains a deferred proof obligation**」 | ✅ `not_mem_primeFactors_derived_of_tau1` (docstring に「**実証明版**」)、さらに一般 `σ(M)`-部分群形 `sigma_subgroup_not_mem_primeFactors_derived_of_tau1` も在る |

⟹ **BG での stale 注記は通算 13 件目 / 14 件目**。⚠ この 2 件は**ファイルヘッダの
「Lane proof-gate notes」**という、後続セッションが真っ先に読む場所に在った。

### ✅ 「`q`-群特殊化」は債務でなかった

`pRank_normalizer_le_one` の docstring は自身を「**`q`-group specialization**」と明示するが、
**一般形が同じファイルに在る** (`sigma_subgroup_pRank_normalizer_le_one`; 特性部分群
`O_q(Y)` 経由で還元、`N_G(Y) ≤ N_G(O_q(Y))`)。⟹ 内部エンジンの特殊化であって
書籍に対する特殊化債務ではない。**「specialization」という語を見たら一般形の有無を確認する**。

## §13 (Prime Action、13 件 = 13.1-13.13) — 監査完了 (2026-08-08)

全 13 件被覆・**未形式化ゼロ・packaging 差ゼロ・stale 注記ゼロ**。全 8 file が実 sorry ゼロ。

多条項がすべて 1 statement に揃っている: **13.1** (a)(b)(c) / **13.2** (a)(b)(c) /
**13.3** (a)(b) / **13.10** (a)(b)(c) / **13.11** (a)(b)(c)(d)。

📌 **13.10 と 13.11 の docstring は「結論は PDF p.102/p.103 から画像読みで復元」と明記**
— OCR が結論を落とす箇所で既にページ画像を使う運用がされていた (本監査が §3/§7/§10 で
独立に到達した手順と同じ)。

## 🚨 §13 で実施した「deferral 注記の一括走査」— 2 件の見落としを回収

`grep -rn "追加予定|stub 未配置|remains deferred|deferred proof obligation|TODO|Phase 1 待ち" OddOrder/BG/`
を全 BG に対して実行し、**節ごとの監査で取りこぼした stale 注記を 2 件回収**した。

### 🔴 回収 1: Lem 10.8(c) の「最大素因子」条項 (§10 の見落とし)

`isHall_Mbeta` の docstring:
> (原典 (c) はさらに「`p` は `|M/O_{p'}(M)|` の最大素因子」を含む — **quotient 型整備後に追加予定**。)

**Thm 10.2(d) と完全に同型**の見落とし (同じ「quotient 型整備後」という言い訳まで同じ)。
条項自体は**直下の** `largestPrime_quotient_oPiCore_compl_of_not_mem_beta` で証明済。
⟹ `bgLem108` (a)(b)(c) 完全形を新設。
⚠ **§10 の監査で `isHall_Mbeta` の結論の型 (4 連言) だけを見て ✅ と判定したのが誤り** —
書籍の (c) が 2 つの主張からなることを見落としていた。**条項の内訳まで書籍と突き合わせる**。

### 🔴 回収 2: `S02_RepresentationPropositions.lean` の「stub 未配置」4 件 (§2 の見落とし)

§2 監査は `S02_RepresentationsBasic.lean` の注記を訂正したが、**同じ節の別ファイル**
`S02_RepresentationPropositions.lean` に同種の注記が 4 件残っていた (Prop 2.1 / Lem 2.3 /
Prop 2.4 / Thm 2.5)。実体はすべて在る。

### 🚨🚨 最重要: 「`^theorem ` grep が docstring 内のコードフェンスに当たる」

§2 census は **Prop 2.1 の実体を `S02_RepresentationPropositions.lean:84` の
`absolutely_irreducible_iff_hom_eq_F`** と記録していたが、その行は

```
**Lean signature 案** (未確定):
```                                    ← markdown コードフェンス
theorem absolutely_irreducible_iff_hom_eq_F      ← 列 0 から始まる
```

という **docstring 内の未実装の草案**だった。`grep -n "^theorem "` は列 0 の行に当たるので
**docstring の中身を宣言と誤認する**。

⟹ **新しい誤判定様式**: 「宣言を `^theorem ` で拾う」走査は docstring 内のコードブロックに
汚染される。**実体確認は `grep -rn "<name>" --include=*.lean` で全 hit を見て、
その行が本当に宣言かを確認する** (hit が 1 件でその 1 件が docstring 内なら未実装)。

✅ 実際の Prop 2.1 は 3 条項とも `GroupTheory/RepresentationTheory/AbsolutelyIrreducible.lean` に:
(a) `isAbsolutelyIrreducible_iff_bijective_algebraMap` /
(b) `span_range_representation_eq_top_of_algebraMap_intertwiningMap_surjective`
(= `Hom_F(M,M) = E(G)`) / (c) `isAbsolutelyIrreducible_overEnd`。
⟹ **未形式化ではない**が、census の所在記録が誤っていた。

## §14 (Maximal Subgroups of Type 𝒫 and Counting、13 件 = 14.1-14.13) — 監査完了 (2026-08-08)

13 件すべてに endpoint あり。**しかし BG 監査で初めて「真の未形式化」を確認**した節。

| BG | repo | 照合 |
|---|---|---|
| **Prop 14.2** ((a)-(g)) | `typeP_structure` + 個別条項 5 本 | 🔴 **(a) 後半と (g) の一部が未形式化** → [issue 0178](../../issues/0178-bg-prop142-regular-u-and-nilpotent-msigma.md) |
| **Thm 14.7** ((a)-(h)) | `typeP_duality` が (b)-(h) を `∃!` で束ね、(a) は `typeP_partner_centralizer_singleton` | ✅ 全条項あり (軽微な分離) |
| **Lem 14.5** ((a)(b)(c)) | `xRsub_disjoint` / `Mtilde_disjoint` / `sigmaSaturation_Rsub_count` | ✅ |
| **Cor 14.9** ((a)(b)) | `exists_mem_conjClassSet_Mtilde_or_zTilde_of_ne_one` ほか | ✅ |
| 14.1 / 14.3 / 14.4 / 14.6 / 14.8 / 14.10 / **14.11** / 14.12 / 14.13 | すべて endpoint あり | ✅ |

### 🔴🔴 BG 監査で唯一の「真の未形式化」— Prop 14.2 の 2 件

§1-§13 (127 件) で見つかった問題は**すべて packaging 差か stale 注記**で、実体は必ず在った。
Prop 14.2 は違う: **書籍の主張が repo のどこにも無い**。

1. **(a) 後半** — 「`K` は `M` のある abelian Hall `(κ(M) ∪ σ(M))'`-部分群 `U` に
   **regular に作用**し、`U M_σ` は `M` における `K` の normal complement」。
   ⚠ `typeP_structure` は `U` の Hall 性を**仮説 `_hU` で受け取り、使っていない**
   (アンダースコア付き)。
2. **(g) 第 3 主張** — 「`M ∈ 𝓜_{𝒫₂}` なら … `M_σ` は **nilpotent** な TI-部分群」。
   `σ = β` / `|K|` prime / TI は在るが**冪零性だけ無い**。
   ⚠ **下流 `AppE_CorollaryE5` / `AppE_E5Counting` はこれを仮説 `hMσnil` として取っている** —
   CLAUDE.md が警告する「hard content を未充足の仮説に hoist」そのもの。
   ⟹ **閉じれば下流の仮説を実証明に置換できる**。

⟹ [issue 0178](../../issues/0178-bg-prop142-regular-u-and-nilpotent-msigma.md) を起票。

### ⚠ この gap は「deferred 注記」に書かれていたが、注記の 8 割は stale だった

`typeP_structure` の docstring は 7 項目を "deferred" と列挙していたが、**そのうち 4 件
((b2)/(d) の第 2 条項/(e)/(f)) は既に別宣言で証明済**だった。⟹ **注記を根拠に「未形式化」と
書かない。概念形の grep で不在を確認してから初めて gap と呼ぶ**。docstring は実態に合わせて訂正。

## §15 (9 件 = 15.1-15.9) / §16 (1 件 = 16.1) — 監査完了 (2026-08-08)

全 10 件被覆・**未形式化ゼロ・packaging 差ゼロ**。条項ラベル付きの endpoint が非常に密:

| BG | 条項 | repo |
|---|---|---|
| **Lem 15.1** | (a)(b)(c)(d)(e) | `isNilpotent_complement_of_isTypeF` / `typeP_hall_derived_eq_and_abelian` / `uniqueMaximal_of_kappaSigmaCompl_element` / `typeP_centralizerGeneratedBySigma_isMulCommutative` / `typeP_hall_frobenius_factorization` |
| **Thm 15.2** | (b)(g) ほか | `Theorem152Assembly` 一式 |
| **Cor 15.3** | (a)(b) | `mf_centralizer_hall_decomp` / `hall_subgroupOf_normal_of_msigma_nilpotent` |
| **Cor 15.4** | — | `eq_top_of_forall_sylow_le` ほか |
| **Cor 15.5** | (a)(b)(c)(d) | `Corollary155` の束 + (c) 後半は §16 (下記) |
| **Cor 15.6** | — | `typeP_kstar_in_mf` |
| **Thm 15.7** | (a)(b)(c)(d)(e) | `S15_MF` の 5 系統 |
| **Thm 15.8** | — | `fittingInAmbient_eq_Msigma_of_isTypeP2_of_tau2_empty` |
| **Cor 15.9** | (b) ほか | `not_fittingIsTI_of_mem_fittingSharp_of_centralizer_not_le` |
| **Prop 16.1** | (a)(b) | `S16.proposition_type_classification` |

### 🚨 実収穫: 「quotient API deferred」の 3 例目も stale

Cor 15.5(c) は「`M_F ⊆ M'` **かつ** `M'/M_F` が nilpotent」の 2 主張。repo は前半だけを束に持ち、
2 箇所 (`Corollary155.lean` のインラインコメント / `AutAbelianCore.lean` の docstring) が
「`M'/M_F` nilpotency は **deferred — quotient API**」と書いていた。

**実体は在る**: `S16_MainResults/TypeBridges.lean` の
`derivedInG_quotient_maxNilpotentNormalHall_isNilpotent` が
`Group.IsNilpotent (↥(derivedInG M) ⧸ (MF M).subgroupOf (derivedInG M))` を証明しており、
同ファイル内の大きな §16 束にも組み込まれている。

⚠ **ただしこれは §15 の束には入れられない** — 証明が **§16 (下流) に在る**ため、
§15 の statement に書くと import cycle になる。§3 の `S03_WithoutSolvableKernel` と同じ構図。
⟹ 注記を「証明済だが層の都合で別位置」に訂正 (bundle はしない)。

📌 **「quotient 型 API 整備後に追加予定」という言い訳は BG で 3 回出て 3 回とも stale だった**
(Thm 10.2(d) / Lem 10.8(c) / Cor 15.5(c))。⟹ **この文言を見たら即座に実体を探す**。

## 補章 A-E — census を訂正 (2026-08-08): **14 件 → 19 件**

当初 census は「`Kind X.N` が 14 件、各補章の `.1` が未発見」としていた。原因は **OCR**:

| 罠 | 実例 | 対処 |
|---|---|---|
| **数字 `1` が大文字 `I` に化ける** | `Theorem A.I.` / `Lemma B.I.` / `Lemma C.I.` / `Lemma D.I.` / `Theorem E.I.` | `[0-9IlL]` を許して正規化 |
| **帰属の括弧が番号の直後に入る** | `Theorem B.4 (L. Puig, 1976).` / `Theorem E.3 (Feit and Thompson, 1991).` | `\.\s` だけでなく `(` も許す (本文節のパターンは既にそうなっていた) |

⟹ 確定: **A:5 / B:4 / C:3 / D:2 / E:5 = 19 件**。

repo 対応 (すべて実体あり): `AppA_PStability*` (`thmA1`/`thmA2`/`thmA3`/`thmA4a,b,c`/`thmA5_*`) /
`AppB_Puig*` + `AppB_Thm62` (B.1-B.4) / `AppC_*` (C.1-C.3) / `AppD_CNGroups/*` (D.1/D.2) /
`AppE_*` (E.1-E.5)。

### ✅ 補章 D は de-opacification の模範例 (2026-07-18、監査より前)

`MinimalSimpleCNHypothesis` が minimal simplicity を **free `Prop` フィールド**として持っていた
ため、`True` で instantiate でき **D.1/D.2 が全 odd CN-群について主張される形**になっていた
(その読みでは両方とも**偽** — D.2 は `C₃`、D.1 は `F_{3⁶} ⋊ (C₇ ⋊ C₃)` が反例)。
既に honest な仮説 (`IsCNGroup` + `IsMinimalSimpleOdd`) に置換され、反例まで docstring に
記録されている。⚠ 「Appendix D を `feitThompson` から空虚に導かない」という注意書きも在る
(CN-定理は FT の**入力**なので依存順序が逆転する)。

## Theorems A-E (章番号なしの主定理 5 件) — 位置と性格を確定

⚠ **issue 0177 の baseline が記録した行番号 (A=L6615 等) は依存関係の図のラベル**だった。
本文は **§16 内** の L6479 (A) / L6509 (B) / L6516 (C) / L6532 (D) / L6554 (E)。

**性格**: Theorems A-E は §10-§15 の結果の**要約 (summary)** で、各条項が既出の番号付き結果の
言い換え。⟹ 被覆は「下敷きの番号付き結果の被覆」に帰着する。

### 🔴 Theorem A の逐条対応 — issue 0178 の gap が主定理条項として再浮上

| Thm A | 書籍の内容 | 下敷き | 状態 |
|---|---|---|---|
| (1) | `M_σ` が `M` の唯一の normal Hall `σ(M)`-部分群、かつ `G` の `σ(M)`-Hall | Thm 10.2(b) | ✅ (`bgThm102`) |
| (2) | `M` は cyclic Hall `κ(M)`-部分群 `K` を持つ | Lem 15.1(b) | ✅ |
| **(3)** | `K M_σ` は `M` 内に **`K`-不変な補群 `U`** を持ち `U M_σ ⊴ M = K U M_σ` | **Prop 14.2(a) 後半** | 🔴 **未形式化** |
| **(4)** | 各 `k ∈ K^#` で **`C_U(k) = 1`** | **Prop 14.2(a) 後半** | 🔴 **未形式化** |
| (5) | `K* = C_{M_σ}(K) ≠ 1`、`K ≠ 1` なら `N_M(⟨k⟩) = K × K*` | Prop 14.2(b)(c) | ✅ |
| (6) | `1 ⊂ M_F ⊂ M_σ ⊂ M' ⊂ M` かつ `M'/M_F` nilpotent | Thm 15.2 + Cor 15.5(c) | ✅ |
| (7) | `M'' ⊆ F(M) = C_M(M_F)M_F`、`K ≠ 1` なら `F(M) ⊆ M'` | Cor 15.5(b)(d) | ✅ |
| (8) | `M_F ≠ M_σ` なら `U = 1`、`F(M)` が TI、`|K|` 素数 | Thm 15.8 | ✅ |

⟹ **[issue 0178](../../issues/0178-bg-prop142-regular-u-and-nilpotent-msigma.md) の gap は
周辺的な条項ではなく、BG の主定理 Theorem A の (3)(4) そのもの**。優先度を上げる根拠になる。

### ⬜ 残り: Theorems B-E の逐条対応

repo は条項ラベル付きで B(1)(3)(4)(5) / C(1)(2)(3)(4)(5)(8)(9) / D(1)(3)(4) / E(2) に言及。
**A と同じ「下敷きの番号付き結果への還元」を B-E でも行うのが残作業** (下敷きは §10-§15 で
既に監査済なので、対応表を作る作業)。
