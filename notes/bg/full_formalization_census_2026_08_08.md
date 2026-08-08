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
| §14 | 12 (+1?) | ⬜ **14.11 が未発見** — ページ画像で要確認 |
| §15 | 9 | |
| §16 | 1 | |
| **小計** | **161** | (14.11 を入れると 162) |

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
| 同 (private の重複) | `BG/AppA_PStability.lean:143` |
| `zmod_smul_ofMul` | `GroupTheory/CommGroupAut.lean:111` |

しかも新設した `mulAutToEnd` は `ExtraspecialSinger.lean` で**名前解決の曖昧化を起こして
ビルドを壊した** (引数順が違う `(p) {E}` vs `(E) (p)` なので型エラーとして出た)。
⟹ **汎用の小さい def を足す前に、名前と「型の形」の両方で grep する**
([[grep-abbreviations-not-just-full-names]] [[grep-before-writing-transport-defs]])。
⚠ `AppA_PStability.lean` の private 複製は残置 (OperatorMaschke 版へ寄せるのは follow-up)。

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

### ⬜ §3 の残り (次イテレーション)

Lem 3.3 / Thm 3.4 / Thm 3.6 / Thm 3.8 / Prop 3.9 / Thm 3.10 の **条項ごとの照合が未了**
(実体の所在は確定済、statement の逐語照合はこれから)。
Thm 3.10 は AxiomsCheck に (a)(b)(c) が分散登録されており、**書籍の 3 条項が
1 つの statement に揃っているか**を確認する必要がある。

### §4-§16 + Theorems A-E + 補章 — 未着手
