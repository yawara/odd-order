---
id: 3021
slug: appe-hall-collection
title: "BG App.E 全体の唯一の unlock = Hall's collecting process (一般 class ≤ p−1)"
created: 2026-07-18
---

# BG App.E: 全体の唯一の unlock = Hall's collecting process

## 済: opaque scaffold の de-opacify (2026-07-18)

`AppE_FurtherResults.lean` は 163 行の **opaque-Prop scaffold** (全仮説・結論が自由 `Prop` +
自己保持 `_holds` ⟹ `∃ data, …` が自明に充足) で、E.1-E.5 に 1:1 対応する 5 sorry があったが
**book strength の内容はゼロ**だった。482 行に書き直し、**opaque フィールド 0 / `_holds` 0**
(コメント除去後) を確認済。実 sorry 9 は全て **honest な book-strength statement の下**にある
(「opaque で sorry-free」より「honest + sorry」を優先 = CLAUDE.md 方針)。

**sorry-free で証明済 (全 axiom-clean)**: `collectionTail_zero` / `collectionTail_one` /
`collectionTail_eq_of_eq_one_of_three_le` / **`hallCollection_of_class_le_two`** (E.1 の class≤2、
既存 `GroupTheory.mul_pow_eq_commutator_pow_mul_of_class_le_two` に接続) /
**`pow_mul_of_class_le_two`** (E.2(b) の class≤2) / `RegularOperatorSetup.isAInvariant_R₀` /
**`RegularOperatorSetup.card_A_dvd_half_p_sub_one`** (= **E.3(a) 完成**、`q ∣ (p−1)/2`)。

honest statement + sorry: `hallCollection` (E.1 一般) / `pow_mul_of_commutator_pow_eq_one`
(E.2 Step1) / `omega_pow_eq_one_of_lowerCentralSeries_eq_bot` (E.2(a)) /
`pow_mul_of_commutator_le_omega` (E.2(b)) / E.3(b)(c)(d) 3 件 / E.4 / E.5。
E.3 の `RegularOperatorSetup` は 18 の実型付きフィールド (opaque でない)。
E.5 は §14-§16 の実語彙 (`IsMinimalSimpleOdd`/`maximalSubgroups`/`S10.Msigma`/`S14.maximalTypeFFamily`
等) で記述、仮説ブロックは既形式化の BG Cor 15.9 (`S16.centralizer_escape_final_local`) と同一。

## 残: 依存グラフは 1 つの根に収束

```
E.1 (Hall's collecting process, 一般 class ≤ p−1)  ← ★根。前提なし・自己完結
 └─ E.2 Step1 (記述済、E.1 待ち)
     └─ E.2(a) + |R| 帰納
         └─ E.2(b) (記述済)
         └─ E.3(b)(c) + BG §5 narrow-p-group 機構 (repo にあり)
             └─ E.3(d) + Schur-Zassenhaus 共役 (repo にあり)
             └─ E.4 + S/S' 固有値論法
                 └─ E.5 + §14 counting (Lem 14.5/Thm 14.7、repo にあり) + Cor 15.9 (repo にあり)
```

**App.E が BG §4/§5/§14/§15/§16 から必要とするものは全て repo に在る**。⟹ **一般 class ≤ p−1 の
Hall collecting process を形式化することが付録 E 全体の唯一の unlock**。純粋な交換子計算で
上流依存が無く、`OddOrder/GroupTheory/HallCollection.lean` 等の独立 leaf に書ける。
既存の class≤2/≤3 特殊例 (`S04_SmallRankBasic.lean`, `CriticalSubgroup.lean`,
`Isaacs/Ch04_Commutators/CommutatorBasics.lean`) が出発点。

⚠ shared infra (`OddOrder/GroupTheory/**`) ゆえ着手前に **9000 claim** + 既存検索。

## 完了条件

Hall collecting process (一般 class ≤ p−1) を形式化 → E.1 一般形 → E.2 → E.3(b)(c)(d) → E.4 → E.5
を順に sorry-free・axiom-clean 化。AppE の sorry が 0 に。survey App.E 行更新。
(E.3/E.4 は Feit-Thompson 1991 の regular-operator bound が別途要る可能性 — 着手時に再評価。)

## 参照
- `OddOrder/BG/AppE_FurtherResults.lean` (de-opacify 済、482 行)、mmd の App.E 節。
- 既存特殊例: `GroupTheory.mul_pow_eq_commutator_pow_mul_of_class_le_two` (CriticalSubgroup.lean:657)、
  `GroupTheory.Omega.pow_eq_one_of_class_le_two`。
- 関連: issue 3020 (App.D の Gorenstein §14.1 ブロッカー)。

## ⭐ 2026-07-20: E.1 / E.2(a) / E.2(b) 完了 — AppE sorry 9 → 7

- **E.1** (`hallCollection`) = Hall–Petresco 公式。Mann ルートで証明 (issue 9132、close 相当)。
  一般形 `GroupTheory.HallPetresco.exists_hallPetresco` は **m 生成元**・冪零性の仮定なし。
- **E.2 Step 1** = `GroupTheory.pow_mul_pow_eq_pow_of_commutator_exponent` (一般形、
  AppE の特殊形は削除して重複解消)。
- **E.2(a)(b)** = `omega_pow_eq_one_of_lowerCentralSeries_eq_bot` /
  `pow_mul_of_commutator_le_omega`。issue 9400 (`GroupTheory/RegularPGroup.lean`) の
  `pow_mul_eq_one_of_class_lt` 経由。⚠ **`IsPGroup` 仮説は未使用だったので両方から削除**
  (特殊化債務の返済)。

すべて sorry-free / axiom-clean。依存グラフの根 (E.1) と第 2 段 (E.2) が開いた。

## 残り 7 sorry と、E.3(b) の前提の実測 (2026-07-20)

| 宣言 | 書籍 |
|---|---|
| `RegularOperatorSetup.omega_pow_eq_one` | E.3(b) 第 1 節 (Ω₁(R) の指数が p) |
| `RegularOperatorSetup.R₀_not_le_derived_omega` | E.3(b) 第 2 節 |
| `RegularOperatorSetup.card_omega_abelianization` | E.3(b) 第 3 節 (`|Ω₁/Ω₁'| = p²`) |
| `RegularOperatorSetup.card_omega_le` | E.3(c) (`|Ω₁(R)| ≤ p^q`) |
| `RegularOperatorSetup.B_fixes_R₀_of_fixes_frattini` | E.3(d) |
| `RegularOperatorSetup.centralizer_upperCentralSeries_abelian_index_p` | E.4 |
| `maximalSubgroups_isTypeI_or_isTypeII` | E.5 |

### ⭐ E.3(b) Step 2 の前提は**全部 repo に在る** (新規 infra は不要)

BG 原文 (pdftotext L7922-8010) の Step 2 が使うもの:

| BG の引用 | repo の所在 |
|---|---|
| `SCN(S)` / `IsSCN₃` | `Ch1_Preliminary/S04_SmallRankBasic.lean:1041` |
| Lemma 4.5 | `Ch1_Preliminary/S04_PGroupsSmallRank.lean` (1043, 1372 で使用) |
| **Lemma 5.2** (`T = C_R(W)` の中心構造) | `Ch1_Preliminary/S05_NarrowSCN.lean:422` 以降 |
| **Theorem 5.3(d)** | `S05_Narrow*` 群 (Ch3 の `S12_Corollary1214.lean:292` が引用) |
| Theorem 5.5 の (5.5) 以降の鎖 | `Ch1_Preliminary/S05_NarrowAutomorphisms.lean:418` 以降 |
| **Proposition E.2** | ✅ 本 issue で今回完了 |

⟹ **E.3(b) は組み立て作業**であって、新しい基盤の構築ではない。Step 2 の筋:
`|S| ≥ p⁴` と仮定 → `V ∈ SCN(S)` から `r(S) ≥ 3` → `Z = Ω₁(Z(S))` に対し `|Z| = p`,
`C_S(R₀) = R₀ × Z` → S は narrow → Lemma 5.2 + Thm 5.3(d) で `T char S`,
`|S:T| = |C_T(R₀)| = p`, `R₀ ∩ T = 1` → Thm 5.5 の鎖で A-不変列 `T = H₀ ⊃ … ⊃ Hₙ = 1`
(`|H_{i-1}:H_i| = p`) → `H₁ = S₂` かつ `|S/S'| = p²` (E.7) → 帰納で `H_i = S_{i+1}`。

### 次段の着手順

E.3(b) 第 1 節 (`omega_pow_eq_one`) が E.3 全体の入口。上表の repo 補題を実測で
名前確認してから Step 2 を組む。E.3(c) は Step 2 の固有値計数、E.3(d) は Step 4
(Schur–Zassenhaus)、E.4 は E.3 を全部消費、E.5 は §14 counting + Cor 15.9。

## E.3(b) Step 2 が cite する repo 補題 — 正確な signature (2026-07-20 実測)

**`OddOrder.BG.Ch1.S05.lemma52`** (`S05_NarrowSCN.lean:1181`) — **BG Lemma 5.2**:
```lean
theorem lemma52 [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) (E : Subgroup R) (hEcard : Nat.card ↥E = p ^ 2)
    (hEstar : IsMaximalElementaryAbelian p E) :
    ¬ E ≤ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) ∧
    (Nat.card ↥(omega1Center R p) = p ∧
      (omega1UpperCentralTwo R p).IsElementaryAbelian p ∧
      Nat.card ↥(omega1UpperCentralTwo R p) = p ^ 2) ∧
    (Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)).index = p
```
⟹ BG の `T = C_R(Ω₁(Z₂(R)))` は repo では
`Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)`。**`|R : T| = p` が直接出る**。

**`narrow_centralizer_decomp`** (`S05_NarrowCharacterization.lean:726`) — **BG Theorem 5.3(d)**。
docstring に「**下流 App.E E.3 が cite**」と明記されており、まさに本用途で用意済:
```lean
theorem narrow_centralizer_decomp [Finite R] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hpg : IsPGroup p R) (h3 : 3 ≤ pRank R p) (hnarrow : IsNarrow p R)
    (S : Subgroup R) (hScard : Nat.card ↥S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2) :
    IsCyclic ↥(C_R(S) ⊓ T) ∧ S ⊓ commutator R = ⊥ ∧ S ⊓ T = ⊥ ∧
    Subgroup.centralizer (S : Set R) = S ⊔ (C_R(S) ⊓ T)
```
⟹ BG Step 2 の `R₀ ∩ T = 1` と `C_R(R₀) = R₀ × C_T(R₀)` がそのまま。

**その他**: `exists_narrow_witness_of_three_le_pRank` (`S05_NarrowSCN.lean:1207`) が
`IsNarrow` から BG の `R₀`(位数 p) + `R₁`(cyclic) + `C_R(R₀) = R₀ ⊔ R₁` を取り出す。
`narrow_iff_exists_card_prime_centralizer_pRank_le_two` (Cor 5.4) で narrow 性を供給。
`scn3_nonempty_of_three_le_pRank` が `SCN₃` を供給。

### ⟹ E.3(b) 第 1 節の組み立て手順 (次段)

1. `|S| ≤ p³` の場合分けを潰す (BG: 「`q ≥ 3` なので位数 `p³` 以下の p 群を調べれば従う」)。
2. `|S| ≥ p⁴` として `SCN(S)` から `r(S) ≥ 3`、`Z = Ω₁(Z(S))` に `|Z| = p`,
   `C_S(R₀) = R₀ × Z` (setup の `C_R(R₀) = R₀ × R₁` から)。
3. `S` が narrow (Cor 5.4: 位数 p の `R₀` で `r(C_S(R₀)) ≤ 2`)。
4. `lemma52` で `|S : T| = p`、`narrow_centralizer_decomp` で `R₀ ⊓ T = ⊥` と分解。
5. Thm 5.5 の鎖 (`S05_NarrowAutomorphisms.lean:418` 以降) で A-不変列
   `T = H₀ ⊃ … ⊃ Hₙ = 1`, `H_i = [R₀, H_{i-1}]`, `|H_{i-1}:H_i| = p`。
6. `H₁ = S₂` と `|S/S'| = p²` (E.7)、帰納で `H_i = S_{i+1}`。
7. 極大性と **Prop E.2** (完了済) の矛盾で `Ω₁(R)` 自体が指数 p。

⚠ 手順 1 の「位数 `p³` 以下の p 群の検査」は BG が省略している箇所。repo の
`S04_PGroupsSmallRank.lean` に該当補題があるか着手時に実測すること。

## ⚠ 2026-07-20: 手順 1 (`|S| ≤ p³`) の対応物と、既存の同型証明を発見

### (i) BG が省略する「位数 p³ 以下の p 群の検査」

`S04_PGroupsSmallRank.lean` に必要な形が既にある:

- **`card_le_prime_cube_of_pRank_le_two_of_exponent_prime`** (:508) —
  `r(R) ≤ 2` かつ指数 p ⟹ `|R| ≤ p³`。E.3 Step 2 の `|S| ≤ p³` 分岐はこの**対偶**
  (`|S| > p³` ⟹ `r(S) ≥ 3`) として使える。実際 BG も直後に `r(S) ≥ 3` を出しているので、
  **`|S| ≤ p³` の個別検査を経由せずこの補題で直接 `r(S) ≥ 3` を取る方が短い**。
- **`nilpotencyClass_le_of_card_le_pow`** (:686) — `|G| ≤ p^{j+1}` ⟹ `cl(G) ≤ j`。
  小さい位数での class 評価が要るときはこれ。

### (ii) ⚠ 既存 `omega1_pow_eq_one_of_pRank_le_two_of_three_lt` (:819) は
### 今回の `pow_mul_eq_one_of_class_lt` と**同型の帰納**

BG Prop 4.3 の `r(R) ≤ 2` 版で、docstring を読むと骨格が完全に一致する:
「`⟨x,y⟩ ≠ R'` なら IH / `⟨x⟩ = R'` なら abelian / それ以外は極大正規 `S ⊇ ⟨x⟩` を取り
IH で `Ω₁(S)` の指数 p …」。違いは最後の詰めだけ — 既存版は `|Ω₁(S)| ≤ p³` から
`|R'| ≤ p⁴` → `cl ≤ 3` → weight-3 交換子が中心、と**class ≤ 3 に落として**閉じるのに対し、
今回の `GroupTheory.pow_mul_eq_one_of_class_lt` は **Hall の公式 (E.1) で任意の class < p**
を直接扱う。

⟹ **E.1 が証明できた今、既存の `r(R) ≤ 2` 版は今回の一般版から導ける可能性が高い**
(`r(R) ≤ 2` かつ `p > 3` ⟹ class < p を示せばよい)。これは特殊化債務の解消候補。
⚠ ただし `S04_PGroupsSmallRank.lean` は BG Ch1 の leaf で **AppE より上流**なので、
GroupTheory 版を cite する形に書き換えるのは import 的には可能 (GroupTheory ⊂ 上流)。
着手は E.3 完了後の低優先タスクとし、**先に E.3 本体を進める**。

### 更新した手順 1

× 「`|S| ≤ p³` の場合分けを潰す」
○ **`card_le_prime_cube_of_pRank_le_two_of_exponent_prime` の対偶で
   `|S| > p³` ⟹ `r(S) ≥ 3` を直接得る** (BG の (E.1)-(E.3) 相当をまとめて飛ばせる)。

## E.3(b) 入口の証明筋 (2026-07-20 に BG の 1 行を展開)

`RegularOperatorSetup` の実フィールド (実測): `R₀_card : Nat.card ↥R₀ = p` /
`R₁_cyclic : IsCyclic ↥R₁` / `centralizer_eq : Subgroup.centralizer (R₀ : Set R) = R₀ ⊔ R₁` /
`R₀_disjoint_R₁ : Disjoint R₀ R₁` / `A_fixes_R₀` / `A_regular` ほか。

### BG の「Since `C_R(R₀) = R₀ × R₁`, we have `R₀ ∩ Z = 1`」の中身

`Z = Ω₁(Z(S))` (`S ≤ R`, `R₀ ≤ S`)。`R₀` は位数 p なので `R₀ ⊓ Z` は `⊥` か `R₀`。
後者なら `R₀ ≤ Z ≤ Z(S)` ⟹ **`S ≤ C_R(R₀) = R₀ ⊔ R₁`** ⟹ `r(S) ≤ r(R₀ ⊔ R₁) ≤ 2`、
これは Step 2 で先に出した `r(S) ≥ 3` に矛盾。⟹ `R₀ ⊓ Z = ⊥` ✓

つまり本当に要るのは次の 2 本 (どちらも BG は明示しない):

1. **`C_R(R₀) = R₀ ⊔ R₁` はアーベル** — `R₀` は centralizer の定義からその中で中心的、
   `R₁` は cyclic。中心的部分群と cyclic 部分群で生成される群はアーベル
   (`Subgroup.mul_normal` で join = 積集合にしてから成分ごとに可換)。
2. **`pRank ↥(R₀ ⊔ R₁) p ≤ 2`** — 上のアーベル性 + `|R₀| = p` (cyclic) + `R₁` cyclic。
   2 つの巡回部分群で生成されるアーベル群の p-rank は ≤ 2。
   ⚠ repo に該当補題があるか要実測 (`pRank_mono_of_le` は S04_SmallRankBasic にある)。

そこから `r(S) ≥ 3` は `card_le_prime_cube_of_pRank_le_two_of_exponent_prime`
(S04_PGroupsSmallRank.lean:508, `hexp : ∀ x : S, x ^ p = 1` = 型全体の指数) の**対偶**を
`↥S` に適用して得る (`|S| > p³ ⟹ r(S) ≥ 3`)。⟹ 手順 1-2 が閉じる。

### 次に書く Lean (この順)

- [ ] `RegularOperatorSetup.isMulCommutative_centralizer_R₀` — 上の 1。
- [ ] `RegularOperatorSetup.pRank_centralizer_R₀_le_two` — 上の 2。
- [ ] `three_le_pRank_of_prime_cube_lt_card` (対偶、2 行) を `↥S` に適用。
- [ ] `R₀ ⊓ Ω₁(Z(S)) = ⊥` と `|Ω₁(Z(S))| = p`、`C_S(R₀) = R₀ × Ω₁(Z(S))` (E.4)。
- [ ] narrow 性 (Cor 5.4) → `lemma52` → `narrow_centralizer_decomp` → Thm 5.5 の鎖。

⚠ `Subgroup R` と `Subgroup ↥S` (`subgroupOf`) の往復が多くなるので、可能な限り
**ambient (`Subgroup R`) の言明**で書き、`↥S` に降りるのは pRank / 指数の評価だけにする。

## 2026-07-20: 補題 (1) は **repo に既存** — 重複を回避

`OddOrder.BG.Ch4.S15.isMulCommutative_sup_of_le_centralizer`
(`Ch4_FamilyOfMaximal/S15_MF/PisetBetaDisjoint.lean:935`):
```lean
theorem isMulCommutative_sup_of_le_centralizer {A B : Subgroup G}
    (hA : IsMulCommutative ↥A) (hB : IsMulCommutative ↥B)
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) : IsMulCommutative ↥(A ⊔ B)
```
AppE は `S16_MainResults` を import しており S15 はその上流なので**そのまま使える**。
⟹ 「`C_R(R₀) = R₀ ⊔ R₁` はアーベル」は新規に書かず、これに
`R₀` の可換性 (位数 p ⟹ cyclic)、`R₁_cyclic`、`R₀ ≤ C_R(R₁)` (= `R₁ ≤ C_R(R₀)` の対称形、
`centralizer_eq` から) を渡すだけ。

## 残る唯一の新規補題 = (2) `pRank ↥(C_R(R₀)) p ≤ 2`

`C = R₀ ⊔ R₁` はアーベル、`|R₀| = p`、`R₁` cyclic、`Disjoint R₀ R₁`。
**証明の筋** (elementary abelian `A ≤ C` について `|A| ≤ p²` を示す):
- `A ⊓ R₁` は cyclic p 群 `R₁` の elementary abelian 部分群 ⟹ **位数 ≤ p**
  (cyclic p 群の位数 p の部分群は高々 1 つ; repo に
  `card_omega1OfAbelian_eq_of_isCyclic` = `OmegaSubgroup.lean:379` あり)。
- `C` アーベル ⟹ `R₁ ⊴ C`、第二同型定理で `A/(A ⊓ R₁) ≅ AR₁/R₁ ≤ C/R₁`。
- `C/R₁ = (R₀ ⊔ R₁)/R₁ ≅ R₀/(R₀ ⊓ R₁) = R₀` (`Disjoint R₀ R₁`) ⟹ **位数 p**。
- ⟹ `|A| = |A ⊓ R₁| · |A/(A ⊓ R₁)| ≤ p · p = p²` ⟹ `Nat.log p |A| ≤ 2`。
- `pRank` は `⨆ A : {A // IsElementaryAbelian p A}, Nat.log p |A|` (`PRank.lean:423`) なので
  `ciSup_le` で閉じる (添字型は `⊥` で nonempty)。

⚠ 一般形 (「アーベル群が cyclic 部分群を指数 p で含むなら p-rank ≤ 2」) で書けば
`S04_SmallRankBasic.lean` (:1080 に `not_le_pRank_of_pRank_le_two` がある = topical な home)
に置くのが筋。ただし同 leaf は上流でリビルドが重いので、**2 消費者目が出るまでは
AppE の private helper で可**。その場合は本 issue に promotion フラグを残すこと。

## ⭐ 2026-07-20 (2): BG の 1 行 `R₀ ∩ Z = 1` を完全に展開 — 8 定理を sorry-free 化

上の「残る唯一の新規補題 (2)」は **`GroupTheory/PRank.lean` に一般形で置いた** (private helper
にせず promotion 済 — pRank API の topical home ゆえ; shared-infra claim = **issue 9401**)。
`normal` 仮説は不要と判明したので落とした (集合積のまま積公式を使うため)。

| 新規宣言 | 内容 | 場所 |
|---|---|---|
| `GroupTheory.pRank_le_two_of_isCyclic_of_index_le_prime` | cyclic 部分群の指数 ≤ p ⟹ `pRank ≤ 2` | `PRank.lean:666` |
| `RegularOperatorSetup.R₀_le_centralizer_R₁` | `centralizer_eq` の対称半分 | AppE |
| `RegularOperatorSetup.isMulCommutative_centralizer_R₀` | `C_R(R₀)` はアーベル | AppE |
| `RegularOperatorSetup.card_centralizer_R₀` | `\|C_R(R₀)\| = p·\|R₁\|` | AppE |
| `RegularOperatorSetup.pRank_centralizer_R₀_le_two` | `r(C_R(R₀)) ≤ 2` | AppE |
| `three_le_pRank_of_prime_cube_lt_card` | BG (E.1)-(E.3) = 既存 S04 補題の対偶 | AppE |
| `RegularOperatorSetup.not_le_centralizer_R₀_of_three_le_pRank` | `r(S) ≥ 3 ⟹ S ⊄ C_R(R₀)` | AppE |
| `RegularOperatorSetup.inf_eq_bot_of_three_le_pRank` | **BG の 1 行 `R₀ ∩ Z = 1`** | AppE |

全て sorry-free / AxiomsCheck OK (4497 jobs green)。AppE の sorry は 7 のまま
(新規は全部 sorry-free な下ごしらえ)。

⚠ `inf_eq_bot_of_three_le_pRank` は `Z ≤ Z(S)` を **ambient で `S ≤ C_R(Z)` と綴った**
(`subgroupOf` 往復を避けるため)。BG の `Z = Ω₁(Z(S))` を渡すときはこの形で供給する。

## BG 原文 Step 2 の実測 (pdftotext L7955-8060) と、次に要るもの

Step 2 の**主張**: 「`S` を `R` の A-不変・指数 p・`R₀` を真に含む部分群とすると
`R₀ ⊄ S'`、`|S| ≤ p^q`、`|S/S'| = p²`」。証明の骨格 (実測):

1. `|S| ≤ p³` は「位数 p³ 以下の p 群の検査」で片付く (BG が省略) → **迂回済**:
   `three_le_pRank_of_prime_cube_lt_card` で `|S| > p³ ⟹ r(S) ≥ 3` を直接得る。
2. `Z = Ω₁(Z(S))`、**`R₀ ∩ Z = 1`** ← ✅ 今回 (`inf_eq_bot_of_three_le_pRank`)。
3. (E.4) `R₀ × Z ⊆ C_S(R₀) ⊆ R₀ × Ω₁(R₁)` ⟹ `|Z| = p` かつ `C_S(R₀) = R₀ × Z`。
   ⟹ **次に書くのはこれ**。`S` は指数 p なので `S ⊓ R₁ ≤ Ω₁(R₁)` (位数 p、R₁ cyclic)、
   よって `C_S(R₀) = S ⊓ (R₀ ⊔ R₁) ≤ R₀ ⊔ Ω₁(R₁)` は位数 ≤ p²。
   `Z ≠ 1` は `Z(S) ≠ 1` (非自明 p 群) から。
4. `S` は narrow (Cor 5.4: 位数 p の `R₀` で `r(C_S(R₀)) ≤ 2`、`|C_S(R₀)| = p²` より)。
5. (E.5) `lemma52` + `narrow_centralizer_decomp` で `T char S`, `|S:T| = |C_T(R₀)| = p`,
   `R₀ ⊓ T = 1`、`S = R₀T`。
6. (E.6) Thm 5.5 の (5.5) 以降で A-不変列 `T = H₀ ⊃ … ⊃ Hₙ = 1`,
   `H_i = [R₀, H_{i-1}]`, `|H_{i-1}:H_i| = p`。
7. (E.7) `H₁ = S₂` かつ `|S/S'| = p²`、(E.8) 帰納で `H_i = S_{i+1}`。
8. (E.9)-(E.12) 固有値 `r_i ≡ r₀ r^i (mod p)` の計算 + `A` の regular 性 (Prop 1.5(d)) で
   `r_i ≢ 1`、`r^q ≡ 1` ⟹ `q - 1 ≥ n` ⟹ `|S| = p·pⁿ ≤ p^q`。← **(c) の出所**。

⟹ **Step 2 を明示の定理として AppE に立てる**のが次の構造上の一手 (現状 AppE には
Step 2 の言明が無く、E.3(b) の 3 clause が直接 sorry になっている)。Step 3 は
「`R₀ × Ω₁(R₁)` を含む極大な A-不変指数 p 部分群 `S`」を取って Step 2 を適用し、
`Ω₁(N_P(S))` の議論 (E.15)-(E.16) で `S = Ω₁(R)` を出す。

## ⭐ 2026-07-20 (3): Step 2 の narrow 経路が通った — **`R₀ ⊄ S'` を証明**

`r(S) ≥ 3` かつ `R₀ ≤ S` なる**任意の** `S ≤ R` について:

| 新規宣言 | BG 対応 |
|---|---|
| `RegularOperatorSetup.card_R₀_subgroupOf` | `\|R₀\| = p` を `↥S` 内で |
| `RegularOperatorSetup.pRank_centralizer_subgroupOf_le_two` | `r(C_S(R₀)) ≤ 2` |
| `RegularOperatorSetup.isNarrow_of_three_le_pRank` | **"Note that S is narrow."** |
| `RegularOperatorSetup.not_le_derivedInG_of_three_le_pRank` | **(E.13) 第 1 節 `R₀ ⊄ S'`** |
| `RegularOperatorSetup.card_omega1Center_and_index_centralizer` | **(E.4) `\|Z\| = p` + (E.5) `\|S:T\| = p`** |

### ⚠ BG より弱い仮説で通った (特殊化債務でなく一般化)

BG は `r(C_S(R₀)) ≤ 2` を **(E.4) の `\|C_S(R₀)\| = p²`** から出すが、こちらは
`C_S(R₀) ≤ C_R(R₀)` の**単調性**だけで出る。⟹ **`S` の指数 p 仮説が要らない**。
同じ理由で Lemma 5.2 が要求する「位数 p² の極大 elementary abelian `E`」は
narrow 性から直接取れる (`narrow_iff_exists_maximalElementaryAbelian_card_prime_sq`) ので、
BG の witness `E = C_S(R₀)` と `\|C_S(R₀)\| = p²` の計算は**丸ごと迂回できる**。

⟹ 当初の計画にあった「(E.4) の `R₀ × Z ⊆ C_S(R₀) ⊆ R₀ × Ω₁(R₁)` を形式化する」は
**Step 2 の経路上では不要**と判明。`Ω₁(R₁)` の位数 p 計算も現時点では不要
(必要になるのは Step 3 の極大性議論で `R₀ × Ω₁(R₁)` を種にするとき)。

### ⭐ 2026-07-20 (4): `|S| ≤ p³` 分岐も閉じた ⟹ **`R₀ ⊄ S'` が無条件で成立**、AppE sorry 7 → 6

BG が「位数 p³ 以下の p 群を検査せよ」と省略する分岐は、**検査不要**と判明:

- `derived_central_of_card_le_prime_cube`: `|S| ≤ p³ ⟹ cl(S) ≤ 2` (既存
  `S04.nilpotencyClass_le_of_card_le_pow`) ⟹ `S' ≤ Z(S)`。
- `not_le_derivedInG_of_derived_central`: **`S' ≤ Z(S)` だけで `R₀ ⊄ S'` が出る** —
  `R₀ ≤ S'` なら `S` は `S'` を中心化 ⟹ `R₀` を中心化 ⟹ `S ≤ C_R(R₀)` は**アーベル**
  ⟹ `S' = 1` ⟹ `R₀ = 1`、`|R₀| = p` に矛盾。⚠ `R₀ ≤ S` 仮説すら不要。
- `not_le_derivedInG`: 2 分岐を `three_le_pRank_of_prime_cube_lt_card` で接合 ⟹
  **指数 p の任意の `S ⊇ R₀` について `R₀ ⊄ S'`** (BG の A-不変性・真部分群性は未使用)。
- `R₀_le_omega`: `R₀ ≤ Ω₁(R)`。

⟹ **E.3(b) 第 2 節 `R₀_not_le_derived_omega` を実証明**した (`S = Ω₁(R)` に適用)。
指数 p の入力だけ第 1 節 `omega_pow_eq_one` (Step 3、まだ sorry) から cite している
= 規約の sorried-cite パターン。**AppE の sorry は 7 → 6**。

### 残る Step 2 の穴 (次に着手する順)

1. ~~`|S| ≤ p³` の分岐~~ ✅ 完了 (上記)。
### ⭐ 2026-07-20 (5): (E.4) と (E.5) を証明

| 新規宣言 | BG 対応 |
|---|---|
| `centralizer_inf_eq_sup_omega1Center` | **(E.4) `C_S(R₀) = R₀ × Ω₁(Z(S))`, 位数 p²** |
| `centralizer_subgroupOf_eq` | `C_{↥S}(R₀) = (S ⊓ C_R(R₀)).subgroupOf S` の橋 |
| `card_centralizer_inf_centralizer_eq` | **(E.5) `\|C_T(R₀)\| = p`** |

**(E.4) の上界は BG より安く取れた**: BG は `C_S(R₀) ⊆ R₀ × Ω₁(R₁)` (位数 p²) で押さえるが、
`C_S(R₀)` は elementary abelian (アーベル ⟸ `C_R(R₀)` がアーベル、指数 p ⟸ `S`) で
`r(C_R(R₀)) ≤ 2` の中に居るので `\|C_S(R₀)\| ≤ p²` が直接出る。
⟹ **`Ω₁(R₁)` の位数計算は結局一度も要らなかった**。下界は `R₀ × Z` (位数 p²、
`\|Z\| = p` は lemma52、`R₀ ∩ Z = 1` は既出) で、両者が一致。

(E.5) は Thm 5.3(d) の内部直積分解 `C_S(R₀) = R₀ × C_T(R₀)` + (E.4) から。
⟹ BG の `\|S : T\| = \|C_T(R₀)\| = p` が両半分そろった。

### 残る Step 2 の穴 (更新)

2. **(E.6) Thm 5.5 の A-不変列** `T = H₀ ⊃ … ⊃ Hₙ = 1`, `H_i = [R₀,H_{i-1}]`,
   `|H_{i-1}:H_i| = p` — **計数の核は完了 (下記)**、残るのは鎖の構成と厳密降下。
3. **(E.7)(E.8)** `H₁ = S₂`, `|S/S'| = p²`, 帰納で `H_i = S_{i+1}`。
   ⟹ E.3(b) 第 3 節 `|Ω₁(R)/(Ω₁(R))'| = p²` の出所。
4. **(E.9)-(E.12)** 固有値 `r_i ≡ r₀ r^i`、`A` regular + Prop 1.5(d) ⟹ `r_i ≢ 1`、
   `r^q ≡ 1` ⟹ `n ≤ q-1` ⟹ `|S| ≤ p^q`。⟹ **E.3(c)** の出所。
5. Step 3 (極大 `S` + `Ω₁(N_P(S))` の (E.15)-(E.16)) ⟹ **E.3(b) 第 1 節**。

## ⭐ 2026-07-20 (6): (E.6) の計数の核が完了

BG が「a short argument using the mapping `H → [R,H]` given by `x ↦ [v,x]`」で済ませる部分:

- **`Ch1.S05.card_le_card_mul_of_commutator_mem_of_card_centralizer_le` を public 化**。
  これは Thm 5.5 自身の `H_i` 鎖の計数エンジンで、**App.E が要るのは全く同じ補題**
  (だから BG は「Thm 5.5 の (5.5) 以降の証明をなぞれ」と書ける)。仮定は純粋な計数のみ
  (p 群性・奇数性・narrow 性なし)。ファイル跨ぎ `private` は規約違反なので public 化が正。
- **`RegularOperatorSetup.card_le_card_commutator_mul_prime`**: App.E 版
  `|H| ≤ |⁅R₀,H⁆| · p` (`H ≤ T`)。`R₀` の生成元 `v` と `|C_H(v)| ≤ |C_T(R₀)| = p` (E.5) を渡す。

### ⭐ 同日: (E.6) の 1 段分も完了 — `card_eq_prime_mul_card_commutator`

非自明正規 `H ≤ T` について **`|H| = p · |⁅R₀,H⁆|`**。2 つの評価が一致:
- `≤` は上の計数ステップ。
- `≥` は `⁅R₀,H⁆ = ⁅H,R₀⁆ < H` (冪零性、既存
  `Isaacs.Ch04.commutator_lt_self_of_isNilpotent_ambient` がそのまま使えた) +
  「p 群の真部分群の指数は p で割れる」。

⟹ BG の `|H_{i-1} : H_i| = p` の**帰納段が完成**。

### ⭐ 同日: BG の `[R,H] = [R₀,H]` を証明 — `commutator_R₀_eq_commutator_top`

**この同一視は計数の *帰結* であって前提ではない**と判明した:
`⁅R₀,H⁆ ⊆ ⁅S,H⁆` は単調性、逆は `⁅S,H⁆` が p 群 `H` の真部分群 (冪零性) ゆえ
`|⁅S,H⁆| ≤ |H|/p = |⁅R₀,H⁆|`。⟹ 上の 1 段補題からそのまま出る。

構造上の意味: **`⁅S,·⁆` は `S` 内の正規性を保つが `⁅R₀,·⁆` は保たない**
(`R₀` は `S` で正規でない)。だから BG は鎖を `[R,H_{i-1}]` 形で定義して `H_i char R`
を確保し、その上で `[R₀,H_{i-1}]` と同一視している。形式化も同じ順序で行う。

副産物: `prime_mul_card_le_card_of_lt` (p 群の真部分群は指数が p で割れる) を private
helper に切り出した。2 箇所で使用。3 消費者目が出たら `OddOrder/GroupTheory/` へ promote。

### ⭐ 同日: **(E.6) 完了** — 鎖と `|T| = pⁿ`

**新しい def は不要だった**: BG の鎖は repo 既存の
`Isaacs.Ch04.iterCommutator T ⊤` (全体群との反復右交換子) そのもので、
`iterCommutator_eq_bot_of_isNilpotent_ambient` (鎖が ⊥ に到達) まで既にある。

| 新規宣言 | BG 対応 |
|---|---|
| `card_iterCommutator_eq` | **`\|H_i\| = p · \|H_{i+1}\|`** (`H_i ≠ ⊥` の間) |
| `card_start_eq_pow_mul` | **`\|T\| = p^i · \|H_i\|`** ⟹ 最後の非自明添字で `\|T\| = pⁿ` |

private helper: `normal_iterCommutator` / `iterCommutator_antitone` /
`iterCommutator_le_start` (鎖の正規性・降下・`≤ T`)。

⟹ **Step 2 の (E.1)-(E.6) が全部そろった**。

### 残り (Step 2 の後半)

1. ✅ **`S = R₀T` 完了** (`sup_centralizer_eq_top`)。BG の `T char S` は repo に
   **instance として既存** (`GroupTheory.centralizer_omega1UpperCentralTwo_characteristic`)
   なので、`↑(R₀ ⊔ T) = ↑R₀ * ↑T` の正規性は推論で見つかる。⚠ 指数 p 仮説は不要だった。
   ⟹ **(E.5) が完全にそろった**。
2. ✅ **(E.7) 完了** (`commutator_eq_and_card_quotient`): `H₁ = S'` かつ `|S/S'| = p²`。
   `|S:H₁| = p²` は `|S:T| = p` (E.5) + `|T:H₁| = p` (E.6) から。`S/H₁` は位数 p² ゆえ
   アーベル ⟹ `S' ≤ H₁`。逆は `H₁ = ⁅T,S⁆ ≤ ⁅S,S⁆ = S'` (BG は `[R₀,T]` 経由だが
   鎖の定義そのものを使う方が短い)。

   ⚠ **これは `3 ≤ pRank S` を仮定するので、`S = Ω₁(R)` に入れても E.3(b) 第 3 節は
   まだ閉じない**。`|S| ≤ p³` 分岐が要る。⚠ `R₀ ⊄ S'` の分岐 (`S' ≤ Z(S)` だけで済んだ)
   と違い、こちらは**位数 p²/p³ の場合分けが実際に要りそう**:
   - `S` アーベル: `S ≤ C_R(R₀)` ⟹ `pRank ≤ 2` + 指数 p ⟹ `|S| ≤ p²`。
     `R₀ < S` (真) ⟹ `|S| ≥ p²` ⟹ `|S| = p²`、`S' = ⊥`、`|S/S'| = p²` ✓
   - `S` 非アーベル (⟹ `|S| = p³`): `cl(S) ≤ 2` ⟹ `S' ≤ Z(S)`、`S' ≠ 1`;
     `S/Z(S)` 非巡回 (mathlib `isMulCommutative_of_isCyclic_quotient_center_self` の対偶)
     ⟹ `|Z(S)| = p` ⟹ `S' = Z(S)`、`|S/S'| = p²` ✓
   ⟹ **ここで初めて BG の「`R₀ < S` 真部分群」仮説が効く**。

### ⭐ 2026-07-20 (7): **E.3(b) 第 3 節を証明** — AppE sorry 6 → 5

| 新規宣言 | 内容 |
|---|---|
| `commutator_le_center_of_card_le_prime_cube` (private) | `\|G\| ≤ p³ ⟹ G' ≤ Z(G)` (既存の cl≤2 論法を抽出) |
| `card_quotient_commutator_of_card_le_prime_cube` | **`\|S\| ≤ p³` 分岐** (上記の筋どおり) |
| `card_quotient_commutator` | 2 分岐を接合 ⟹ 指数 p の任意の `S ⊋ R₀` で `\|S/S'\| = p²` |
| `R₀_lt_omega` | **`R₀ < Ω₁(R)` (真)** |
| `card_omega_abelianization` | **E.3(b) 第 3 節** (sorry → 実証明) |

⚠ **`R₁` が Step 2 で初めて効いたのがここ**。第 3 節は `S = R₀` では**偽** (`p` になる) なので
真部分群性が要り、それを `R₁ ≠ 1` の位数 p 元 (R₀ と disjoint) から取る。
それ以前のステップは全部 `R₁` 無しで通っていた。

⚠ `|S| ≤ p³` 分岐は `R₀ ⊄ S'` のときと違って**本当に位数の場合分けが要った** —
BG の「位数 p³ 以下の p 群の検査」が実際に必要な唯一の箇所。
2. ✅ **(E.8) 完了** (`iterCommutator_eq_lowerCentralSeries`): `H_i = S_{i+1}`。
   (E.7) で `H₁ = S'` が付いた後は、`H_{i+1} = ⁅H_i,S⁆` と `γ_{i+1}(S) = ⁅γ_i(S),S⁆` が
   **同じ漸化式**なので帰納は即座。
3. **(E.9)-(E.12)**: 固有値 `r_i ≡ r₀ r^i (mod p)`、`A` regular + Prop 1.5(d) ⟹
   `r_i ≢ 1`、`r^q ≡ 1` ⟹ `n ≤ q-1` ⟹ `|S| = p·pⁿ ≤ p^q`。⟹ **E.3(c)**。
   - ✅ **(E.9) 冒頭 `vᵃ = vʳ`, `r^q ≡ 1`** = `exists_zpow_eq_act_of_mem_A`。
     `R₀` は位数 p の巡回群で `A` 不変 ⟹ 冪写像; `|A| = q` ⟹ `a^q = 1` ⟹ `r^q ≡ 1`。
     BG どおり**整数**冪で述べ、合同は `(r : ZMod p)^q = 1`。
   - ✅ **(E.11) `r ≢ 1 (mod p)`** = `zpow_exponent_ne_one`。`r ≡ 1` なら `a` が
     `R₀ ≠ 1` を点ごとに固定 ⟹ regular 性に矛盾。
     ⚠ **Step 2 で regular 性を使う最初の箇所** ((E.8) までは `|R₀| = p`・`R₁` cyclic・
     centralizer 分解だけで通っていた)。
   - ✅ **(E.10)-(E.12) の算術的終点** = `le_pred_of_forall_mul_pow_ne_one`。
     抽象的な有限**巡回**群で: `u ≠ 1`, `u^q = 1` (q 素数), `u₀^q = 1`,
     `∀ i < n, u₀ uⁱ ≠ 1` ⟹ `n ≤ q - 1`。
     巡回性がまさに `u₀ ∈ ⟨u⟩` を与える鍵で、`u₀ = uʲ` (`1 ≤ j ≤ q-1`) から
     `u₀ uⁱ = u^{j+i}` が 1 を避ける ⟹ 区間 `[j, j+n-1]` が `q` を外す。
     ⚠ **鎖上の固有値の帳簿付けより先に終点を証明した**ので現時点で consumer 無し。
     E.3(c) の `|S| ≤ p^q` はこれで閉じる。
   - ✅ **エンジンを抽象化** = `exists_zpow_eq_of_card_eq_prime`:
     位数 p (素数) の群の自己同型は冪写像 `x ↦ xʳ`、`φ^q = 1` なら `r^q ≡ 1`。
     **BG はこれを 2 回使う** — `R₀` に対してと、各切断 `H_i/H_{i+1}` に対して
     ((E.6) よりこれも位数 p) — ので 2 度証明せず切り出した。
     `exists_zpow_eq_act_of_mem_A` はその `R₀` への適用に書き換え済。
   - ✅ **(E.10) 完了** = `quotient_action_ne_one`: `a ∈ A^#` は非自明な切断
     `H_i/H_{i+1}` を中心化しない。誘導自己同型が `≠ 1` の形で述べた (これが内容)。
     ⚠ 記録どおり **`⟨a⟩` を作用群として** 要素形 Prop 1.5(d) を適用 (`A` 全体でなく)。
   - ✅ **(E.12) の数学的核** = `commutatorElement_pow_pow_of_central`:
     `⁅x,y⁆` が中心的なら `⁅x^m, y^n⁆ = ⁅x,y⁆^(m·n)`。repo には片スロットずつの形
     (`Ch1.S04.commutatorElement_pow_{left,right}_of_central`) しか無かったので、
     **双線形形**を組んだ (BG が (E.12) で実際に使うのはこちら)。
     右スロットは `⁅x^m, y⁆` に当てる — これが中心的なのは `⁅x,y⁆^m` に**等しい**から。
     ⚠ topical には S04_SmallRankBasic の 2 スロットの隣が home。消費者が 1 つの間は AppE に置く。
   - ✅ **`H̄_i ≤ Z(S̄)`** = `chain_map_le_center` (BG「`⟨w̄ᵢ⟩ = H̄ᵢ ≤ Z(S̄)`」)。
     鎖の定義そのものから即座 — `H_{i+1} = ⁅H_i, S⁆` ゆえ `H_i` の元との交換子は商で死ぬ。
     これが `commutatorElement_pow_pow_of_central` の中心性仮説そのものなので、
     Lemma 4.2(a) が商で使えるようになる。
   - ✅ **`w_i` 列** = `commutatorIterate` (`w₀ = w`, `w_i = ⁅w_{i-1}, v⁆`) +
     `commutatorIterate_mem_chain` (`w_i ∈ H_i`)。
     repo に**要素レベル**の反復交換子が無かったので新設 (`Isaacs.Ch04.iterCommutator` は
     部分群レベル)。⚠ `w ∈ T` だけでよく `v` は無制約 — 鎖が `R₀` でなく `S` 全体と
     bracket しているため。
   - ⬜ 残 (E.12 の最終組み立て)。**次の難所を 2026-07-20 に解析したので記録する**。

## ⭐ 2026-07-20: 新 leaf `AppE_RegularOperator.lean` を開始 (issue 0134 への対応)

`AppE_FurtherResults.lean` が 2000 行上限に達したので、以降の App.E 作業は新 sibling leaf
`OddOrder/BG/AppE_RegularOperator.lean` に置く。第一弾 = `commutator_mul_mem_chain`。

### ⚠ 下の「単射/ファイバー」経路は**より良い経路に置き換わった**

`commutator_mul_mem_chain`: `y ∈ H_i` に対し `(⁅v,x⁆*⁅v,y⁆)⁻¹ * ⁅v,x*y⁆ ∈ H_{i+2}`。
すなわち **`x ↦ ⁅v,x⁆` は準同型 `H_i → H_{i+1}/H_{i+2}`**。
⟹ `{x ∈ H_i | ⁅v,x⁆ ∈ H_{i+2}}` はその**核**で、`H_{i+1}` を含み、`H_i` 全体ではありえない
(そうなると `H_{i+1} ≤ H_{i+2}`)。`|H_i : H_{i+1}| = p` (素数) なのでちょうど `H_{i+1}`。
⟹ `⁅v,x⁆ ∈ H_{i+2} ⟺ x ∈ H_{i+1}` ⟹ `w ∉ H₁` から帰納で `w_i ∉ H_{i+1}`。

**この核論法は計数を一切使わない**ので、下記の tightness 経由の議論より簡単。

### ✅ 完了 (2026-07-20): BG の 5 語「So `⟨w̄ᵢ⟩ = H̄ᵢ`」を完全に回復

sorry-free の補題 5 本を要した:

1. `commutator_mul_mem_chain` — `x ↦ ⁅v,x⁆` が `H_{i+2}` を法として乗法的
2. `chainStepHom` — ゆえに準同型 `H_i →* G/H_{i+2}` (終域は周囲の商に取ると軽い)
3. `chainStepHom_ker_ge` — 核が `H_{i+1}` を含む (**易しい半分**)
4. `commutator_pow_mem_of_commutator_mem` + `commutator_zpowers_le_of_forall` —
   核が全体なら `⁅R₀, H_i⁆ ≤ H_{i+2}`
   (⚠ 4 の前半は `x` への仮説が不要だった: `⁅v,x⁆` が商で自明なら中心性は自動)
5. `RegularOperatorSetup.exists_commutator_not_mem` — `⁅R₀,H_i⁆ = ⁅S,H_i⁆ = H_{i+1}` と
   合わせて `H_{i+1} ≤ H_{i+2}` を強いるので矛盾 (**難しい半分**)

⟹ 核は `H_{i+1}` を含む真部分群、`|H_i : H_{i+1}| = p` が素数なのでちょうど `H_{i+1}`
⟹ `⁅v,x⁆ ∈ H_{i+2} ⟺ x ∈ H_{i+1}` ⟹ `w ∉ H₁` から帰納で `w_i ∉ H_{i+1}`。
(切り出した `index_centralizer_le_card_of_commutator_mem` 自体は補題の改善として有効だが、
ここでは不要になった。)

## (旧) BG が完全に省略している鍵: `⁅v, x⁆ ∈ H_{i+1} ⟺ x ∈ H_i` — tightness 経路

BG は `w ∈ H₀ − H₁` と置いて `w_i = [w_{i-1}, v]` を作り、後で **「So `⟨w̄ᵢ⟩ = H̄ᵢ`」**
と一言で済ませる。これは `w_i ∉ H_{i+1}` を要求するが、BG はその理由を書いていない。
実際には**計数が tight であること**から出る。以下、導出:

`M := H_{i-1}`, `N := ⁅R₀, H_{i-1}⁆ = H_i`, `C := C_M(v)` (`v ∈ R₀^#` は `R₀` の生成元) とする。

1. 既存 `Ch1.S05.card_le_card_mul_of_commutator_mem_of_card_centralizer_le` の証明中の
   単射 `M/C ↪ N` (写像 `x ↦ ⁅v,x⁆` は `C` の左剰余類上でちょうど定数) から
   `|M : C| ≤ |N|`。
2. 一方 `card_eq_prime_mul_card_commutator` は **等式** `|M| = p·|N|` を与える。
   また `|C| ≤ p` (= `card_le_card_commutator_mul_prime` の中で使った評価)。
3. `p·|N| = |M| = |C|·|M:C| ≤ |C|·|N|` ⟹ `p ≤ |C|` ⟹ **`|C| = p`** かつ
   **`|M:C| = |N|`** ⟹ 上の単射は**全単射** `M/C ≅ N`。
4. `⁅v,·⁆` による `H_{i+1}` の逆像は、全単射なので `M` の中でサイズ
   `|C|·|H_{i+1}| = p·(|H_i|/p) = |H_i|`。
5. 他方 `x ∈ H_i ⟹ ⁅v,x⁆ ∈ ⁅H_i, S⁆ = H_{i+1}` なので `H_i ⊆` 逆像。両者サイズ `|H_i|`
   ⟹ **逆像 = `H_i` ちょうど**。
   ⟹ **`⁅v, x⁆ ∈ H_{i+1} ⟺ x ∈ H_i`** (`x ∈ H_{i-1}` の下で)。
6. ⟹ `w_{i-1} ∉ H_i` なら `⁅v, w_{i-1}⁆ ∉ H_{i+1}`。`⁅w_{i-1}, v⁆ = ⁅v, w_{i-1}⁆⁻¹` も同様。
   `w ∉ H₁` から帰納して **`w_i ∉ H_{i+1}`** ⟹ `⟨w̄_i⟩ = H̄_i` (位数 p)。

✅ **形式化の障害は解消済 (同日)**: 手順 1 の単射は既存補題の*証明の中*にあったが結論が
不等式だけだったので、**`Ch1.S05.index_centralizer_le_card_of_commutator_mem`
(`|M : C_M(v)| ≤ |N|`) として切り出した**。予想どおり証明本体は既に単射を構成していたので
分離はコストゼロで、旧
`card_le_card_mul_of_commutator_mem_of_card_centralizer_le` は 3 行の系になった
(呼び出し側は無変更、S05 leaf + AppE + full AxiomsCheck で確認)。

### そこが出た後の残り
`chain_map_le_center` + `commutatorElement_pow_pow_of_central` で `r_i ≡ r_{i-1} r`、
帰納で `r_i ≡ r₀ r^i`、`le_pred_of_forall_mul_pow_ne_one` で `n ≤ q-1` ⟹ **E.3(c)**。

### (E.10) の道具は特定済 — 要素レベル形が public (2026-07-20 実測)

BG は「`r_i ≡ 1` なら Prop 1.5(d) で `A` が `H_i/H_{i+1}` を中心化し、`A` の regular 作用に
矛盾」と書く。repo に**要素レベル**の形がある (部分群レベルの
`GroupTheory/CoprimeFixedPoints.map_fixedSubgroup_eq_fixedSubgroup_quotient` より軽い):

```lean
-- OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean:800
theorem coprime_fixedPoints_quotient_of_coprime_normal
    {φ : A →* MulAut G} {N : Subgroup G} [N.Normal]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card ↥N))
    (hSolv : IsSolvable A ∨ IsSolvable ↥N)
    (hN_inv : IsAInvariant φ N) {g : G}
    (hg_fix : ∀ a : A, ∃ n ∈ N, φ a g = g * n) :
    ∃ c : G, (∀ a : A, (φ a) c = c) ∧ (∃ n ∈ N, c = g * n)
```

**組み立て方**: `G := ↥H_i`, `N := H_{i+1}.subgroupOf H_i`,
`φ := (isAInvariant_iterCommutator …).restrict` を
`A := ↥(Subgroup.zpowers (⟨a,ha⟩ : ↥hyp.A))` に制限して適用する
(仮説が特定の `a` についてなので `A` 全体でなく `⟨a⟩` を取るのがポイント)。
- `r ≡ 1 (mod p)` + 切断が位数 p ⟹ `x^r = x` ⟹ `a` は切断上自明 ⟹ `hg_fix` が成立。
- 結論の `c` は `a` に固定され、`g ∉ N` を取れば `c ∉ N` ゆえ `c ≠ 1`。
- `act a (c : R) = c` かつ `c ≠ 1` は `A_regular` に矛盾。
- 係数条件: `|⟨a⟩| ∣ q`、`|N|` は p 冪 ⟹ Coprime。`IsSolvable ↥N` は p 群ゆえ成立。
- 切断が位数 p は `index_subgroupOf_chain`、`H_{i+1} < H_i` は
  `card_eq_prime_mul_card_commutator` の証明中と同じ冪零性論法から。

### (E.9) 本体に要る配線

1. ✅ **`S` の A-不変性を仮説に追加** = `IsAInvariant (hyp.act.comp hyp.A.subtype) S`
   (`isAInvariant_R₀` と同型の形)。`IsAInvariant.restrict` で `↥A →* MulAut ↥S` に降りる。
2. ✅ **鎖の characteristic 性** = `characteristic_iterCommutator`。
   ⚠ **BG が鎖を `[R,H_{i-1}]` 形で定義する見返りがここ**: `⁅·,⊤⁆` は characteristic を
   保つが `⁅R₀,·⁆` は保たない (`R₀` は `S` で正規でない) — 両形が一致すること自体は
   `commutator_R₀_eq_commutator_top` で示してあるのに、である。
3. ✅ **鎖の A-不変性** = `isAInvariant_iterCommutator`
   (既存の `IsAInvariant.of_characteristic` に流すだけ)。
4. ✅ **切断の 2 入力がそろった**:
   - `index_subgroupOf_chain`: 切断は**位数 p** ((E.6) の `|H_i| = p·|H_{i+1}|` を
     「`H_i` の中での `H_{i+1}` の指数」の形に言い換え = quotient 機構が要求する形)。
   - `isAInvariant_subgroupOf_chain`: `H_{i+1}` は `↥H_i` の中で A-不変
     (`isAInvariant_iterCommutator` を `↥H_i` 上の制限作用に移送)。
5. ✅ **(E.9) 完了** = `exists_zpow_eq_on_chain_section`:
   `a ∈ A` に対し切断 `H_i/H_{i+1}` (位数 p) 上の誘導自己同型は冪写像 `x ↦ xʳ` で
   `r^q ≡ 1 (mod p)`。BG の `wᵢᵃ ≡ wᵢ^{rᵢ} (mod H_{i+1})` はこれを商で読んだもの。
   すべて既存部品の組み立てで、証明は 8 行。
   ⚠ `characteristic_iterCommutator` を **instance 化**した — 商作用を*述べる*のに要る
   `H_{i+1}.subgroupOf H_i` の正規性が推論で見つかるようにするため。
   (旧メモ) 道具は repo にある:
   **`Isaacs.Ch03.IsAInvariant.quotientMulAutHom`** (+ `_apply_mk'`) が
   `IsAInvariant φ N` (N 正規) から `A →* MulAut (G ⧸ N)` を作る。多数の file で使用実績あり。
   ⚠ ただし要るのは `↥S ⧸ ...` でなく **`↥H_i ⧸ (H_{i+1}.subgroupOf H_i)`** なので、
   先に `IsAInvariant.restrict` で `↥H_i` に降ろしてから適用する 2 段構え。
   位数 p は `card_iterCommutator_eq` から。そこに
   `exists_zpow_eq_of_card_eq_prime` を当てて `r_i` を得る。
4. Step 3 (極大 `S` + `Ω₁(N_P(S))` の (E.15)-(E.16)) ⟹ **E.3(b) 第 1 節**。

## ⚠ 2026-07-20 (8): Step 2 の**仮説が BG より弱いまま来ている**

BG は Step 2 を「`S` を `R` の **A-不変**・指数 p・`R₀` を真に含む部分群とする」で始めるが、

- **`R₀ ⊄ S'` (E.13 第 1 節) と `|S/S'| = p²` (E.7) は、A-不変性も A-作用も一切使わずに
  証明できた**。使ったのは指数 p と `R₀ < S` (第 3 節のみ真部分群性) だけ。
- **A-作用が要るのは第 3 の結論 `|S| ≤ p^q` (E.9)-(E.12) だけ** — `A` の regular 性が
  固有値 1 を禁じるところが本体だから。

⟹ 現状の 2 定理は BG より広く使える。(E.9) 以降を書くときに初めて `S` の A-不変性を
仮説に足す (setup に既にある `act`/`A_regular` と繋ぐ)。

### (E.9)-(E.12) の前提は repo に在る (2026-07-20 実測)

| BG の引用 | repo の所在 |
|---|---|
| **Prop 1.5(d)** (`C_{M/N}(B) = C_M(B)·N/N`, coprime) | `S03g_Thm310Nilpotent.lean:87` |
| **Lemma 4.2(a)** (交換子が中心なら `(xy)^n` 展開) | `S04_SmallRankBasic.lean:180, 193`; 整数冪版は `S04f_Blackburn.lean:997, 1010` |
| 鎖の A-不変性 | `iterCommutator T ⊤ i` は `↥S` で characteristic ⟹ `S` が A-不変なら従う (要形式化) |

⟹ (E.9)-(E.12) は**新しい基盤の構築ではなく、固有値の帳簿付け** (mod p の乗法群での
位数計算 + 上記 2 補題の適用)。ただし A-作用を `↥S` の鎖に降ろす配線が要るので分量は大きい。

## ⭐ 2026-07-20 (9): **(E.12) 完了** — 固有値の漸化式

`RegularOperatorSetup.eigenvalue_step`: `r_{i+1} ≡ r_i · r (mod p)`。BG の 1 行

```
w_{i+1}^{r_{i+1}} ≡ w_{i+1}^a = ⁅w_i,v⁆^a = ⁅w_i^{r_i} u, v^r⁆ ≡ ⁅w_i,v⁆^{r_i r}  (mod H_{i+2})
```

を完全に形式化。cancel は前回の `w_i ∉ H_{i+1}` (BG の 5 語) が効く。

| 新規宣言 | 内容 |
|---|---|
| `commutatorElement_mul_central_left` | `⁅a·c,b⁆ = ⁅a,b⁆` (c 中心) |
| `commutatorElement_zpow_zpow_of_central` | Lemma 4.2(a) 双線形形の**整数冪版** |
| `commutator_zpow_mul_congr` | **(E.12) 1 歩** `⁅x^m·u, v^k⁆ ≡ ⁅x,v⁆^{mk} (mod H_{i+2})` |
| `RegularOperatorSetup.exists_zpow_eq_mod_chain` | (E.9) を BG と同じ**元の合同式**の形に |
| `RegularOperatorSetup.eigenvalue_step` | **(E.12)** |

要点: `chain_map_le_center` を 2 回使う — 剰余 `u ∈ H_{i+1}` は `G/H_{i+2}` で
中心的ゆえ左スロットから落ち、`⁅x,v⁆ ∈ H_{i+1}` も中心的ゆえ Lemma 4.2(a) が
両スロットで効く。⚠ `v` は無制約 (鎖が `S` 全体と bracket するため)。

支持変更: `S04f_Blackburn` の `commutatorElement_zpow_{left,right}_of_central` と
`zmod_eq_of_zpow_eq_of_order_prime` を public 化 (ファイル跨ぎ `private` は規約違反)。

### 残り (E.3(c) までの道)

1. ⬜ **帰納 `r_i ≡ r₀ rⁱ`** — `eigenvalue_step` を `i` について回す。⚠ 同じ `a` を
   全段で使うので、`r`・`w`・`v` を固定して `r_i` を選択関数として取る形が要る。
2. ⬜ **(E.10) を合同式の形に** — `quotient_action_ne_one` (誘導自己同型 ≠ 1) と
   `exists_zpow_eq_mod_chain` の `r_i` を突き合わせて `(r_i : ZMod p) ≠ 1`。
3. ⬜ **算術的終点** — `le_pred_of_forall_mul_pow_ne_one` を `(ZMod p)ˣ` に適用 ⟹
   `n ≤ q-1`。⚠ `ZMod p` の**単位群が巡回**であることを供給する必要
   (`ZMod.instIsCyclicUnits` 等、要実測)。`r₀ rⁱ ≠ 1` が `u₀ uⁱ ≠ 1` に対応。
4. ⬜ **`|S| = p·pⁿ ≤ p^q`** = `card_start_eq_pow_mul` + `sup_centralizer_eq_top` ⟹
   **E.3(c) `card_omega_le`**。

### ファイル分割 (issue 0134)

`AppE_FurtherResults` が 2020 行になったので prefix-split。
現在の 3 層: `AppE_CollectionFormula` (E.1-E.2, 337 行) →
`AppE_FurtherResults` (E.3-E.5, 1719 行) → `AppE_RegularOperator` ((E.9)-(E.12), 552 行)。

## ⭐⭐ 2026-07-20 (10): **E.3(c) 完了 — BG Step 2 が全部閉じた**。AppE sorry 5 → 4

| 新規宣言 | BG 対応 |
|---|---|
| `exists_chain_length` | 鎖 `T = H₀ ⊃ … ⊃ Hₙ = 1` の存在と `|T| = pⁿ` |
| `le_pred_of_forall_zmod_mul_pow_ne_one` | 締めの計数を `(ZMod p)ˣ` に移送 (`n ≤ q−1`) |
| `card_le_pow_card_A` / `card_le_pow` | **Step 2 第 3 節** `|S| ≤ p^q` (rank≥3 / 無条件) |
| `card_omega_le` | **E.3(c)** |
| `exists_zpowers_eq_R₀_subgroupOf` | BG の `v ∈ R₀^#` |

### 発見 3 つ

- **サイズは (E.5) から読む方が安い**: BG の `|S| = |R₀T|` でなく
  `|S| = |T|·|S:T| = pⁿ·p`。指数 `p` は Lemma 5.2 が既に与えている。
- **`|S| ≤ p³` 分岐はまた不要**: `q` は奇素数ゆえ `q ≥ 3`、よって `p³ ≤ p^q`。
  BG の「位数 p³ 以下の p 群の検査」が Step 2 で実際に要ったのは
  `card_quotient_commutator` の 1 箇所だけだった。
- **A-作用が本当に効くのは第 3 節だけ**: 第 1・2 節は A 不変性なしで通っていた
  (2026-07-20 (8) の観察の確定)。

### 配置

E.3(c) の結論は (E.9)-(E.12) 機構に依存するので、宣言を `AppE_FurtherResults` から
`AppE_RegularOperator` へ移設 (名前・namespace 不変、消費者ゼロ)。

### 検証

`card_omega_le` 以外は axiom-clean。`card_omega_le` の `sorryAx` は
`omega_pow_eq_one` (Step 3) の sorried-cite 1 本のみ。
フルビルド 4554 jobs green / AxiomsCheck OK / sorry 総数 15 (非退行)。

## 残り 4 sorry と次の frontier

| 宣言 | 書籍 | 状況 |
|---|---|---|
| `omega_pow_eq_one` | **E.3(b) 第 1 節 = BG Step 3** | ★ 次の根。E.3(b)(c) 3 節すべてがこれを cite |
| `B_fixes_R₀_of_fixes_frattini` | E.3(d) = Step 4 | Schur–Zassenhaus + regular |
| `centralizer_upperCentralSeries_abelian_index_p` | E.4 | E.3 を全部消費 |
| `maximalSubgroups_isTypeI_or_isTypeII` | E.5 | §14 counting + Cor 15.9 |

**次は Step 3** (`omega_pow_eq_one`)。BG 原文 (pdftotext L8062-8110):
「`R₀ × Ω₁(R₁)` を含む A-不変・指数 p の**極大**部分群 `S` を取る ⟹ `S ⊆ Ω₁(R)`。
Step 2 より (E.13) `R₀ ⊄ S'`, `|S| ≤ p^q`, `|S/S'| = p²`。`P = Ω₁(R)`, `T = N_P(S)` と置き、
`S = Ω₁(T)` なら … (E.14)-(E.16) で `T = P` かつ `S = Ω₁(P) = Ω₁(Ω₁(R)) = Ω₁(R)`」。
⟹ Step 2 の 3 結論が**そのまま入力になる**ので、機構はもう揃っている。
要る新規は「極大な A-不変指数 p 部分群の存在」と `Ω₁(N_P(S))` の議論 (Lemma 4.5 を使う)。

## 2026-07-20 (11): Step 3 の足場 + 易しい分岐 (新 leaf `AppE_ExponentP.lean`)

### 足場

| 宣言 | 内容 |
|---|---|
| `seed` | **BG の種 `R₀ × Ω₁(R₁)`** を `Ω₁(C_R(R₀))` として |
| `R₀_le_seed` / `R₀_lt_seed` / `isAInvariant_seed` | 種の性質 |
| `ExpPFamily` / `exists_maximal_expP` | **BG の極大選択** |
| `expPFamily_le_omega` | **`S ⊆ Ω₁(R)`** |
| `expPFamily_pow_eq_one` / `R₀_lt_of_expPFamily` | Step 2 が消費する形への橋 |

⭐ **種を `Ω₁(C_R(R₀))` と綴る理由**: setup は `R₁` に A-不変性を与えていないので
BG の字面 `R₀ × Ω₁(R₁)` では族が空でないことが言えない。`C_R(R₀)` は `R₀` が A-不変
ゆえ A-不変で、アーベル性は Step 2 で既証明。2 つは集合として等しい。

### 易しい分岐

| 宣言 | 内容 |
|---|---|
| `omegaInG` (+ `_eq_map` / `_le` / `mem_`) | 部分群の `Ω_n` を ambient `Subgroup G` に |
| `omegaInG_omega` | **`Ω₁(Ω₁(G)) = Ω₁(G)`** (生成集合が一致、即座) |
| `normalizer_le_normalizer_omegaInG` | **`N_G(H) ≤ N_G(Ω_n(H))`** |
| `eq_omega_of_omegaInG_normalizer_eq` | **`S = Ω₁(N_P(S)) ⟹ S = Ω₁(R)`** |

`T = P` は `↥P` での正規化条件 (Isaacs Thm 1.22) + `Subgroup.subgroupOf_normalizer_eq`。
⚠ この分岐は **A も `R₀`/`R₁` も使わない** — `R` が p 群であることだけ。

### 残り = BG (E.14)-(E.16) の難しい分岐

仮定 `S ≠ Ω₁(T)` (T = N_P(S)) から矛盾を出す。BG 原文 (pdftotext L8080-8110) の筋:

1. **(E.15)** `v ∈ R₀^#` の `S`-共役類 `K` は `|K| = |S : C_S(v)| = |S : C_S(R₀)| = |S|/p²`。
   ⟸ `C_S(R₀) = R₀ × Ω₁(Z(S))` が位数 p² (**Step 2 の (E.4) `centralizer_inf_eq_sup_omega1Center`
   が既にある**)。⚠ ただし (E.4) は `3 ≤ pRank ↥S p` を仮定するので、`|S| ≤ p³` 分岐は
   BG の `C_S(R₀) = S ∩ (R₀ × R₁) = R₀ × Ω₁(R₁)` 経路が要るかもしれない — 着手時に再評価。
2. **(E.16)** `T₁ := N_T(K)` (集合 K の正規化群) とすると `S ≤ T₁` で、`v` の `T`-共役類は
   `|T : T₁|` 個の `S`-共役類の合併。恒等元を含まないので
   `|T:T₁|·|S|/p² ≤ |S| − 1 < |S|` ⟹ **`|T : T₁| < p²`**。
3. **Frattini 変形**: `T₁ = S·(T₁ ∩ R₀R₁) = S·(T₁ ∩ R₁)` ⟹ `T₁/S ≅ (T₁∩R₁)/(T₁∩R₁∩S)`。
   `R₁` cyclic ⟹ **`T₁/S` cyclic**。
4. `T₁/S` は `T/S` の指数 1 or p の巡回部分群 ⟹ **Lemma 4.5** で `|Ω₁(T/S)| ≤ p²`。
5. `|Ω₁(T)/S| ≤ p²` ⟹ `|Ω₁(T)| ≤ p²|S| ≤ p^{q+2}` ⟹ `cl(Ω₁(T)) ≤ q+1 ≤ p−1`
   (Step 1 = `card_A_dvd_half_p_sub_one` で `q ≤ (p−1)/2`、`p ≥ 7`)。
6. **Prop E.2(a)** (`omega_pow_eq_one_of_lowerCentralSeries_eq_bot`、済) ⟹ `Ω₁(Ω₁(T))` は指数 p。
   `Ω₁(Ω₁(T)) = Ω₁(T)` (今回の `omegaInG_omega`) かつ `Ω₁(T) ⊋ S` は A-不変 ⟹ **極大性に矛盾**。

⟹ 必要な新規は主に **(E.15)(E.16) の共役類計数**と **Frattini 変形**。
Lemma 4.5 と Prop E.2 と Step 1 は repo に既にある。

## 2026-07-20 (12): Step 3 難しい分岐 — (E.15) と Frattini 変形

| 新規宣言 | BG 対応 |
|---|---|
| `centralizer_singleton_eq_of_zpowers_eq` | `C(v) = C(⟨v⟩)` |
| `card_centralizer_generator` | `\|C_S(v)\| = \|C_S(R₀)\| = p²` |
| `card_conjClass_generator` | **(E.15)** `p²·\|K\| = \|S\|` |
| `sup_centralizer_eq_sup_inf_R₁` | **Frattini 変形** `S ⊔ C_T(v) = S ⊔ (T ⊓ R₁)` |

### ⭐ 設計上の発見: `T₁ = N_T(K)` は定義に据え替えられる

BG は `T₁` を「`K` の `T` における正規化群」として導入するが、**下流が使うのは
(a) `S ≤ T₁`、(b) `|T:T₁| < p²`、(c) `T₁/S` 巡回 の 3 つだけ**。
Frattini 論法の結論 `T₁ = S·C_{T₁}(v) = S·C_T(v)` を**定義に据える**と:

- Frattini 論法そのものが不要
- 「部分集合の集合への T-作用」(軌道が S-共役類を並べる) を組む必要も消える
- (b) は `|T:C_T(v)| = |T:T₁|·|T₁:C_T(v)|` と `|T₁:C_T(v)| = |S:C_S(v)| = |S|/p²`、
  および `T`-共役類 ⊆ `S \ {1}` から出る

### 残り (この順)

1. ⬜ **`T₁/S` 巡回**: `T ⊓ R₁` は巡回 `R₁` の部分群 ⟹ その `T/S` での像が巡回
   (`isCyclic_of_surjective`)。`S ⊴ T` は `T = N_R(S) ⊓ P` の定義から。
   ⟹ `T₁/S = ((T ⊓ R₁).subgroupOf T).map (mk' (S.subgroupOf T))` として綴るのが軽い
   (第二同型定理の `subgroupOf` 往復を回避)。
2. ⬜ **`|T:T₁| < p²`** = 上の積公式 + `T`-共役類 ⊆ `S \ {1}`。
3. ⬜ **Lemma 4.5** で `|Ω₁(T/S)| ≤ p²` ⟹ `|Ω₁(T)| ≤ p²|S| ≤ p^{q+2}`。
4. ⬜ `cl(Ω₁(T)) ≤ q+1 ≤ p−1` (Step 1 `card_A_dvd_half_p_sub_one` + `p ≥ 7`)
   ⟹ **Prop E.2(a)** で `Ω₁(T)` が指数 p ⟹ 極大性に矛盾 ⟹ **Step 3 完了**。

## 2026-07-20 (13): `T₁/S` 巡回性 — 生成元形で

| 宣言 | 内容 |
|---|---|
| `exists_zpowers_eq_map_of_isCyclic` | 巡回部分群の像は生成元の `zpowers` |
| `isCyclic_inf_R₁` | `T ⊓ R₁` は巡回 |
| `exists_zpowers_eq_map_sup_inf_R₁` | **`T₁/S = ⟨x⟩`** (x は `T ⊓ R₁` の生成元の像) |

⭐ **生成元形にした理由 = 下流の要求**。BG Lemma 4.5(b) は repo に
**`Ch1.S04.card_omega1_le_prime_sq_of_cyclic_index_prime`** として既にあり、
署名は `(hR : IsPGroup p R) (hp_odd : Odd p) {x : R} (hHidx : (Subgroup.zpowers x).index = p)
: Nat.card (Omega R p 1) ≤ p ^ 2` — **生成元とその zpowers の指数**を消費する。

### Step 3 の残り (この順、次セッションはここから)

1. ⬜ **`|T : T₁| ≤ p`**: `|T:C_T(v)| = |T:T₁|·|T₁:C_T(v)|`、`|T₁:C_T(v)| = |S:C_S(v)| = |S|/p²`
   (積公式)、`T`-共役類 ⊆ `S \ {1}` ⟹ `|T:T₁|·|S|/p² ≤ |S|−1` ⟹ `|T:T₁| < p²` ⟹ (p 群ゆえ) ≤ p。
   ⟹ `(zpowers x).index ≤ p` in `T/S`。
2. ⬜ **Lemma 4.5(b) 適用**: `|Ω₁(T/S)| ≤ p²`。⚠ 指数 = 1 の場合 (`T/S` 巡回) は
   `card_omega1_le_prime_sq_of_cyclic_index_prime` が使えない (index = p 固定) ので
   別途「巡回 p 群の `Ω₁` は位数 ≤ p」が要る。
3. ⬜ **`|Ω₁(T)| ≤ p²|S|`**: `S ≤ Ω₁(T)` (S は指数 p) と `Ω₁(T)` の像 ⊆ `Ω₁(T/S)`。
4. ⬜ **`cl(Ω₁(T)) ≤ q+1 ≤ p−1`**: `|Ω₁(T)| ≤ p²·p^q = p^{q+2}` +
   `S04.nilpotencyClass_le_of_card_le_pow` + Step 1 (`card_A_dvd_half_p_sub_one`) で `q ≤ (p−1)/2`、
   `p ≥ 7` (E.3(a) の帰結)。
5. ⬜ **Prop E.2(a)** (`omega_pow_eq_one_of_lowerCentralSeries_eq_bot`、済) ⟹ `Ω₁(Ω₁(T))` 指数 p、
   `omegaInG_omega` で `= Ω₁(T)`、`Ω₁(T)` は A-不変 (T が A-不変ゆえ) で `⊋ S`
   ⟹ **極大性に矛盾** ⟹ Step 3 完了 ⟹ `omega_pow_eq_one` ⟹ **E.3(b) 全体が axiom-clean**。

現状 AppE の sorry = 4 (`omega_pow_eq_one` / E.3(d) / E.4 / E.5)。

## 2026-07-20 (14): (E.16) の準備 — 位数公式と `C_T(v)` の同定

| 宣言 | 内容 |
|---|---|
| `card_sup_centralizer` | **`\|T₁\|·p² = \|S\|·\|C_T(v)\|`** (T₁ = S ⊔ C_T(v)) |
| `centralizer_singleton_subgroupOf` | `C_{↥T}(v) = (T ⊓ C_R(v)).subgroupOf T` |

### (E.16) `|T:T₁| < p²` の証明筋 (次セッションはここから — 部品は全部そろっている)

BG は「`v` の `T`-共役類は `|T:T₁|` 個の `S`-共役類の合併」と言うが、**S-類の融合を
形式化する必要はない**。`T` で軌道-固定化群を 1 回使うだけでよい:

1. `|T-class of v| · |C_T(v)| = |T|` — `MulAction.orbit (ConjAct ↥T) v'` と
   `ConjAct.stabilizer_eq_centralizer` + `centralizer_singleton_subgroupOf` (今回)。
2. `|T| = |T:T₁| · |T₁|` — `Subgroup.card_mul_index` (`T₁.subgroupOf T`)。
3. `|T₁|·p² = |S|·|C_T(v)|` — `card_sup_centralizer` (今回)。
4. 1,2,3 から `p² · |T-class| = |T:T₁| · |S|` (両辺 `|C_T(v)|` で約分)。
5. `T-class ⊆ S \ {1}`: `S ⊴ T` (T ≤ N_R(S)) と `v ∈ S`, `v ≠ 1`。
   ⟹ `|T-class| ≤ |S| − 1`。
6. ⟹ `|T:T₁| · |S| ≤ p²·(|S|−1) < p²·|S|` ⟹ **`|T:T₁| < p²`**。
   p 群なので `|T:T₁| ∈ {1, p}`。

⚠ 5 の Lean 化で少し手間: `ConjAct.smul_def` で `t • v' = t * v' * t⁻¹` に開き、
`Subgroup.mem_normalizer_iff` で `S` 内に留まることを言う。`≠ 1` は共役が単射だから。

## 2026-07-20 (15): (E.16) 完了 + Lemma 4.5(b) への接続

| 宣言 | 内容 |
|---|---|
| `index_sup_centralizer_lt` | **(E.16)** `\|T:T₁\| < p²` |
| `index_map_mk'` | `(H/N).index in G/N = H.index in G` |
| `exists_zpowers_index_lt` | **`∃ x : T/S, (zpowers x).index < p²`** |

⚠ **(E.16) は S-類の融合なしで出た** — `T` で軌道-固定化群を 1 回使い、
`\|K_T\|·\|C_T(v)\| = \|T\|` / `\|T\| = \|T₁\|·\|T:T₁\|` / `\|T₁\|·p² = \|S\|·\|C_T(v)\|`
の 3 本から `\|C_T(v)\|` を約分 ⟹ `p²·\|K_T\| = \|T:T₁\|·\|S\|`。
`K_T ⊊ S` (`S ⊴ T` で中に入り `v ≠ 1` で `1` を外す) から結論。
BG の (E.15)「各 S-類は `\|S\|/p²` 個」はこの経路では未使用。

### 次の一手 = `|Ω₁(T/S)| ≤ p²` (index=1 分岐に注意)

repo の `Ch1.S04.card_omega1_le_prime_sq_of_cyclic_index_prime` は
**index = p ちょうど**を要求する。`exists_zpowers_index_lt` は `< p²` を与えるので、
p 群では index ∈ {1, p}。分岐:

- **index = p**: そのまま 4.5(b)。
- **index = 1**: `T/S = ⟨x⟩` 巡回。このとき `|Ω₁(T/S)| ≤ p` を別途示す。
  ⭐ **道具**: mathlib `IsCyclic.card_pow_eq_one_le` (巡回群で `x^n = 1` の解は高々 n 個)。
  巡回⟹アーベルなので `{g | g^p = 1}` は既に部分群で `Omega G p 1` に一致
  (`Omega` は closure なので `Subgroup.closure_eq` 相当で潰す)。
  ⟹ 一般補題 `card_omega_le_of_isCyclic : IsCyclic G → Nat.card ↥(Omega G p 1) ≤ p`
  を書くのが素直 (App.E leaf でよい; 2 消費者目が出たら `GroupTheory/OmegaSubgroup.lean` へ)。

### その後 (Step 3 の締め)

1. `|Ω₁(T)/S| ≤ |Ω₁(T/S)| ≤ p²` — `S ≤ Ω₁(T)` (S は指数 p) と像の包含。
2. `|Ω₁(T)| ≤ p²·|S| ≤ p²·p^q = p^{q+2}` — `card_le_pow` (Step 2 第 3 節、済)。
3. `cl(Ω₁(T)) ≤ q+1 ≤ p−1` — `S04.nilpotencyClass_le_of_card_le_pow` +
   Step 1 `card_A_dvd_half_p_sub_one` (`q ≤ (p−1)/2`) + `p ≥ 7`。
4. **Prop E.2(a)** `omega_pow_eq_one_of_lowerCentralSeries_eq_bot` (済) ⟹ `Ω₁(Ω₁(T))` 指数 p、
   `omegaInG_omega` で `= Ω₁(T)`、`Ω₁(T)` は A-不変 (T = N_P(S) が A-不変) かつ `⊋ S`
   ⟹ **極大性に矛盾** ⟹ Step 3 完了。

## ⚠⚠ 2026-07-20 (16): 最終組み立てで**設計の食い違いを発見** — `3 ≤ pRank ↥S p` が Step 3 では手に入らない

Step 3 の最終組み立てに入ったところで、次の依存が問題になった:

`index_sup_centralizer_lt` (E.16) → `card_sup_centralizer` → **Step 2 の (E.4)
`centralizer_inf_eq_sup_omega1Center`** → **`3 ≤ pRank ↥S p` を要求**。

しかし Step 3 の `S` (極大な A-不変指数 p 部分群) について `r(S) ≥ 3` は**与えられていない**。

### BG は別ルートで `|C_S(R₀)| = p²` を出している

BG (E.14): 「Clearly `S ⊇ Ω₁(Z(R))` and `C_S(R₀) = S ∩ (R₀ × R₁) = R₀ × Ω₁(R₁)`」。
つまり **rank でなく「種を含むこと」から**出している:

- `S ⊓ C_R(R₀) ⊇ seed = Ω₁(C_R(R₀))` — 種が `S` に入っているから
- `S ⊓ C_R(R₀) ⊆ seed` — `S` は指数 p なので `S ⊓ C_R(R₀)` の元は `C_R(R₀)` 内で `x^p = 1`
- ⟹ **`S ⊓ C_R(R₀) = seed` (ちょうど)**
- `|seed| = |Ω₁(R₀ × R₁)| = |R₀| · |Ω₁(R₁)| = p · p = p²`
  (`R₁` は非自明巡回 p 群なので `|Ω₁(R₁)| = p`)

### 対応方針 (次セッション)

**`card_sup_centralizer` と `index_sup_centralizer_lt` の仮説を
`(hexp, hS3 : 3 ≤ pRank ↥S p)` から
`hp2 : Nat.card ↥(S ⊓ Subgroup.centralizer (hyp.R₀ : Set R)) = p ^ 2` に置き換える**
(パラメータ化)。供給元は 2 つ:

- Step 2 の文脈: (E.4) `centralizer_inf_eq_sup_omega1Center` (rank ≥ 3 あり)
- Step 3 の文脈: 新補題 `inf_centralizer_eq_seed` + `card_seed = p²` (rank 不要)

⟹ 書くべき新規:
1. `RegularOperatorSetup.inf_centralizer_eq_seed`:
   `hyp.seed ≤ S` かつ `S` 指数 p ⟹ `S ⊓ C_R(R₀) = hyp.seed`。
2. `RegularOperatorSetup.card_seed`: `|seed| = p²`。
   ⟸ `seed = Ω₁(C_R(R₀))`、`C_R(R₀) = R₀ ⊔ R₁` アーベル、`|Ω₁(R₁)| = p`
   (`GroupTheory.card_omega1OfAbelian_eq_of_isCyclic` = `OmegaSubgroup.lean:526` を実測確認)。
3. 上記 2 定理の仮説パラメータ化 (呼び出し側 = Step 2 の消費点も更新)。

⭐ **これは特殊化債務の返済でもある** — 現状の (E.16) は BG より強い仮説
(`rank ≥ 3`) を要求しており、パラメータ化すれば BG どおりの一般性になる。

## 2026-07-20 (17): (E.14) 完了 + ⭐ パラメータ化は `≤ p²` で足りる

`inf_centralizer_eq_seed`: `S ⊓ C_R(R₀) = hyp.seed` (種を含む指数 p の `S` について)。
⟹ `|C_S(R₀)| = |seed|` なので、rank≥3 を経由せずに済む。

### ⭐ 発見: 等式でなく **`|C_S(R₀)| ≤ p²` で十分**

`index_sup_centralizer_lt` の算術を追うと、`|C_S(v)| = c` を一般の `c` にしても

- `|T₁|·c = |S|·|C_T(v)|` (積公式)
- `c·|K_T| = |T:T₁|·|S|` (約分後)
- `|K_T| < |S|` ⟹ `|T:T₁| < c`

⟹ **`c ≤ p²` なら `|T:T₁| < p²` が出る**。等式は要らない。
⟹ パラメータは `hp2 : Nat.card ↥(S ⊓ C_R(R₀)) ≤ p ^ 2` でよい (供給が楽になる)。

### 残タスク (次セッション)

1. ⬜ **`card_seed_le : |seed| ≤ p²`**。候補ルート 2 つ:
   - (a) `seed` は elementary abelian で `C_R(R₀)` 内、`pRank_centralizer_R₀_le_two` を使う。
     要: 「pRank ≤ n の群の elementary abelian 部分群は位数 ≤ p^n」の橋
     (`pRank` の定義は `⨆ A, Nat.log p |A|` = `GroupTheory/PRank.lean:423`)。
   - (b) `seed ⊓ R₁ ≤ Ω₁(R₁)` (位数 ≤ p、cyclic) と `|C_R(R₀) : R₁| = p`
     (`card_centralizer_R₀`) から積公式で `|seed| ≤ p·p`。
     ⚠ `GroupTheory.pRank_le_two_of_isCyclic_of_index_le_prime` (issue 9401 で書いた)
     の証明が同型なので、そこから部品を切り出せる可能性が高い — 先に実測すること。
2. ⬜ `card_sup_centralizer` / `index_sup_centralizer_lt` の仮説を
   `(hexp, hS3)` → `hp2 : |S ⊓ C_R(R₀)| ≤ p²` にパラメータ化 (Step 2 の呼び出し側も更新)。
3. ⬜ Step 3 最終組み立て (`Ω₁(T) ∈ ExpPFamily` → 極大性 → `omega_pow_eq_one`)。

## 2026-07-20 (18): rank≥3 依存の解消**完了** — Step 3 は最終組み立て 1 手のみ

| 宣言 | 内容 |
|---|---|
| `GroupTheory.card_le_prime_sq_of_isCyclic_of_index_le_prime` | pRank 補題から**位数評価を切り出し** |
| `RegularOperatorSetup.card_seed_le` | **`\|seed\| ≤ p²`** |
| (refactor) `card_sup_centralizer` | `p²` → `\|S ⊓ C_R(R₀)\|`; **仮説 3 つが不要に** |
| (refactor) `index_sup_centralizer_lt` / `exists_zpowers_index_lt` | 仮説を `hp2 : \|S ⊓ C_R(R₀)\| ≤ p²` に |

検証: フルビルド 4558 jobs green / AxiomsCheck 3540 件 OK / sorry 15 (非退行)。

### 残り = Step 3 最終組み立て 1 手

`RegularOperatorSetup.eq_omega_of_maximal (hS : ExpPFamily S) (hmax : …) : S = Omega R p 1`:

```
P := Omega R p 1;  T := N_R(S) ⊓ P
hSP  := expPFamily_le_omega hS            -- S ≤ P
hST  := le_inf Subgroup.le_normalizer hSP -- S ≤ T
hTN  := inf_le_left                       -- T ≤ N_R(S)
hn   := (normal_subgroupOf_iff_le_normalizer hST).mpr hTN
hSW  : S ≤ omegaInG T p 1                 -- S は指数 p
refine eq_omega_of_omegaInG_normalizer_eq (hmax _ ⟨?_, ?_, ?_⟩ hSW)
  (a) A-不変: isAInvariant_omegaInG (hS.1.normalizer.inf (.of_characteristic _)) p 1
  (b) 指数 p: pow_eq_one_of_card_omegaInG_le で、hcard を
      card_omegaInG_le_mul hST (hS.2.1)                       -- |Ω₁(T)| ≤ |Ω₁(T/S)|·|S|
      × card_omega_le_prime_sq_of_index_lt (IsPGroup の商) hyp.p_odd
          (exists_zpowers_index_lt … の x)                    -- |Ω₁(T/S)| ≤ p²
      × hyp.card_le_pow (R₀_lt_of_expPFamily hS).le (expPFamily_pow_eq_one hS) hS.1
                                                              -- |S| ≤ p^q
      から `≤ p²·p^q = p^{q+2}` として組む
  (c) seed ≤ Ω₁(T): hS.2.2.trans hSW
```
`exists_zpowers_index_lt` の `hp2` は `inf_centralizer_eq_seed hS.2.2 hS.2.1 ▸ card_seed_le`、
`v` は `exists_zpowers_eq_R₀` から (`hvS` は `hR₀S (hv ▸ mem_zpowers v)`)。

⟹ これが通れば `omega_pow_eq_one` (= E.3(b) 第 1 節) が閉じ、
**E.3(b) 第 1〜3 節 + E.3(c) が丸ごと axiom-clean**。AppE sorry 4 → 3。

## ⭐⭐⭐ 2026-07-20 (19): **Step 3 完了 — BG Thm E.3 (a)(b)(c) が全て axiom-clean**

`eq_omega_of_maximal` → `omega_pow_eq_one` (E.3(b) 第 1 節)。
乗っていた E.3(b) 第 2・3 節と E.3(c) も sorried-cite が外れて完全証明に。
**AppE sorry 4 → 3、リポジトリ全体 15 → 14。**

### ⭐ 発見: BG の「矛盾」は矛盾ではなく**閉包性**だった

BG は Step 3 後半を「`S ≠ Ω₁(T)` と仮定 → (E.14)-(E.16) → `Ω₁(T)` は指数 p
→ 極大性に矛盾」と書くが、形式化すると (E.14)-(E.16) が実際に示しているのは

> 族 `ExpPFamily` が写像 `S ↦ Ω₁(N_P(S))` で**閉じている**

こと。極大性から直ちに `Ω₁(N_P(S)) = S` が出るので**背理法の仮定は要らず**、
易しい分岐 (`eq_omega_of_omegaInG_normalizer_eq`) にそのまま渡せる。

### 配置

E.3(b) 全 3 節 + E.3(c) の宣言を `AppE_ExponentP.lean` に集約
(証明が Step 3 に依存するため)。上流 2 leaf にはポインタコメント。名前・namespace 不変。

### 検証

5 宣言すべて axiom-clean (sorryAx なし) / フルビルド 4558 jobs green /
AxiomsCheck 3540 件 OK / sorry 15 → 14。

## 残り 3 sorry (AppE)

| 宣言 | 書籍 | 次の着手対象 |
|---|---|---|
| `B_fixes_R₀_of_fixes_frattini` | **E.3(d) = BG Step 4** | ★ 次。Step 2/3 の結論を全部使える |
| `centralizer_upperCentralSeries_abelian_index_p` | E.4 | E.3 を全部消費 |
| `maximalSubgroups_isTypeI_or_isTypeII` | E.5 | §14 counting + Cor 15.9 |

### Step 4 (E.3(d)) の筋 — BG 原文 (pdftotext L8112-8140)

`S = Ω₁(R)`、`G = S ⋊ B`。(b) より `|S/S'| = p²`, `|S'| = |S|/p²`。
`Φ(S) = S'` (S は指数 p)。`B` が `R₀S'` を固定すると仮定:
1. `v ∈ R₀^#` の `S`-共役類は `vS'` に含まれ、(E.15) より `|S|/p²` 個
   ⟹ **`= vS'` ちょうど**。`v², …, v^{p−1}` も同様。
   ⟹ `R₀S' − S'` の任意の元は `R₀^#` の元に共役。
2. ⟹ 各 `β ∈ B` で `R₀^β = R₀^x` (∃x ∈ S) ⟹ Frattini 変形で `SB = S·N_G(R₀)`。
3. Schur–Zassenhaus で `N_G(R₀)` は `N_G(R₀) ∩ S` の補群 `B*` を含み `B* = B^y` (y ∈ S)。
⟹ (E.15) が**ここで効く** (Step 2 では積公式に置き換えられて未使用だった)。

## 2026-07-20 (20): Step 4 (E.3(d)) の BG 原文を完全に起こした (pdftotext L8112-8150)

> **Step 4.** Part (d) is valid.
> `S = Ω₁(R)`、`G = S ⋊ B`。(b) より **(E.17)** `|S/S'| = p²`, `|S'| = |S|/p²`。
> `S` は指数 p なので `Φ(S) = S'`。`B` が `R₀S'` を固定すると仮定する。
> `v ∈ R₀^#` とすると各 `x ∈ S` で `x⁻¹vx ≡ v (mod S')` なので、`v` の `S`-共役類は
> `vS'` に含まれる。**(E.15)** よりそれは `|S|/p²` 個、(E.17) より `|vS'| = |S'| = |S|/p²`
> ⟹ **共役類 = `vS'` ちょうど**。`v², …, v^{p−1}` も同様。
> ⟹ **`R₀S' − S'` の任意の元は `R₀^#` の元に共役**。
> `B` が `R₀S'` を固定するので、各 `β ∈ B` で `R₀^β = R₀^x` (∃`x ∈ S`)。
> Frattini 変形で **`SB = S·N_G(R₀)`**。Schur–Zassenhaus で `N_G(R₀)` は
> `N_G(R₀) ∩ S` の補群 `B*` を含み、`B* = B^y` (∃`y ∈ S`)。⟹ `B` は `R₀^{y⁻¹}` を正規化。
> すると `A` は `R₀` と `R₀^y` を正規化するので、`a ∈ A` で `(y^a)⁻¹y ∈ N_S(R₀)`、
> つまり `y^a N_S(R₀) = y N_S(R₀)` — `A` は剰余類 `y N_S(R₀)` を固定する。
> `|A| = q` に対し `|y N_S(R₀)| = |N_S(R₀)|` は p 冪ゆえ `q` で割れない
> ⟹ **`A` は `y N_S(R₀)` の元 `z` を固定**。`A` は `R` に regular に作用するので `z = 1`
> ⟹ `1 ∈ y N_S(R₀)` ⟹ `y ∈ N_S(R₀)` ⟹ `R₀^y = R₀`。∎

### ⭐ ここで (E.15) が初めて効く

Step 2 では (E.15)「`v` の `S`-共役類は `|S|/p²` 個」を積公式で迂回したが、
Step 4 では **`vS'` と個数が一致することを言うため**に必要 (包含 + 同数 ⟹ 一致)。

### 必要な新規インフラ

1. ⬜ `Φ(S) = S'` (S 指数 p) — `frattiniInG` と `Agemo`。repo の
   `GroupTheory/OmegaSubgroup.lean` に `Agemo` があるので `Φ = S'·℧₁(S)` 経由。
2. ⬜ **`G = S ⋊ B`** の構成 — setup は `act : B →* MulAut R` なので
   `SemidirectProduct` が使える (mathlib)。⚠ 本 leaf で初出。
3. ⬜ Frattini 変形 (Step 3 の `sup_centralizer_eq_sup_inf_R₁` と同型の論法だが、
   今度は `G` の中で `N_G(R₀)` について)。
4. ⬜ **Schur–Zassenhaus** — mathlib `SchurZassenhaus` / repo に既存か要実測。
5. ⬜ 剰余類上の coprime 固定点 (`|A| = q` と p 冪の剰余類 ⟹ 固定点あり) —
   repo の `Isaacs.Ch03`/`Ch04` の coprime 作用補題に該当があるか要実測。

⟹ Step 4 は E.3(a)(b)(c) と違い **`G = S ⋊ B` という新しい舞台**を組む必要がある。
着手時はまず 2 (semidirect product の配線) を単独で通すのが安全。

## 2026-07-20 (21): Step 4 の前提を repo 内で実測 — **最難関の Schur–Zassenhaus は在る**

| 必要なもの | repo での所在 (実測) |
|---|---|
| **Schur–Zassenhaus 存在** | mathlib `Subgroup.exists_right_complement'_of_coprime` |
| **Schur–Zassenhaus 共役** | **`OddOrder/Mathlib/SchurZassenhausConj.lean:1292`** `Subgroup.IsComplement'.exists_conj_of_coprime` (mathlib に無いので repo が補完済) |
| `S' ≤ Φ(S)` | `GroupTheory.IsPGroup.commutator_sup_pow_closure_le_frattini` (FrattiniPGroup.lean:212) |
| `Φ(S) ≤ S'` (指数 p) | 直接の補題は無い。`S/S'` は指数 p のアーベル ⟹ elementary abelian ⟹ `frattini_eq_bot_iff_isElementaryAbelian` (S01_Solvable.lean:55) で `Φ(S/S') = ⊥` ⟹ 「`Φ(G/N) = 1 ⟹ Φ(G) ≤ N`」で結論 (この橋は要新規、数行) |
| `R/Φ(R)` elementary abelian | `GroupTheory.IsPGroup.quotient_frattini_isElementaryAbelian` (:162) |
| 半直積 | mathlib `SemidirectProduct` (本 leaf で初出) |
| coprime 固定点 | `Isaacs.Ch03` に coprime 作用群 (3.23/3.24) あり。剰余類版は要確認 |

⟹ **Step 4 の最難関 (SZ 共役) が既に repo にある**ので、残りは
(i) `Φ(S) = S'`、(ii) 半直積の配線、(iii) Frattini 変形、(iv) coprime 固定点、の 4 件。
(i) が最も軽いので着手はそこから。
