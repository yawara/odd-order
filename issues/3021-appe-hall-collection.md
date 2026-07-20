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
