# BG §4 (p-Groups of Small Rank) 実装計画 — 2026-05-30

> **生成**: `bg-s04-design` workflow (run wf_39c356b8-eb2, 6 agent / 581k tok / 42min; bg-mmd agent 1本が StructuredOutput 失敗、gorenstein-blackburn agent が §4 補題チェーンを代替取得)。
> **最重要**: Blackburn 4.16 は **BG が §4 内で完全自前展開** (Gorenstein/Isaacs にフル分類なし)。形式化対象 = BG §4 補題チェーン (Prop 4.3→4.5→4.8→4.11 Huppert→4.12→4.13-15→4.16)。
> **v1 = Wave 0 (PRank 性質/SCN₃/Prop 4.4a) + Lem 4.7** で §5/§7/§10 の §4 依存が解ける (Thm 4.16 フル分類は v2、設計先行が要る)。**Lem 4.17 は 0016 (Thm 1.13 = thompson_critical_omega) を直接使う → 最速**。
> 真のゲート = 「性質ゼロ問題」(PRank/SCN/IsMetacyclic/IsExtraspecial は def のみ)。
> 着手 (2026-05-30): v1 自律実装 workflow を起動 (Thm 4.16/Huppert は scaffold trap リスクで除外、設計先行)。

# BG §4 "p-Groups of Small Rank" — 実装計画 (統合)

読み手: Lean 形式化主導の数学者。出典: `references/bg/local-analysis.mmd` L1359-1788 (printed pp.33-43)、既存 `notes/bg/s04_pgroups_small_rank.md`。本計画は 4 並列調査 + 私の repo 再検証に基づく。

## 0. エグゼクティブサマリ (最重要結論を先に)

1. **Blackburn 4.16 は Gorenstein にも Isaacs にもフル分類が無い。BG が §4 内で完全自前展開する**(Gorenstein は mmd L4181 で "we shall not present his full results here" と明言)。よって**形式化対象は「分類定理」ではなく BG §4 の自己完結補題チェーン**。これは形式化に好都合 (外部巨大定理の引き写しが不要)。
2. **ルート決定**: §4 は **(I) Isaacs 既存資産 + (II) BG 自前 inline + (III) Gorenstein 行間補完 の 3 層**。CLAUDE.md の "Isaacs 優先" は §4 の rank 理論本体には**適用できない** (Isaacs に rank/SCN/Huppert/Blackburn が無い)。ただし**下層の道具 4 件は Isaacs で完全に賄える**(§2 参照)。
3. **真のゲートは概念 def ではなく性質ゼロ問題**。`IsExtraspecial/IsMetacyclic/IsSCN/pRank/Omega/IsElementaryAbelian` は**全て def + 最小 projection だけ存在**。§4 を着手する前の最初の山は **PRank/SCN の性質補強**(現状 lemma 数ゼロ)。
4. **good news (調査が未確認だった点を私が確認)**: **Isaacs Ch04 §4D は sorry-free で完成済**。`isaacs_thm_4_36` (一般 p-群版、Baer trick 込み) も `actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p` (Cor 4.35) も存在。s04 ノートが "HARD GATE" と書いた Lem 4.5(a) 前提は**既に開いている**。
5. **誇張しない gap**: (a) Blackburn 4.16 本体 (帰納法 + GL(2,p) 合同論法 + central product 構成) が最難、(b) Huppert Prop 4.11/Thm 4.12 がその次、(c) `pRank` の 2 形 (elem-ab log|·| vs abelian m(Ω₁)) の橋・全素数 `rank G` 未定義、(d) central product と exponent-p extraspecial M(p,r) が repo 完全不在。

---

## 1. §4 全結果リスト + Lean 化方針 (型レベル)

BG §4 は **20 結果** (Lem/Prop/Thm/Cor 4.1-4.20)。s04 ノート表 (L42-61) で全件確認済。以下、各 statement の **Lean 型レベル方針**と **ルート** (I=Isaacs / B=BG自前 / G=Gorenstein行間 / repo=既存補強)。

形式化先: 新規 `OddOrder/BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean` (未作成)。shared module 拡張 (`PRank.lean`/`SCN.lean`/`IsMetacyclic.lean`/`IsExtraspecial.lean`/`OmegaSubgroup.lean` + 新規 `CentralProduct.lean`) は `OddOrder/GroupTheory/` 配下。

| # | 種別 | statement | Lean 型方針 | ルート |
|---|---|---|---|---|
| 4.1 | Lem | `G/Z(G)` cyclic ⇒ `G` abelian | mathlib `commutative_of_cyclic_center_quotient` 系で済む見込み(要確認)。無ければ短い自前 | mathlib/B |
| 4.2 | Lem | `[x,y]∈Z ⇒ [xⁿ,y]=[x,y]ⁿ`, `(xy)ⁿ` 二項展開 | **repo 既存**: `mul_pow_eq_commutator_pow_mul_of_class_le_two` (CriticalSubgroup.lean:655) を因子並べ替えで。`[xⁿ,y]=[x,y]ⁿ` は mathlib commutator API で短く | repo |
| 4.3 | Prop | p odd, cl≤2 (or p>3,cl≤3) ⇒ (a) Ω₁(R) exp 1or p, (b) R'⊆Ω₁ ⇒ x↦xᵖ 準同型 | **(a) cl≤2 は repo `Omega.exponent_eq_of_class_le_two` (L755) で完了**。`cl≤3,p>3` 分岐は新規 (Hall collection、mmd L1410-1472 の式変形を移植)。regular p-group 理論は**不要** | repo + B |
| 4.4 | Prop | (a) `SCN(R)=maximal abelian normal`, (b) R Syl_p ⇒ `C_G(A)=A×H` (H p′) | (a) `IsSCN` ↔ `centralizer_eq_self_of_maximal_abelian_normal` (CriticalSubgroup.lean:166、一方向済) + 逆方向 + 集合等号。(b) は **Isaacs Thm 7.6.5 = repo Ch07 要 audit** | repo/I |
| 4.5 | Lem | p odd noncyclic ⇒ (a) ∃ normal `E_p²`⊴R, (b) cyclic index p ⇒ Ω₁≅E_p², (c) Ω₁(Z₂(R)) noncyclic exp p | (a) `exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_ne` (ElementaryAbelian.lean:406) + normalize (`exists_mem_omega1_center_of_normal_ne_bot`) + **Isaacs 4.36**。(b) `isElementaryAbelian_card_prime_sq_of_card_le_prime_sq_of_not_isCyclic` (L329)。(c) 新規 | repo+I / G(5.4.3) |
| 4.6 | Prop | normal noncyclic S⊴R ⇒ S 内に normal E_p²⊴R | 4.5 + BG Lem 1.22 を組む | B |
| 4.7 | Lem | `SCN₃(R)=∅ ⟺ r(R)≤2` | **SCN₃ 述語が SCN.lean 未実装** + `pRank` 性質が前提。`⇒` (r≤2⇒SCN₃=∅) は自明方向、`⇐` は Gorenstein 5.4.15 非自明部 | G(5.4.15) + repo |
| 4.8 | Prop | r(R)≤2 ⇒ (a) exp p⇒|R|≤p³, (b) p>3⇒Ω₁ exp 1or p | 4.5+4.3+帰納法。「maximal sub は normal」は mathlib `NormalizerCondition.normal_of_coatom` | B |
| 4.9 | Lem | p>3, `|Ω₁(R)|≤p²` ⇒ 商でも `|Ω₁(R/T)|≤p²` | `|R|` 帰納、quotient tower | B |
| 4.10 | Lem | p odd metacyclic noncyclic ⇒ Ω₁≅E_p² | 4.5(b) 経由。`omega1OfAbelian` + ElementaryAbelian | B(via 4.5) |
| 4.11 | **Prop (Huppert)** | p>3, `|Ω₁(R)|≤p²` ⇒ R metacyclic | **BG 自前再証明** (Huppert Satz III.11.6、帰納法、mmd L1556-1586)。`IsMetacyclic` def 済。**§4 第 2 の山** | B |
| 4.12 | **Thm (Huppert)** | metacyclic + p′-op A, `[R,A]=R` ⇒ (a) R abelian, (b)(c) Ω₁ 構造 | BG 自前 (帰納 + Maschke)。coprime action は repo `CoprimeAction.lean`/BG S01 | B + repo |
| 4.13 | Lem | `SCN₃=∅`, `q∤p`, `q∣|Aut R|` ⇒ `q∣(p²-1)`, `q<p` | Gorenstein 5.4.15 + mathlib `Matrix.card_GL_field` (n=2)。Aut↔GL 橋が gap | G + mathlib |
| 4.14 | Lem | (cont.) `q∣½(p±1)` | 初等 (`p²-1=4·½(p-1)·½(p+1)`) | B |
| 4.15 | Lem | S extraspecial, `[S,R]⊆S'` ⇒ `R=SC_R(S)` | Gorenstein Lem 5.4.6。`IsExtraspecial` 活用 | G(5.4.6)/B |
| 4.16 | **Thm (Blackburn)** | p odd, r(R)≤2, `[R,A]=R`, `|A|` odd ⇒ **p>3** かつ R は (1) abelian or (2) `R₁∘R₂` (R₁ exp-p extraspecial 位数p³, R₂ cyclic, `Ω₁(R₂)=R₁'`) | **§4 最難**。4.3-4.15 を全部組む。**central product と exp-p extraspecial M(p,r) が新規**。GL(2,p) 合同 (`j²≡1 mod p` 矛盾) は新規計算 | B (全自前) |
| 4.17 | Lem | A solvable p′-op, r(R)≤2, `|A|` odd ⇒ `A'` は p-群 | **repo `thompson_critical_omega` (Thm 1.13、完成済) を直接使用** (mmd L1712)。**最も早く書ける** | repo (Thm 1.13) |
| 4.18 | **Thm** | G solvable odd, `r_p(G)≤2` ⇒ (a) p 最大素因子, (b) normal p-complement, (c)(d)(e) 構造 | 4.17+4.7+4.16 + 導来列。**Isaacs Ch.6 Fitting (Thm 6.16) 依存** (Ch06 状態要確認) | B + I(Ch06) |
| 4.19 | Cor | `G*⊴G`, `r_p(G*)≤2` ⇒ G' が p-chief factor を中心化 | 4.18+4.17 + chief series | B |
| 4.20 | **Thm** | `r(G)≤2` or `r(F(G))≤2` ⇒ (a) G' nilpotent, (b) `T⊴S⊆S'⇒T⊴G`, (c) characteristic Sylow series | 4.19+BG Prop 1.2+4.18 + Sylow 帰納。**§7-§16 の骨格** | B + repo |

**型レベル注意点 (3 件、load-bearing)**:

- **`r(R)≤2` の述語**: 単一素数なら `pRank R p ≤ 2`。但し BG `r(R)=max_q r_q(R)` は**全素数の sup**で、`pRank` は単一素数のみ。**全素数版 `rank G` が repo 未定義**。Thm 4.18/4.20 は `r_p`(単一)で書ける箇所が多いが、4.20 の `r(G)≤2` は全素数版が要る。
- **`pRank` の 2 形不一致**: repo `pRank = ⨆_{elem-ab A} log_p|A|`、BG `r_q = max_{abelian A} m(A)` (m(A)=Ω₁(A) の生成元数)。elem-ab では値が一致するが、**Lem 4.7 を述べるには両形の橋補題が必要**。
- **central product の表現**: Thm 4.16(2) の `R=R₁∘R₂`。repo・mathlib とも不在。設計案は §4 で後述 (`R=R₁R₂ ∧ ⁅R₁,R₂⁆=1 ∧ R₁∩R₂=Z(R₁)` の `Prop` 述語が最小)。

---

## 2. 依存 DAG (§4 内 + 外部依存)

```
外部依存 (✅=完成/sorry-free, ❓=要確認, 🆕=未実装):
┌─────────────────────────────────────────────────────────────────────┐
│ Isaacs Ch04 §4D ✅ (sorry-free, 私が確認):                            │
│   isaacs_thm_4_36 ✅ (一般 p-群, Baer)  ── Lem 4.5(a) 前提            │
│   actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p ✅(Cor4.35)│
│   Isaacs Thm 4.8 ✅ (cl≤2, Ω₁ exp p)    ── Prop 4.3(a) cl≤2          │
│ Isaacs Ch07 ThompsonSubgroup ❓          ── Prop 4.4(b)=Thm 7.6.5     │
│ Isaacs Ch06 FrobeniusActions ❓          ── Thm 4.18=Fitting Thm 6.16 │
│ BG §1 Thm 1.13 ✅ (issue 0016, thompson_critical_omega) ── Lem 4.17  │
│ BG §1 Lem 1.22 ❓, Prop 1.2 ❓, Prop 1.6 (CoprimeAction) ❓           │
│ Gorenstein 5.4.15 行間 ── Lem 4.7(⇐), Lem 4.13 │ 5.4.6 ── Lem 4.15  │
│ repo GroupTheory: CriticalSubgroup ✅ / ElementaryAbelian ✅ /         │
│   Omega ✅(def) / PRank 🆕(性質ゼロ) / SCN 🆕(SCN₃ 不在) /            │
│   IsMetacyclic 🆕(性質ゼロ) / IsExtraspecial 🆕(def のみ) /            │
│   CentralProduct 🆕(完全不在) / CoprimeAction ❓                       │
└─────────────────────────────────────────────────────────────────────┘

§4 内 DAG (上流→下流):

  [pRank 性質補強] ──┐
  [SCN₃ 定義]    ──┴──► Lem 4.7 ──► Lem 4.13 ──► Lem 4.14 ──┐
                                       (Gorenstein 5.4.15)      │
                                                                │
  Lem 4.2 ──► Prop 4.3 ──┐                                     │
  (repo)      (repo+B)    │                                     │
                          ├──► Prop 4.8 ──┐                     │
  Lem 4.5 ────────────────┤   (B)         │                     │
  (repo+I) ──► Prop 4.4   │               │                     │
            └─► Lem 4.6 ──┘               ├──► Prop 4.11 ──► Thm 4.12 ──┐
                  │                        │     (Huppert,B)   (Huppert,B)│
                  └─► (Lem 4.7 へ)         │                              │
                                Lem 4.9 ───┘                              │
  Lem 4.10 ◄─ Lem 4.5(b)                                                  │
     │                                                                    │
     └──► Thm 4.12 へ                                                     │
  Lem 4.15 (Gorenstein 5.4.6, IsExtraspecial) ───────────────────────────┤
                                                                          ▼
  ╔══════════════════════════════════════════════════════════════════════╗
  ║  Thm 4.16 (Blackburn) ◄── {4.3,4.4,4.5,4.7,4.8,4.9,4.11,4.12,4.13,    ║
  ║                            4.14,4.15} + central product + exp-p ES    ║
  ╚══════════════════════════════════════════════════════════════════════╝
                          │
  Lem 4.17 ◄── Thm 1.13 (repo, 独立に早期可)
     │
     ▼
  Thm 4.18 ◄── {4.17, 4.7, 4.16, Isaacs Ch06 Fitting} ──► Cor 4.19 ──► Thm 4.20
                                                              │           │
                                                              └───────────┴──► §5,§7-§16
```

**クリティカルパス**: `[pRank/SCN₃ 補強] → 4.5 → 4.8/4.11 → 4.12 → 4.16`。Thm 4.16 が単一最大ボトルネック。Lem 4.17→4.18→4.20 は 4.16 後に直列。

---

## 3. ルート決定: Blackburn 4.16 を Gorenstein / Isaacs / 自前 のどれで

**決定: Thm 4.16 本体は「BG §4 自前 (B)」で形式化する。Gorenstein 原文も Isaacs も引かない。**

**根拠 (3 点、いずれも 1 次資料確認済)**:

1. **Isaacs にフル分類が無い** (調査 2 が grep 確認: Isaacs 本文に 3-level theorem 0 件、rank は abelian 限定 mmd L3729)。よって CLAUDE.md "Isaacs 優先" の対象外。Isaacs が供給するのは下層 4 件 (Thm 4.8 / 4.36 / 10.13 / 6.11) のみ。
2. **Gorenstein にもフル分類が無い** (調査 1 が mmd L4181 で確認: "we shall not present his full results here")。Gorenstein §5.4 が持つのは depth 用語 + Thm 5.4.15 (= Lem 4.7/4.13 の出典) で、**4.16 そのものではない**。CLAUDE.md の Gorenstein 方針 ("BG が `G, Thm X.Y` として本体を省略する箇所のみ参照") は、**BG が 4.16 を省略していない**ので発動しない。
3. **BG が 4.16 を完全自前展開** (mmd L1638-1704 全文確認)。証明は `|R|` 帰納で `|Ω₁(R)|≤p²` (→Prop 4.11 metacyclic) / `>p²` (→exp-p extraspecial S=Ω₁(R)、C=C_R(S) cyclic、`R=SC` or GL(2,p) 矛盾) に場合分け。**全ステップが §4 内の 4.3-4.15 に閉じている**。

**部分的に Gorenstein 行間補完が要る 2 箇所** (これは CLAUDE.md 準拠で OK):
- **Lem 4.7 の `⇐` 方向** (`SCN₃=∅ ⇒ r≤2`) = Gorenstein 5.4.15 非自明部。**ただし Thm 4.16 本体は `⇒` (自明方向) しか使わない**。`⇐` が実際に要るのは下流 Thm 4.18/4.20 (要精査)。
- **Lem 4.13** (Aut order 制約) と **Lem 4.15** (Lem 5.4.6) = Gorenstein 引用。4.13 の核は Prop 4.8 の交換子計算とほぼ重複するので BG 自前再証明も可能 (調査 1 の見立て)。4.15 は extraspecial commutator で短い。

**結論**: 4.16 は **B (自前)**。Gorenstein 参照は 4.7(⇐)/4.13/4.15 の補助に限定 (mmd `references/gorenstein/finite-groups.mmd` L4181-4231)。Isaacs は 4.5(a)/4.3/4.10 の下請けに使う。

---

## 4. 必要な新規記法 / API (repo 性質補強コスト)

「def はあるが性質ゼロ」を **使える状態にするコスト**を正直に列挙。これが §4 着手前の実質的な第 0 波。

### 4.1 `PRank.lean` (現状: def のみ、lemma 0) — **最優先・第 0 波**
必要な追加:
- `pRank` の **BddAbove / 有限性** (現状 `iSup` が有界か未証明)。
- **評価補題** `pRank G p ≤ n ↔ ∀ elem-ab A, log_p|A| ≤ n`。
- **2 形の橋**: `pRank` (elem-ab log) ↔ BG `r_q` (abelian m(Ω₁))。`AddCommGroup.zmodModule` で `Module (ZMod p) (Additive A)` を与え、`m(A) := Module.finrank (ZMod p) (Additive A)`、`FiniteField.pow_finrank_eq_natCard` で `|Ω₁(A)|=p^{m(A)}` (調査 4)。
- **全素数版 `rank G := ⨆_p (pRank G p)`** (BG `r(G)`)。Thm 4.20 用。
- monotonicity (subgroup/quotient)。
- 工数: **3-5 日** (調査 3 が「§4 着手の最初の山」と明言)。

### 4.2 `SCN.lean` (現状: `IsSCN` struct + 2 projection) — **第 0 波、PRank 後**
- **`SCN₃` / `SCN_n` 述語** (rank≥n の SCN) を `pRank` と連動定義 (現 docstring が「PRank 完成後追加」と明記)。
- **Prop 4.4(a)**: `IsSCN A ↔ A maximal-abelian-normal`。一方向は `centralizer_eq_self_of_maximal_abelian_normal` (CriticalSubgroup.lean:166)、逆方向 + 集合等号は新規。
- **BG-literal SCN への橋**: repo `IsSCN` は `IsMulCommutative` を**含む**が、BG `SCN(R)={A⊴R : C_R(A)=A}` は abelian 不問 (p-群では Prop 4.4(a) で一致)。clean 参照のため 1 本橋を引く。
- **レバレッジ大**: `SCN₃` は §5/§7/§8/§9 も待っている (notes s07-s09)。ここで定義すると §4-§9 の前提が一気に開く。
- 工数: **2-4 日**。

### 4.3 `IsMetacyclic.lean` (現状: def + `of_isCyclic` + `isSolvable`)
- **subgroup/quotient closure** (docstring が「非自明・未収載」と明記)。→ **Isaacs Lemma 10.13** の短い proof (mmd L5588) で埋まる (Gorenstein 不要、調査 2 の good find)。
- Lem 4.10 (Ω₁≅E_p²)、Prop 4.11 (Huppert 分類)、Thm 4.12 (operator) は §4 本体側で実装。
- 工数: closure **1-2 日**、分類は §4 本体に計上。

### 4.4 `IsExtraspecial.lean` (現状: struct + 3 projection)
- 現 def は一般 extraspecial。**Thm 4.16(2) は "exponent p, 位数 p³" の特殊形 M(p,1)** が要る → `exponent (G) = p` を加えた述語 or `IsExtraspecial p G ∧ Monoid.exponent G = p`。
- Lem 4.15 用 commutator 補題 (`[S,R]⊆S'⇒R=SC_R(S)`)。
- 工数: **1-2 日** (def 拡張は軽い、Lem 4.15 本体込み)。

### 4.5 `OmegaSubgroup.lean` (現状: `Omega` def + `omega1OfAbelian`)
- `|Ω₁(A)|=p^{m(A)}` (§4.1 の橋で従属)。
- **`℧ⁿ(R)=⟨x^{pⁿ}⟩` (agemo) が repo 完全不在**。Prop 4.11/Thm 4.12 で `℧¹` 使用。新規。
- 工数: **1-2 日**。

### 4.6 `CentralProduct.lean` (新規、repo・mathlib 完全不在) — **Thm 4.16(2) 専用**
- 設計案 (最小): `def IsCentralProduct (R R₁ R₂ : Subgroup G) : Prop := R = R₁ ⊔ R₂ ∧ ⁅R₁,R₂⁆ = ⊥ ∧ R₁ ⊓ R₂ ≤ Subgroup.center R`。mathlib `Subgroup.sup`/`commutator`/`center` で組む。SemidirectProduct/DirectProduct とは別。
- Thm 4.16 結論専用なので最小限で可。
- 工数: **2-3 日** (設計 + 基本補題)。

**補強コスト合計 (def→使える)**: 約 **12-18 日** (PRank 3-5 + SCN 2-4 + Metacyclic closure 1-2 + Extraspecial 1-2 + Omega/agemo 1-2 + CentralProduct 2-3)。これは §4 定理証明とは**別建ての前提整備**。

---

## 5. 実装順 (Wave) + v1 スコープ

### Wave 0: 性質基盤 (前提整備、§4 定理に入る前)
`PRank` 性質 → `SCN₃` 定義 + Prop 4.4(a) → `IsMetacyclic` closure (Isaacs 10.13) → `agemo ℧` → `CentralProduct` 述語 → `IsExtraspecial` exp-p 拡張。
**この Wave 完了で §4-§9 が SCN₃ を使える**ようになる (最大レバレッジ)。

### Wave 1: 下層補題 (Isaacs/repo 流用が効く、軽い)
Lem 4.2 (repo) → Prop 4.3(a) cl≤2 (repo)、cl≤3 分岐 (B) → Lem 4.5 (repo ElementaryAbelian + Isaacs 4.36) → Lem 4.6 → **Lem 4.17 (repo Thm 1.13、独立に最速)**。

### Wave 2: rank/metacyclic 中核
Prop 4.4(a) 完成 → Lem 4.7 → Prop 4.8 → Lem 4.9 → Lem 4.10 → **Prop 4.11 (Huppert、山 2)** → **Thm 4.12 (Huppert)** → Lem 4.13/4.14/4.15。

### Wave 3: Blackburn 本体
**Thm 4.16 (山 1)** = Wave 0-2 を全部組む + central product + GL(2,p) 合同。

### Wave 4: 下流構造定理
Thm 4.18 (Isaacs Ch06 Fitting 依存) → Cor 4.19 → Thm 4.20。

### v1 スコープ (§5 narrow / §7 transitivity が §4 から最小限要求するもの)

下流が **4.16 フル分類を待たずに** 開ける部分を切り出す:

- **§7 (Thompson transitivity)** が §4 から要求する核 = **`SCN₃` 述語 + Lem 4.7** (`r_p(R)≤2 ⟺ SCN₃=∅`)。§10 の `α(M)={p : r_p(M)≥3}` 定義もこれ。→ **Wave 0 (SCN₃) + Lem 4.7 だけで §7/§10 の前提が開く**。Thm 4.16 本体は不要。
- **§5 (narrow p-groups)** が §4 から要求 = `pRank` 性質 + Prop 4.4(a) (SCN 特徴付け)。→ **Wave 0 で開く**。
- **Thm 4.18/4.20** は §7-§16 の Sylow tower 骨格だが、調査 1 によれば現フロンティア (§7-§16) の**さらに先**で消費される。FT master roadmap 上のボトルネックは §7 Thompson transitivity 自体。

**→ v1 = Wave 0 (PRank/SCN₃/Prop 4.4(a)) + Lem 4.7。** これで §5/§7/§10 の §4 依存が解け、Thm 4.16 フル分類 (Wave 1-3、最重) は v2 に後回しできる。**下流を最速で開けるなら Wave 0 + Lem 4.7 を最初に切る**のが正しい。

---

## 6. 工数見積 + 自律 workflow stage 構成

### 工数見積 (誇張なし、調査 3 の「30-40 日」と整合させた内訳)

| ブロック | 日数 | 備考 |
|---|---|---|
| Wave 0 性質基盤 | 12-18 | PRank が最初の山。SCN₃ レバレッジ大 |
| Wave 1 下層補題 | 4-6 | Isaacs/repo 流用で軽い。Lem 4.17 は 0.5 日 |
| Wave 2 rank/metacyclic | 8-12 | **Prop 4.11/Thm 4.12 Huppert が山 2** (帰納 + Ω₁ 計算密) |
| Wave 3 Thm 4.16 | 8-10 | **単一最難**。central product + GL(2,p) 合同 + 場合分け |
| Wave 4 下流 4.18-4.20 | 5-8 | Isaacs Ch06 Fitting 依存 (未確認分のリスク) |
| **計** | **37-54** | s04 ノート「30-40」より上振れ (性質ゼロ問題 + central product を厳しめに) |

**v1 (Wave 0 + Lem 4.7) のみなら 14-20 日**で §5/§7 が開く。

### 自律実装 workflow の stage 構成 (0016 と同型に乗るか)

**乗る。ただし 0016 (Thm 1.13 単発) と違い §4 は 20 定理 + 6 module 補強なので、issue 単位を細分し各 issue 内で stage 駆動するのが適切。** 0016 が `S1→…→BG-facing` で回したのと同型の「fixed statement・single-leaf・build-green」型 workflow に**乗るのは各 issue だけ**で、§4 全体は multi-issue。

**推奨 issue 分割** (各 issue が `/goal` build-green workflow の単位):

1. `issue: pRank 性質補強` (Wave 0a) — fixed statement 群、single-leaf `PRank.lean`。**`/goal build-green` 型に最適**。
2. `issue: SCN₃ 定義 + Prop 4.4(a)` (Wave 0b) — `SCN.lean`。
3. `issue: IsMetacyclic closure (Isaacs 10.13)` + `agemo` + `CentralProduct` 述語 — module 補強束。
4. `issue: Lem 4.2/4.3/4.5/4.6 + Lem 4.17` (Wave 1) — `S04_*.lean` 下層。
5. `issue: Lem 4.7` (v1 ゴール、§7 を開く) — ここまでが **v1**。
6. `issue: Prop 4.8-4.12 (Huppert)` (Wave 2、**最難 stage の一つ**)。
7. `issue: Lem 4.13-4.15`。
8. `issue: Thm 4.16 Blackburn` (Wave 3、**単一最難**)。central product 構成 + GL(2,p) 合同を sub-stage に。
9. `issue: Thm 4.18-4.20` (Wave 4、Isaacs Ch06 依存リスク)。

**stage 数**: 全 §4 で **9 issue**。各 issue 内は 0016 同様 `S1 (statement 確定) → S2-Sk (補題逐次 build-green) → final (BG-facing API)` で 3-6 stage。

**最難 stage**: **issue 8 (Thm 4.16)**。理由 — (a) 帰納法 + `|Ω₁|` 場合分け、(b) **central product と exp-p extraspecial の新規 API をその場で要求**、(c) GL(2,p) の `j²≡1 mod p` 合同矛盾が新規線形代数計算で fixed statement に落としにくい。**memory `scaffold-sorry-free-not-done` の警告が最も効く箇所**: conditional scaffold で hard content を hypothesis に追い出して "sorry-free" に見せかけるリスクが高い → judge は hypothesis constructibility で。**issue 8 は `/goal` 単発で回さず、設計 + 複数 sub-issue に割るべき** (memory `goal-command-spec`: design/multi-sub 型には `/goal` は不適)。

**次点の難所**: **issue 6 (Prop 4.11/Thm 4.12 Huppert)** — BG 自前帰納法が密。

**workflow に乗せやすい順** (=`/goal build-green` 単発が効く): issue 1, 2, 3, 5 (定義・性質・closure・単一補題、fixed statement)。issue 4, 7 は中。**issue 6, 8, 9 は設計先行 (multi-sub)**。

---

## 主要パス (相対でなく絶対、読み手の参照用)

- BG §4 原典: `/home/ywr/odd-order/references/bg/local-analysis.mmd` L1359-1788 (4.16 本体 L1636-1704)
- 既存ミニロードマップ (20 結果表 L42-61): `/home/ywr/odd-order/notes/bg/s04_pgroups_small_rank.md`
- Gorenstein 行間 (4.7⇐/4.13/4.15): `/home/ywr/odd-order/references/gorenstein/finite-groups.mmd` L4181-4231
- **Isaacs Ch04 §4D (sorry-free, 4.36/4.35/4.8)**: `/home/ywr/odd-order/OddOrder/Isaacs/Ch04_Commutators/Main.lean` (`isaacs_thm_4_36` ≈ L4040 台、`actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p` L3442、Thm 4.8 L1462)
- repo 補強対象: `/home/ywr/odd-order/OddOrder/GroupTheory/{PRank,SCN,IsMetacyclic,IsExtraspecial,OmegaSubgroup}.lean`
- repo 流用元: `/home/ywr/odd-order/OddOrder/GroupTheory/{CriticalSubgroup,ElementaryAbelian}.lean` (4.2/4.3(cl≤2)/4.5 の下請け)
- Lem 4.17 出典 (Thm 1.13): `/home/ywr/odd-order/OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean:845` (`thompson_critical_omega`)
- 新規作成先: `/home/ywr/odd-order/OddOrder/BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean` (未作成) + `/home/ywr/odd-order/OddOrder/GroupTheory/CentralProduct.lean` (新規)

## 要確認 gap (実装着手前に潰すべき、リスク順)

1. **Isaacs Ch06 (Fitting Thm 6.16) / Ch07 (Thm 7.6.5) の形式化状態未確認** — Thm 4.18 / Prop 4.4(b) が依存。Ch06/Ch07 dir は存在するが定理レベル未 audit。**Wave 4 / Prop 4.4(b) のリスク**。
2. **Aut(elem-ab F_p^n) ≅ GL(n,p) 橋が mathlib にあるか未確認** — Lem 4.13 / Thm 4.16 が `Matrix.card_GL_field` を使うのに必須。無ければ自前。
3. **BG §1 Lem 1.22 / Prop 1.2 / Prop 1.6 (CoprimeAction) の状態未確認** — Lem 4.6 / Thm 4.12 / Thm 4.20 依存。
4. **central product 表現の設計が未確定** — §4.6 案は最小限だが、Thm 4.16(2) の `Ω₁(R₂)=R₁'` 条件込みで述語が十分か実装時検証要。
5. **Lem 4.7(⇐) が下流 4.18/4.20 で実際に要るか** — 要れば Gorenstein 5.4.15 行間読みが必須化 (v1 では `⇒` のみで回避可)。