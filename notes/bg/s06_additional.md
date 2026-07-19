# BG §6: Additional Results — mini-roadmap (FT critical normal-J hub)

**スコープ**: BG §6 (mmd L1957-2128, PDF pp. 49-66 + blank p.67), **7 結果** (Thm 6.1, 6.2, 6.3, 6.4, 6.7 + Lem 6.5, 6.6 — ナンバリング注: 6.3 は Lemma, 飛び番号 6.8+ は存在せず).

形式化先: [`OddOrder/BG/Ch1_Preliminary/S06_Additional.lean`](../../OddOrder/BG/Ch1_Preliminary/S06_Additional.lean) (着手済).

## 実装状況 (2026-05-27)

**core results 3 件 sorry-free 完成・配線済** (commit `b3a51b2`):
- `comm_of_isPGroup_two_of_odd` (helper): 奇数位数 ⇒ 2-部分群自明 ⇒ 可換 (`normal_J` の `h2abelian` discharge)。
- `thompsonJ_le_opCore_of_odd` (**Thm 6.1 reduced case**): 奇数 solvable, p≠2, P∈Syl_p, O_{p'}=⊥, P=C_G(Z(P)) ⇒ `J(P) ≤ O_p(G)`。
- `normalJ_normal_of_odd` (**Thm 6.2 reduced case**): 同仮説 ⇒ `J(P) ⊴ G`。

いずれも `OddOrder.Isaacs.Ch07.{normal_J, thompsonJ_le_opCore_of_normal_J_hypotheses}` を呼び、奇数位数+solvable で自動充足する 2 仮説 (`h2abelian` / `h_pSolvable` via `isPiSeparable_of_solvable` instance) を discharge した特殊化。

**残課題 (2026-05-27 difficulty 再評価 — 前回見立て訂正)**:

> **2026-05-28 追記**: §6 → App.A+B(Puig)で Gorenstein 依存を捨てる経路の設計決定・依存閉包・J→L 大域置換の検証は [`notes/meta/bg_s6_appAB_route_2026_05_28.md`](../meta/bg_s6_appAB_route_2026_05_28.md) に集約。要点: Isaacs は Z(J) を省くため 6.2 は **App.B Thm B.4(Puig L(S))**で代替、ゲートは **A.4(b)+A.4(c)**(7.3 reduction、最深部 7.3 は repo 既証)。

⚠️ **重要訂正**: Thm 6.1/6.2 の一般形は repo の `Isaacs.Ch07.normal_J` への単純簡約では**到達しない**。原文精読 (mmd L1971-1977) で判明:
- BG **Thm 6.1** = Hall-Higman (Gorenstein **6.5.2**)、BG **Thm 6.2** = Glauberman ZJ (Gorenstein **6.5.1** + 8.2.11)。いずれも「任意 Sylow S・`P=C_G(Z(P))` 仮定なし」の**完全形**。
- repo の `normal_J` は Isaacs **Thm 7.6**(仮説 `O_{p'}=1` ∧ `P=C_G(Z(P))` ⇒ `J(P)⊴G`)で、Isaacs はこれを **Thompson normal p-complement (7.1) の補題**として使う。一般 ZJ とは別物。`P=C_G(Z(P))` ギャップは O_{p'}-商簡約では埋まらない。
- ⇒ **Thm 6.1 (Hall-Higman) / Thm 6.2 (ZJ) はともに実質的な新規証明**。今回の reduced case (`normalJ_normal_of_odd` 等) は J(P)-instance の特殊形で、一般形の足場ではあるが直接の前段ではない。
  - ⚠ **2026-07-19 追記 — この行は Thm 6.1 については誤り**。Thm 6.1 の一般形は「新規証明」を
    要さず、**App.A 側に `thmA4b` として既に存在していた** (下記残課題 3 参照)。Thm 6.2 (ZJ) に
    ついては正しく、実際 Gorenstein Ch.8 §2 の全面移植を要すると確定した (issue 3024)。

残タスク (難度順):
1. **(infra)** `opCore p G ≤ oPiPrimePiCore {p} G` 橋 (O_p ≤ O_{p',p})。`IsPiGroup.le_oPiCore` + `IsPGroup.map` + `map_le_iff_le_comap`。注意: `oPiPrimePiCore` の `{q | q ∉ {p}}` と `normal_J` の `{q | q ≠ p}` の set 同値 (`Set.mem_singleton_iff`)。自己完結・再利用可。
2. **Lem 6.3** (solvable: normal Hall H + complement K, H⊆G' ⇒ H=[H,K] ∧ C_H(K)⊆H')。BG Prop 1.5(d)/1.6(d) = Ch04 (`fixedPoints_sup/inf_actionCommutator`) 済で**最も tractable**。
3. ~~**Thm 6.1** (Hall-Higman 一般形)~~ → ✅ **完了** (2026-07-19、issue 3025)。⚠ ただし
   **本項の想定は誤りだった**: 「§7B internals を再利用して新規に構築」する必要は無く、
   **一般形は既に `OddOrder.BG.AppA.thmA4b` (`AppA_PStability.lean:1387`) として存在していた**
   (`O_{p'}(G) = ⊥` も `C_G(Z(P)) = P` も仮定せず、`O_{p'}` reduction を内部で実行)。
   BG 自身 mmd L4627 で「Theorem A.4(b) is just Theorem 6.1」と同一視している。
   §6 側の入口 = `S06_Thm61.le_oPiPrimePiCore_of_abelian_normal_in_sylow` で、実質は
   `thmA4b` の `p ≠ 2` (奇数位数下で vacuous) を任意素数へ外しただけ。新規の数学は無し。
3.5. ~~**Thm 6.4**~~ → ✅ **完了** (2026-07-19、issue 3026)。無条件形
   `S06_Thm64Case2.exists_centralizing_conj_sup_isPiGroup_of_normalHall`。`|G|+|H|` の強帰納で、
   reduction「`G = LH` としてよい」+ `π(F(G)) ⊆ π(H)` の 2 分岐。⚠ 過程で **BG p.50 の誤植**を
   発見・訂正した (原文 `[H,yz] ⊆ H ∩ L = 1` の `L` は `N` の書き損じ; 結論は健全)。
   Coq は本定理を「revised proof に不要」として落としており repo にも consumer は無いが、
   CLAUDE.md「進捗の測り方」に従い正面から形式化した。
4. **Thm 6.2** (Glauberman ZJ 一般形): ⚠ **blocked** (2026-07-19 確定、issue 3017 → **3024**)。
   literal `J(S)` 一般形は Gorenstein Ch.8 §2 (Glauberman ZJ) の全面移植を要し
   (2,000-4,000 行/複数 session)、repo には p-stable+p-constrained 版 ZJ が無い。
   `C_G(Z(P)) = P` は反例あり (位数 1029 の `7^{1+2} ⋊ C₃`) で discharge 不可。
   **book 推奨代替の `L(S)` 一般形は済** = `AppB_Thm62.zCenter_lOdd_sup_oPiCore_normal`。
   math-comp も ZJ を形式化せず `L(S)` で代替している。
5. Thm 6.4 (J₁/J₂ 共役, 長い帰納), Lem 6.5/6.6 (p-length 1 系)。

**ROADMAP 上の位置**: **Phase 2a 第 2 波** (Phase 1 Ch.7 完成必須, §1+§3+§4 完了直後).

**FT 経路上の位置**: ☆☆☆ **クリティカル**. **Thm 6.2** が §7, §8, §9, App.A, App.B, App.C で **7+ 箇所引用される** FT の核心結果.

## TL;DR — Thm 6.2 normal-J hub

§6 は **局所解析の道具袋**: 5 つの solvable + p-length 系の定理群 (Thm 6.1, 6.2, 6.4, 6.7, Lem 6.5, 6.6) のうち、特に **Thm 6.2 `Z(J(S))·O_{p'}(G) ⊴ G`** が **§8, §9 (Uniqueness Theorem) で FT クリティカルパスの要**. Isaacs Thm 7.6 と **完全等価** (odd-order 仮定下).

形式化困難度: **Thm 6.2 は論理的に Isaacs Ch.7 (Thm 7.6) に依存**, App.A (p-Stability) で再述. Phase 2a §6 開始 = Phase 1 Ch.7 完成の必須条件.

## §6 全 7 結果一覧

| # | 種別 | mmd 行 | statement 要約 (1-2 行) | Isaacs 対応 | 後続被引用 |
|---|------|--------|--------------------------|-------------|------------|
| **6.1** | Thm | 1971-1973 | **(Hall-Higman)** G solvable odd, p prime, S Syl_p ⇒ `O_{p',p}(G)` contains every abelian normal subgroup of S | Thm 3.21 (Hall-Higman 1.2.3) 再形式 | App.A Thm A.4 系; BG App.B Thm B.4 の代替 |
| **6.2** | **Thm** | **1975-1977** | **(normal-J)** G solvable odd, p prime, S Syl_p ⇒ `Z(J(S))·O_{p'}(G) ⊴ G` | **Thm 7.6** (odd-order 等価) | **§8 L2456, L2478, L2482; §9 L2511, L2515; App.A Thm A.4(b); App.B L5014, L5030; App.C L5030. 計 7+ 箇所** |
| **6.3** | Lem | 1981-1993 | (a) H normal Hall, K complement, H ⊆ G' ⇒ H = [H,K], C_H(K) ⊆ H'; (b) G' nilpotent, |G/G'| prime ⇒ G' Hall, G' = [G,K] for all complements K | Lem 2.17 + basic solvable theory | (used internally in §6-§9) |
| **6.4** | Thm | 1996-2044 | H π'-subgroup, G_0 normal Hall with G_0/F(G_0), (G/G_0)/F(G/G_0) nilpotent, H normalizes two π-subgroups J_1, J_2 ⇒ ∃x ∈ ⟨J_1, J_2⟩ s.t. ⟨J_1^x, J_2⟩ π-group, x centralizes H | (inductive theorem; relates to p-group conjugacy) | §13 (fringe), App.C |
| **6.5** | Lem | 2048-2088 | K ◁ G solvable, G = KU, H ⊆ U, (|H|,|K|)=1 ⇒ (a) H ∩ G' = H ∩ U', (b) N_G(H) = C_K(H)N_U(H), (c) H^g ⊆ U ⇒ g = cu, c ∈ C_K(H), u ∈ U | Lem 2.17 + N/C theory | **§6 Lem 6.6 (internal); §8 L2246; §10 L2795, L2797, L2801; §13 L3365; App.C** |
| **6.6** | Lem | 2090-2103 | G solvable, p-length 1, S Syl_p ⇒ (1) `O_{p',p}(G) = O_{p'}(G)·S`, G = `O_{p'}(G)·N_G(S)`, (2) S ⊆ G' ⇒ S ⊆ (N_G(S))', (3) Y ⊆ S, Y^x ⊆ S ⇒ ∃c ∈ C_G(Y), g ∈ N_G(S), cg = x, (4) Q p-subgroup ⇒ ∃x ∈ C_G(Q∩S) s.t. Q^x ⊆ S | (p-length 1 characterization; Isaacs Thm 5.26 Frobenius normal p-complement と関連) | **§6 Thm 6.7 (internal); §8 L2795; §10 L2795; App.C via p-length context** |
| **6.7** | Thm | 2105-2127 | G solvable, p odd prime, E ∈ E^*_p(G), L p'-subgroup normalized by E, p-length 1 ⇒ L ⊆ O_{p'}(G) | (Thompson-type result on E^*_p(G); 関連: App.A Thm A.3 p-stability) | §7 L2261 (via Hypothesis 7.1); §13 indirectly; App.C |

## Thm 6.2 (normal-J theorem) の詳細

### Statement (mmd L1975)

```
G: solvable group of odd order
p: prime
S: Sylow p-subgroup of G
─────────────────────────────────
Z(J(S))·O_{p'}(G) ⊴ G
```

### 前提条件

1. **G is solvable** — G が可解群
2. **odd order** — |G| が奇数 (p ≠ 2, すべての素因子が奇数)
3. **p is a prime** — p: 任意の素数
4. **S ∈ Syl_p(G)** — S が p-Sylow subgroup

### 結論

**`Z(J(S))·O_{p'}(G) ⊴ G`** (normal subgroup となる).

- `J(S)` = Thompson J-subgroup of S = Isaacs Thm 7.2 の定義 (最大位数 elementary abelian 部分群の生成)
- `Z(J(S))` = center of J(S)
- `O_{p'}(G)` = largest p'-subgroup of G (p-complement)
- 結論は「Z(J(S)) と O_{p'}(G) の積が normal」, すなわち `Z(J(S)) ⊆ N_G(O_{p'}(G))` かつ `O_{p'}(G) ⊴ G` (後者は trivial since O_{p'}(G) はそもそも normal characteristic)

### 証明源 (BG L1977)

```
**Proof.**  G, Theorem 6.5.1, p. 234 and Theorem 8.2.11, p. 279. □
```

BG は Gorenstein 1968 "Finite Groups" を引用 (Isaacs FGT に読み替え要).

### Isaacs Thm 7.6 との対応

**完全等価** (odd-order 仮定下):

| 観点 | Isaacs Thm 7.6 | BG Thm 6.2 | 備考 |
|------|----------------|------------|------|
| **型** | p-solvable + abelian Sylow-2 + C_G(Z(P))=P, O_{p'}=1 ⇒ J(P) ⊴ G | odd-order solvable ⇒ Z(J(S))·O_{p'}(G) ⊴ G | BG は odd-order 仮定で **仮定を減らす** |
| **中核結論** | J(P) ⊴ G | Z(J(S))·O_{p'}(G) ⊴ G | Isaacs は J(P) の normality 直接; BG は Z(J(S))·O_{p'}(G) の normality |
| **証明方針** | 8 step proof: (1-3) maximal elementary abelian 特性化, (4-6) GL(2,p) embedding, (7-8) abelian Sylow-2 と normal-P theorem 結合 | Gorenstein 参照 (短縮) | App.A で BG が Isaacs 手法の odd-order 再述 |
| **App.A 記載** | Thm A.4(b) — "P ∈ Syl_p(G) ⇒ every normal abelian subgroup of P is in O_{p',p}(G)" | Thm 6.1 (Hall-Higman 再形) + Thm 6.2 の系 | App.A は Thm 6.2 を **odd-order p-stability 下での再構築** |

### Phase 2a 形式化方針

**選択肢 1 (Isaacs import 派)**:
- Phase 1 Ch.7 Thm 7.6 を import (`OddOrder.Isaacs.Ch07_ThompsonSubgroup.theoremJ_norm`)
- BG Thm 6.2 statement を Isaacs Thm 7.6 の odd-order 特例として形式化
- 証明: Isaacs output → odd-order constraint で簡略化

**選択肢 2 (BG 流再証明派)**:
- Isaacs Thm 7.6 を **参考** にするが, BG App.A (p-Stability) 経由で直接実装
- Gorenstein 原典 → Isaacs に読み替え, BG の odd-order 短縮を Lean で展開
- 長所: BG App.A の理論体系を局所解析に密着させられる
- 短所: 証明が長い (Isaacs 8 step の再構築)

**推奨**: **選択肢 1 (Isaacs import)** — Phase 1 Ch.7 完成後すぐ着手可能, 形式化コスト低い. BG App.A Thm A.4(b) は Isaacs result の thin wrapper になる.

## Thm 6.4, 6.7 / Lem 6.5, 6.6 — p-length 1 系の道具袋

### Lem 6.5 (3 parts, solvable N/C theory)

**目的**: solvable group G = K·U (K normal, coprime order) 下での Hall subgroup の normalization and conjugacy.

**主要結論**:
- (a) `H ∩ G' = H ∩ U'` — derived series reduced modulo normal factor
- (b) `N_G(H) = C_K(H)·N_U(H)` — normalizer decomposition
- (c) `H^g ⊆ U ⇒ g = cu, c ∈ C_K(H), u ∈ U` — conjugacy decomposition

**被引用**: §6 Lem 6.6 (2 箇所), §8 L2246 (M_σ structure), §10 L2795-L2801 (p-length 1 analysis), §13 L3365 (E structure), App.C.

**形式化**: 難度中. Isaacs Lem 2.17 (N/C quotient) からの自然な拡張, coprime action と Hall theory の結合.

### Lem 6.6 (4 parts, p-length 1 characterization)

**目的**: p-length 1 群 G (i.e., `G = O_{p'}(G)·P` for P Syl_p) の Sylow subgroup と関連構造の characterization.

**主要結論**:
1. `O_{p',p}(G) = O_{p'}(G)·S`, `G = O_{p'}(G)·N_G(S)` (Frattini argument)
2. `S ⊆ G' ⇒ S ⊆ (N_G(S))'` (Lem 6.5(a) 応用)
3. `Y ⊆ S, Y^x ⊆ S ⇒ ∃c ∈ C_G(Y), g ∈ N_G(S), cg = x` (Lem 6.5(c) 応用)
4. `Q p-subgroup ⇒ ∃x ∈ C_G(Q∩S) s.t. Q^x ⊆ S` (Sylow conjugacy + centroid)

**被引用**: §6 Thm 6.7 (kernel), §8 L2795 (proof start), §10 L2795-L2801 (M_σ, maximal subgroup analysis), App.C (p-length framework).

**形式化**: 難度高. (3), (4) は induction + Sylow conjugacy + coprime action の複雑な結合. Lem 6.5 に強く依存.

### Thm 6.4 (π-subgroup conjugacy under Hall divisibility)

**目的**: π-subgroup と π'-divisor 操作の conjugacy theorem — §6.4 内で最大結果, §13 (prime action) で参照されるが局所的.

**主要機構**:
- `H π'-subgroup normalizes J_1, J_2 (π-subgroups)`
- **条件**: G_0 normal Hall, G_0/F(G_0) and (G/G_0)/F(G/G_0) both nilpotent
- **結論**: `∃x ∈ ⟨J_1, J_2⟩ s.t. ⟨J_1^x, J_2⟩ π-group and x centralizes H`

**証明**: 長い (L2000-L2044). induction on |G| + |H|, case split on π(F(G)) ⊆ π(H).

**形式化**: 難度高. 独立した "conjugacy forcing" theorem; Lem 6.5(c) + Hall theory + order divisibility 引数の集積.

### Thm 6.7 (p-odd elementary abelian action ⇒ π'-containment)

**目的**: p odd, p-length 1, E maximal elementary abelian p-group ⇒ p'-subgroups normalized by E は O_{p'}(G) に contained.

**証明**: 3 ステップ (L2109-L2127)
- Reduction mod K = O_{p'}(G) to K = 1 case
- Lem 6.6 (p-length 1 characterization) で S ◁ G
- Corollary 1.12 (abelian on p-group) で L centralizes S
- Proposition 1.15(a) (centralizer ⊆ O_{p',p}(G)) で L ⊆ S
- L p'-group ⇒ L = 1

**形式化**: 難度中. Lem 6.6 + prior theorems (1.12, 1.15) の blackbox 利用; 自体は短い.

## mmd 抽出問題と PDF 確認結果

### BG §6 ヘッダ問題

| 問題 | 状況 | 解決 |
|------|------|------|
| **mmd 内 `### 6` 無し** | L1969 で `**6. Additional Results**` (inline marker のみ) | PDF pp. 49-66 で確認: 章タイトル **"6. Additional Results"** (p.49) |
| **mmd L1957** | `6. Additional Results` (テキストラッパー, actual § marker 無し) | Nougat 抽出時の章番号認識ミス. mmd 線形処理 OK だが `### 6` 見出し復元は format issue |
| **PDF page number** | BG p.49 (§6 開始) - p.66 (Thm 6.7 proof end) | **18 ページ, 7 結果 + 7 proofs + remarks** |

### MISSING_PAGE_EMPTY:67

| 詳細 | 記載 |
|------|------|
| **mmd L2129** | `[MISSING_PAGE_EMPTY:67]` |
| **PDF p.67** | **完全に blank** (Nougat OCR 失敗 or 原本スキャンミス) |
| **PDF p.66 末尾** | Thm 6.7 proof 終了 "`□`" |
| **PDF p.68 冒頭** | "**CHAPTER II** — The Uniqueness Theorem" (§7 開始) |
| **§6 末尾への影響** | **なし** — §6 内容は p.66 で完全に closed, p.67 blank は単なる page break 空白 |

**結論**: MISSING_PAGE:67 は §6 に論理的影響なし. mmd L2128 後の内容欠落なし.

## mathlib カバレッジ評価 (Phase 1 Ch.7 完成下)

| 結果 | mathlib | 新規実装 | 難度 |
|------|---------|----------|------|
| **Thm 6.1** (O_{p',p}(G) abelian containment) | **mid** (Hall, abelian, normal: existing) | thin wrapper (Isaacs Thm 3.21 read-through) | 短 |
| **Thm 6.2** (Z(J(S))·O_{p'}(G) ⊴ G) | **low** (J(S) 定義: 新規; Z(J(S)): `Subgroup.center` OK; O_{p'}: `Subgroup.pCore` OK) | **Isaacs Thm 7.6 import** (選択肢 1) or **App.A p-stability 再証明** (選択肢 2) | **大** (App.A 経路) |
| **Lem 6.3** (Hall + derived series) | **high** (Hall: `exists_subgroup_dvd`, derived, solvable: existing) | thin wrapper | 短 |
| **Thm 6.4** (π-subgroup conjugacy) | **low** (induction, case split, Frattini: basic) | **独立新規実装** (局所 conjugacy theorem) | 大 |
| **Lem 6.5** (solvable N/C decomposition) | **mid** (`Subgroup.normalizer`, derived, Hall: existing) | thin wrapper (Isaacs Lem 2.17 拡張) | 中 |
| **Lem 6.6** (p-length 1 characterization) | **mid** (`Subgroup.pCore`, Sylow, Frattini: existing) | Lem 6.5 + Sylow conjugacy 組み合わせ | 中-大 |
| **Thm 6.7** (p-odd E^*_p(G) ⇒ O_{p'}(G)) | **low** (E^*_p(G) 定義: 新規; 他: abelian, normalize, Lem 6.6) | Lem 6.6 + 1.12, 1.15 依存 | 中 |

**総合**: **Phase 1 Ch.7 (Thm 7.6) 完成後, Thm 6.2 は import 可 (選択肢 1). Lem 6.5, 6.6, Thm 6.7 は 3-4 週の実装量. Thm 6.4 は独立だが局所的 (§13 edge). §6 全体形式化: Isaacs import 経路で 2-3 週, BG 再証明経路で 4-5 週**.

## Phase 2a §7-§16 での被引用

### Thm 6.2 (7+ 箇所, FT core)

| セクション | mmd 行 | 引用文脈 |
|-----------|--------|---------|
| **§8.1** (Fitting) | L2456 | "By (8.9) and **Theorem 6.2**, we know that Z(J(P)) ⊴ M. Consequently N_G(P) ⊆ N_G(Z(J(P))) = M" — Thm 8.1 核心ステップ |
| **§8.1** | L2478 | "By (8.12) and **Theorem 6.2**, [analysis of R Sylow structure]" — maximal subgroup 定義 |
| **§8.1** | L2482 | "By (8.9), (8.13), and **Theorem 6.2**, M = N_G(Z(J(R))) = H [contradiction]" — Thm 8.1 終了 |
| **§9.1** (Uniqueness) | L2511 | "By **Theorem 6.2**, O_{p'}(M)·Z(J(P)) ⊴ M. Therefore, by Frattini argument, [N_G(P) structure]" — Uniqueness proof core |
| **§9.1** | L2515 (implicit) | Theorem 9.6 論証で Z(J(P)) ⊴ structure を多重活用 |
| **App.A** (Thm A.4) | L4476-L4488 | "Theorem A.4(b): **P ∈ Syl_p(G) ⇒ every normal abelian subgroup of P is in O_{p',p}(G)**" — Thm 6.2 の odd-order p-stability 形再述 |
| **App.C** (Lem D.1) | L5014, L5030 | "Let N = N_G(Z(J(P))). (One may substitute L(P)... if one prefers to use **Theorem B.4 instead of Theorem 6.2**)" — Puig L(P) 代替との parallel 提示 |

**計 7 明示引用** (§8: 3, §9: 2, App.A: 1, App.C/B: 1, cross-ref を含むとさらに多数).

### Lem 6.5, 6.6 (内部 + §8-§13 多用)

| セクション | 行 | 引用 |
|-----------|-----|------|
| **§6 内部** | L2100-L2101 | Thm 6.7 証明: Lem 6.5(a), (c) 活用 |
| **§7** | L2261 | Hypothesis 7.1 (Transitivity) setup で Thm 6.7 言及 |
| **§8** | L2246 | "By Lemma **6.5**, N_G(P) = LC_K(P)" — maximal subgroup normalization |
| **§10** | L2795-L2801 | Thm 10.4 証明: Lem **6.6** 4 部中 (a), (c) 連続活用. p-length 1 → Sylow structure |
| **§13** | L3365 | "By Corollary 10.9(b), it follows from **Lemma 6.5(b)**" — E structure 正規化 |

### Thm 6.4 (局所, §13 周辺)

| セクション | 行 | 引用 |
|-----------|-----|------|
| **§7 (間接)** | L2261 | Thm 6.4 なし, 代わりに Thm 6.7 |
| **§13** (理論上) | — | Thm 6.4 π-conjugacy は "prime action" 論証の補助だが明示引用は稀 |
| **App.C** | — | Thm 6.4 理論的後ろ盾 (counterfactual 除去) |

## Peterfalvi での被引用

**検索**: `references/peterfalvi/04.*.mmd` (Peterfalvi §1-§9 = 本文) + `05-09.*.mmd` (付録) で "[BG] §6", "BG 6", "Theorem 6.2", "Lemma 6.5" grep.

**結果**: (Peterfalvi 本体実装前なので予備スキャン)
- **Peterfalvi §10** (Minimal Simple Group structure): "[BG] Theorem 6.2" 間接参照 (構造分析で Z(J(P)) 正規化)
- **Peterfalvi 付録** (Suzuki 等): [BG] §6 直接引用 **0 件** — 付録は [Suzuki 1957], [H]/[HB] Huppert 中心

**結論**: Peterfalvi 本体は BG を通じた間接依存 (§10 以降で BG App.C → BG Thm 6.2 chain). Phase 2a §6 完了 → Phase 2b §10 着手依存度 **確定**.

## Phase 2a 形式化着手順

### 推奨順序 (§6 内)

1. **Lem 6.3** (Hall + derived): 短く high mathlib coverage. 準備段階 (1-2 日).
2. **Lem 6.5** (solvable N/C decomposition): Isaacs Lem 2.17 拡張, 独立. Lem 6.6 先行不要 (2-3 日).
3. **Lem 6.6** (p-length 1 characterization): Lem 6.5 + Sylow theory. 4 部中 (1)-(3) 順次 (3-4 日).
4. **Thm 6.7** (p-odd E^*_p ⇒ O_{p'}): Lem 6.6 直接依存, 短い (1-2 日).
5. **Thm 6.1** (Hall-Higman O_{p',p}(G) containment): Isaacs Thm 3.21 thin wrapper (1 日).
6. **Thm 6.2** (normal-J): Isaacs Ch.7 Thm 7.6 import (選択肢 1) = 1-2 日; BG App.A 再証明 (選択肢 2) = 4-5 日.
7. **Thm 6.4** (π-subgroup conjugacy): 独立だが局所. §13 以前に着手するが優先度低 (2-3 日).

### 並列可能性

- **Group A**: Lem 6.3, 6.5 (独立)
- **Group B**: Lem 6.6 (Lem 6.5 後), Thm 6.7 (Lem 6.6 後) = 順次
- **Group C**: Thm 6.1, 6.2 (並列可, Thm 6.2 は Isaacs 依存)
- **Group D**: Thm 6.4 (独立)

**推奨**: Group A (2-3 日) → Group B (4-5 日) → Group C (2-3 日 with Isaacs, または 5-6 日 rebuilding) → Group D (2-3 日) = **計 11-17 日, または Isaacs import 経路 9-14 日**.

## Isaacs Thm 7.6 → BG Thm 6.2: 証明適用差異分析

### Isaacs 8 step proof (Ch.7 Thm 7.6)

```
仮定: (i) G p-solvable, (ii) p ≠ 2, (iii) Sylow-2 abelian, 
     (iv) O_{p'}(G)=1, (v) P = C_G(Z(P))
結論: J(P) ⊴ G
```

証明技法:
- Step 1-3: maximal elementary abelian 特性化, Z(P) fixed-point analysis
- Step 4: GL(2,p) embedding (Aut(E) ≅ GL(2,p) for E elementary abelian)
- Step 5: Lemma 7.3 (GL(2,p) 補助定理)
- Step 6: Lemma 7.4 (SL(2,q) unique involution = -I)
- Step 7: normal-P theorem (Thm 7.5), Hall-Higman 1.2.3 結合
- Step 8: J(P) normality 結論

### BG Thm 6.2 (odd-order special case) 証明

```
BG **Proof.**  G, Theorem 6.5.1, p. 234 and Theorem 8.2.11, p. 279. □
```

- **方策**: Gorenstein 1968 "Finite Groups" 参照 (短い証明)
- **odd-order 仮定活用**: G 奇数位数 → p-solvable ∧ abelian Sylow-2 (Burnside p^a q^b) 既に確立
- **BG App.A との関係**: Thm A.4(b) が **"odd-order solvable G, P ∈ Syl_p ⇒ every abelian normal ⊆ O_{p',p}(G)"** 形で再述 (Isaacs Thm 7.6 の odd-order 版)

### Phase 2a 形式化判断

**Isaacs 7.6 との等価性**:
- Isaacs 条件 (iv) O_{p'}(G)=1 は **一般性を失わない** (L4117 reduction argument)
- BG 結論 `Z(J(S))·O_{p'}(G) ⊴ G` は **`J(S) ⊴ C_G(O_{p'}(G))·O_{p'}(G)` の再表現**
- odd-order + solvable 下で **完全同値**

**形式化戦略確定**:

**選択肢 1 (推奨): Isaacs import**
```lean
theorem thm6_2 {G : Type*} [Group G] [Fintype G] [Odd G.card] 
    [IsSolvable G] {p : ℕ} [Fact (Nat.Prime p)] 
    (S : Sylow p G) : 
    (Subgroup.center (S.subgroup.thompsonJ) ⊔ Subgroup.pCore p' G).Normal G := by
  -- App.A Thm A.4(b) 経路 or Isaacs.Ch07.theoremJ_norm 直接 import
  sorry
```

長所:
- Phase 1 Ch.7 完成直後即時 (1-2 日)
- 証明論理簡潔 (import + odd-order specialization)
- BG App.A との論理的層化明確

**選択肢 2 (代替): BG App.A 経由再構築**
```lean
-- App.A Thm A.3 (p-stability 不可 ⇒ even order) と 
-- Thm A.4 (odd-order p-stability) を先に証明
-- その後 Thm 6.2 を Thm A.4(b) から導出
```

長所:
- BG 局所解析理論 self-contained
- App.A 証明自体が後続 §10-§16 への隠れた依存性 (p-stability framing)

**最終決定**: **選択肢 1** (Isaacs import). Phase 2a 日程短縮 + 検証簡便.

## mathlib カバレッジ (最終評価)

### §6 全 7 結果の mathlib 対応率

| 層 | 結果数 | mathlib 対応 |
|----|--------|-------------|
| **直接定理使用可** (statement 一致) | 0 / 7 | 0% — BG §6 は局所解析新概念集 |
| **概念存在, wrapper 必要** | 4 / 7 | ~57% (Hall, derived, normal, pCore: existing) |
| **部分依存, 新規 proof** | 3 / 7 | ~43% (Thm 6.2 via Isaacs, Thm 6.4 独立, Thm 6.7 オーダーメイド) |
| **完全新規定義** | J(S) | 1 個 — Phase 1 Ch.7 で既定義予定 |

**Phase 1 Ch.7 (Thompson J-subgroup) 完成 = Phase 2a §6 形式化開始の絶対必須条件**.

## 未解決 / TODO

| 項目 | 状態 | 確認先 |
|------|------|--------|
| **BG mmd §6 ヘッダ復元** | TBD | `### 6 Additional Results` 整合性スタイル検討 (mmd 再作成不可, docstring 選択) |
| **Isaacs Ch.7 Thm 7.6 実装日程** | TBD | Phase 1 第 5 波スケジュール確認 (Ch.6 完成前提) |
| **BG App.A p-stability 定義** | TBD | Thm A.3, A.4, A.5 statement と Thm 6.2 依存構造詳細化要 (per-section App.A ノート) |
| **Peterfalvi 04.10+ で [BG] Thm 6.2 引用詳細** | TBD | Phase 2b §10 着手前に引用パターン grep (現在予備) |
| **BG Thm 6.4 π-subgroup conjugacy の §13 応用** | TBD | §13 "Prime Action" ノートで詳細化 |

---

**作成**: 2026-05-22

**出典**: 
- `references/bg/local-analysis.mmd` lines 1957-2128 (§6 完文), PDF pp. 49-66 (本文) + p.67 (blank)
- `references/isaacs/finite-group-theory.mmd` lines 3828-3896 (Thm 7.6)
- `notes/isaacs/ch07_thompson.md` (Phase 1 Thm 7.6 ノート)
- `notes/bg/_overview.md` (BG overview)
- `notes/meta/phase2_cross_refs.md` (クロス参照マップ)

**次ステップ**: 
- Phase 1 Ch.7 進捗状況モニタ (Phase 2a §6 開始 gate)
- Per-section ノート (`notes/bg/s06_additional.md` 本文) 形式化
- Phase 2a 第 2 波スケジュール (§1, §4 完了後) 確定
