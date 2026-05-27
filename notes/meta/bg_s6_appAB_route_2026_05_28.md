# BG §6 (Thm 6.1/6.2) → App.A + App.B (Puig) で Gorenstein 依存を捨てる経路 — 設計決定

**作成**: 2026-05-28. **種別**: 横断設計決定 + 依存閉包分析 (BG §6 / App.A / App.B / §8-§9 / Isaacs Ch.7 をまたぐ).
**出典**: `references/bg/local-analysis.mmd` (§6 L1957-2128, App.A L4450-4516, App.B L4517-4758, §8 L2315-2485, §9 L2486-2630), `references/isaacs/finite-group-theory.mmd` (Ch.7 L3721-3961, HH 3.21 L1805), repo Ch.7 §7A/§7B.

## TL;DR

- **BG Thm 6.1 (Hall-Higman) = Gorenstein 6.5.2、Thm 6.2 (Glauberman Z(J)) = Gorenstein 6.5.1 + 8.2.11**。BG 本文は **statement + G 引用のみで証明を書かない**。
- **Isaacs FGT は Glauberman Z(J)-定理を明示的に省く** (p.217 verbatim)。⇒ CLAUDE.md「BG の G 引用 → Isaacs 読み替え」方針が **Thm 6.2 で破綻**(Isaacs に対応物なし)。
- **解決 = BG App.A + App.B(Puig の L(S))の自己完結ルート**。BG が Gorenstein 依存を断つために用意した代替で、**B.4 は Isaacs 本人の未公刊証明**。
- **依存閉包の真のゲートは A.4(b)(= Thm 6.1)と A.4(c)(A.5/B.4 が要する)の 2 つだけ**。両者は Gorenstein §6.5 の special case で、**最深部 = SL(2,p) 表現論(Dickson 2.8.4 / G 3.8.1)は repo に既にある**(`gl2_pSubgroup_centralizes_of_normalizes` = Isaacs Lem 7.3)。A.2/A.3/A.4(a) は直接構築すれば**迂回可**。
- **J → L(S) 大域置換は通る**(§8/§9 精査済)。M は J で定義されておらず「N_G(Z(J(P)))=M」は導出的。App.B(B.1(f)/B.2/B.4)が J の使用性質を**設計通り**ミラーする。
- **2026-05-23 wave1 監査の「App.B + Thm A.5 を Phase 2a でスキップ推奨」は、no-Gorenstein 方針下では誤り**。App.B は 6.2 代替の本線で必須。本 doc で撤回。

## 1. 問題: 6.1/6.2 は深く、Isaacs に無い

| BG | = | 完全証明の所在 | BG での扱い |
|---|---|---|---|
| **Thm 6.1** (G solvable odd, S∈Syl_p ⇒ `O_{p',p}(G)` が S の全 abelian normal を含む) | Hall-Higman | Gorenstein **6.5.2** | statement + 引用のみ |
| **Thm 6.2** (G solvable odd, S∈Syl_p ⇒ `Z(J(S))·O_{p'}(G) ⊴ G`) | Glauberman Z(J) | Gorenstein **6.5.1 + 8.2.11** | statement + 引用のみ |

**Isaacs FGT (p.217, mmd L3961) verbatim**: *"Bender used Glauberman's Z(J)-theorem, which we have decided not to include in this book. Instead, we appeal to the normal-J theorem."* 索引にも "Glauberman Z(J)-theorem, 217"。

⇒ repo の `OddOrder.Isaacs.Ch07.normal_J` は **Isaacs Thm 7.6(normal-J、仮説 `O_{p'}=1` ∧ `P=C_G(Z(P))` ⇒ `J(P)⊴G`)**で、Isaacs はこれを **Thompson normal p-complement (7.1) と Burnside p^a q^b (7.8) の補題**として使う。**一般 Z(J)(任意 S・`P=C_G(Z(P))` 不要)とは別物**で、`P=C_G(Z(P))` ギャップは O_{p'}-商簡約では埋まらない。Isaacs 7.6 Step 1 が与えるのは `Z(P) ⊆ O_p`(特定の1つの abelian)だけで 6.1 の一般形ではない。

**6.1 の奇数位数仮定は本質的**: p=2 では反例(S_4, p=2: D_8 の非-V_4 Klein-4 が O_{2',2}=V_4 に入らない)。p-stability(p 奇で SL(2,p) 障害が消える)が効いている。

## 2. 解決: BG App.A + App.B(Puig L(S))の自己完結ルート

BG App.A 序文 (L4452): 6.1/6.2 を "p-stability で得る、J(S) の代わりに別の characteristic subgroup を使い奇数位数に限れば短い証明"。App.B 序文 (L4521): "result of L. Puig … using **a short, unpublished proof of I. M. Isaacs**"。

- **A.4(b) ≡ Thm 6.1** (BG L4486 "Theorem A.4(b) is just Theorem 6.1")。
- **B.4(a) = Thm 6.2 の代替** (BG L4691 verbatim "Theorem B.4(a) serves as a substitute for Theorem 6.2 of this work")。

Puig の L(S):`X → Y :⟺ Y は X に正規化される abelian 部分群で生成`、`L_G(X)` = 最大の Y、`L_n` 再帰、`L(G)=∩L_{2n+1}`、`L_*(G)=∪L_{2n}`。J(S) と違い **S≠1 で L(S)≠1**(B.1(f))。

## 3. 依存閉包(各証明が事足りているかの精査結果)

### App.B (B.1-B.4): 完全な証明が BG にあり、ほぼ満たせる

| 結果 | BG 証明 | 依存 | 判定 |
|---|---|---|---|
| **B.1** L_i(G) の性質(a-g) | 完全記述 | (f) のみ G 5.3.12 (= Isaacs **1D.10**: p群の極大 abelian normal は self-centralizing, 可証) | ✓ 小補題1件 |
| **B.2** `H⊇L(G) ⇒ L(G)=L(H)` | 完全記述(帰納) | B.1 + 定義のみ | ✓ 完全自己完結 |
| **B.3** `L_*(S)⊆L_*(T)⊆L(T)⊆L(S)` | 完全記述(帰納) | B.1(f), **A.5** | ✓ A.5 待ち |
| **B.4** Puig (= 6.2 代替) | 完全記述(Step 1-4) | **A.5** + G 6.3.1(iv)(= repo `oPiCore_quotient_self_eq_bot` ✓)+ Frattini(repo ✓) | ✓ A.5 待ち |

→ **App.B の実質依存は A.5 のみ**。

### App.A: A.1/A.5 は完備、A.2/A.3/A.4 は BG 未記述

| 結果 | BG での証明 | 判定 |
|---|---|---|
| **A.1** 2-dim irreducible odd ⇒ p∤\|G\| | 完全(BG 2.6〔repo S02 ✓〕+「irreducible の正規 p部分群は自明」= p-group fixed vector〔repo `PGroupFixedVector`〕) | ✓ |
| **A.2** | 「Gorenstein 3.8.1 の証明を p.105 dim-2 まで辿れ」のみ | ⚠️ 未記述(SL(2,p) dim-2 reduction) |
| **A.3** | 「G §3.8 p.109 まで A.2 で置換し辿れ」+ p-stable の定義自体が G 由来 | ⚠️ 未記述 |
| **A.4(a/b/c)** | 「G §6.5.1-6.5.3 を A.3 で置換し we obtain」のみ | ⚠️ 未記述。A.4(b)=Thm 6.1 |
| **A.5** | **完全記述**(A.4(c) + BG Prop 1.8〔repo S01 `burnside_operator` ✓〕+ **Prop 1.15(b)**〔要確認〕) | ✓ A.4(c) 待ち |

→ チェーンは **B.4 → A.5 → A.4(c)** で底打ち。

### 真のゲート = A.4(b) + A.4(c)、最深部は済

- **A.4(c)** (`O_{p'}(G)P⊴G`, A≤N_G(P) p-subgroup, `[P,A,A]=1` ⇒ `AC_G(P)/C_G(P) ⊆ O_p(N_G(P)/C_G(P))`) は **A.5/B.4 が要する**。
- **A.4(b)** (= Thm 6.1) は **§7/§8 本文が独立に引用**(後述§4)。A.4(c) からは出ない(Gorenstein §6.5 の別 special case)。
- **A.4(c) は Isaacs 7.5 の系ではない**(兄弟定理):
  - 7.5 (normal-P): P∈Syl_p, faithful 作用 V, `|V:C_V(P)|≤p` ⇒ P⊴G。主役 P が外部加群に作用、結論は大域正規性。
  - A.4(c): A が P に二次作用 `[P,A,A]=1`、結論は O_p(N/C) 局所化。
  - 共通核 = **Lemma 7.3 (GL(2,p))**。両証明とも rank-2/GL(2,p) に落として 7.3 を適用。
- **最深部 = Dickson 2.8.4 / Gorenstein 3.8.1(SL(2,p) 表現論、BG が "long, complicated" と呼び A.1/A.2 で迂回)は repo に既証**: `OddOrder.Isaacs.Ch07.gl2_pSubgroup_centralizes_of_normalizes`(S7A1:1269、Isaacs Lem 7.3)。
- ⇒ A.4(b)/(c) は「**新規 reduction を組んで 7.3 を適用**」する bounded な作業(7.5 の repo 証明と同程度の reduction)。A.2/A.3/A.4(a) は直接構築するため**不要**(BG の §3.8→§6.5 経路を迂回)。
- **鉱脈**: repo §7B `normal_J` 証明(Step 1-7 で `J(P)≤O_p`)が、abelian A∈E(P) の `[H∩L,A]⊆U` 型と 7.5 を使うので、A.4(c) の stability-lift 部品が再利用できる可能性。

## 4. J → L(S) 大域置換の検証(§8/§9 精査)

**M は J で定義されていない**: §7 L2135 で `𝓜 = G の極大部分群全体`、`𝓤 = {真部分群 H : 𝓜(H) 単元}`。M ∈ 𝓜。「N_G(Z(J(P))) = M」(L2456 等)は **導出**(Z(J(P))⊴M〔6.2〕⇒ M⊆N_G(Z(J(P)))、M 極大 + N_G(Z(J(P))) 真部分群 ⇒ =M)。⇒ **定義的障害なし**、L で同論法。

| §8/§9 で使う J 性質 | 箇所 | L 対応 | 出所 |
|---|---|---|---|
| `Z(J(P)) ⊴ M` / `O_{p'}(M)Z(J(P))⊴M` | L2456, 2480, 2511 | `Z(L(P)) ⊴ M` | **B.4** ✓ |
| `Z(J(P)) char P` ⇒ N_G(P)⊆N_G(Z(J(P))) | L2456, 2515 | `L(P) char P`(canonical = Aut(P)-同変)⇒ Z(L(P)) char P | B.1/定義 ✓ |
| `Z(J(P)) ≠ 1` ⇒ N_G(Z(J(P))) 真 | L2456, 2482 | `Z(L(P)) ⊇ Z(P) ≠ 1` | **B.1(f)** ✓ |
| `Z(J(R))⊴H`(Sylow R of H∩M), J(R) char R | L2480, 2482 | Z(L(R))⊴H, L(R) char R | B.4 + B.1 ✓ |
| `J(P)⊆Q⊆P ⇒ J(P)=J(Q)`(Isaacs **7.2**、Sylow 移動) | Sylow 遷移 | `L(P)⊆Q⊆P ⇒ L(P)=L(Q)` | **B.2** ✓ |

**BG はこれを意図設計**: Thm 6.2 直後 Remark が "for S≠1, L(S)≠1 (Lemma B.1(f))" と P3 を名指し、L5014 が "substitute L(P) for J(P) throughout" と明示。

- **6.1(A.4(b))の使用は J→L と直交**: §7 L2275/L2291、§8 L2452「By Theorem 6.1, A ⊆ F」は `O_{p',p}/F(M)` への abelian normal 包含で J/L 無関係。置換は **6.2 ステップに局所化**され clean。**6.1 は独立に必要なまま**。
- 置換は **§8-§16 + App.C 全域**(L5014/5030 も Z(J) 使用、BG が L で sanction 済)。大域 formalize 方針の確定要。

## 5. 旧ノートの訂正(本 doc で確定)

- **`bg_phase2a_wave1_audit_2026_05_23.md` の「App.B + Thm A.5 を Phase 2a でスキップ可(FT-orphan)」は撤回**。FT-citation-orphan の観察自体は正しいが、**App.B が "Gorenstein 依存を断つための 6.2 自己完結代替" である役割を見落とした**。no-Gorenstein 方針下では App.A+B は 6.1/6.2 への**唯一の自己完結ルート**で必須。
- **`appA_pstability.md` の「A.4(b) は Isaacs 7.6 import 推奨(選択肢1)」は訂正**: Isaacs は §6.5/Z(J) を持たず、A.4(b)/(c) は 7.3 ベースの新規 reduction が要る。
- `phase2_cross_refs.md` L34(App.B「skip 推奨」)も反転。

## 6. 残課題 / 次の実装(issues/ 化候補)

1. **A.4(b)(=Thm 6.1)reduction**: 7.3 を核に、abelian normal A → rank-2 chief factor → 7.3 → O_{p',p} 包含。§7/§8 本文が独立使用。
2. **A.4(c) reduction**: 7.3 を核に、二次作用 [P,A,A]=1 → rank-2 → 7.3 → stability-lift → O_p(N/C)。A.5/B.4 の前提。
3. **Prop 1.15(b)** を repo S01 で確認/実装(A.5 が使用; Prop 1.8 は ✓)。
4. **L(S) char S** 形式補題(canonical 構成の Aut(S)-同変性、`thompsonJ` char 補題と同型)。
5. **App.A**: A.1(BG 2.6 + PGroupFixedVector)、A.5(written、A.4(c)+Prop 1.8/1.15(b))。
6. **App.B**: B.1(+ G 5.3.12=Isaacs 1D.10)、B.2、B.3(A.5)、B.4(A.5 + oPiCore_quotient + Frattini)。
7. **§8-§16 を L(S) で formalize**(J→L 大域置換、本 doc §4 で健全性確認済)。

着手順: **7.3 は済 → (1)+(2) A.4(b)/(c) → (3)(4) 小補題 → A.5 → App.B(B.1-B.4) → §8-§16 を L(S) 化**。これで §6 の Gorenstein §3.8/§6.5/8.2.11 依存を完全に捨てられる。

## 関連ノート

- [`s06_additional.md`](../bg/s06_additional.md): §6 per-section(reduced-case 実装済 + 難度注)
- [`appA_pstability.md`](../bg/appA_pstability.md): App.A per-section(本 doc で訂正)
- [`appB_puig.md`](../bg/appB_puig.md): App.B per-section(本 doc で skip 撤回)
- [`bg_phase2a_wave1_audit_2026_05_23.md`](bg_phase2a_wave1_audit_2026_05_23.md): wave1 監査(本 doc で skip-App.B を反転)
- [`phase2_cross_refs.md`](phase2_cross_refs.md): 3 冊クロス参照
- repo: `OddOrder/Isaacs/Ch07_ThompsonSubgroup/{S7A1_JpGL2p,S7A2_NormalPThm75,S7B1_NormalJ,S7B2_NormalJ_PComplement}.lean`(7.2/7.3/7.5/7.6/normal_J)、`OddOrder/BG/Ch1_Preliminary/S06_Additional.lean`(reduced-case)
