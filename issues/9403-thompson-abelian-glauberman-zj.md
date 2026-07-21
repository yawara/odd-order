---
id: 9403
slug: thompson-abelian-glauberman-zj
title: "CLAIM: abelian Thompson subgroup J_a(P) + Gorenstein Ch.8 §2 (Glauberman ZJ) の移植"
created: 2026-07-21
---

# CLAIM: abelian Thompson subgroup J_a(P) + Gorenstein Ch.8 §2 (Glauberman ZJ) の移植

**claim 主体**: lane c。**consumer**: issue 3024 → 3017 (BG Thm 6.2 literal J(S) 一般形)。
親 issue = 3024 (規模見積・リスク・Gorenstein 参照根拠はそちらが正本)。

## 背景 — 設計判断 (2026-07-21 確定、lane c)

BG Thm 6.2 の literal `J(S)` は **Gorenstein 版 Thompson subgroup**:
`A(P)` = **abelian** 部分群のうち**最大位数**のもの、`J(P) = ⟨A(P)⟩`
(G Ch.8 §2, mmd L5443-5449)。根拠:

- BG は `J(P)` を自前定義しない (記号表 L8611 "Thompson subgroup of P, p.49" の初出 =
  Thm 6.2 自身、証明 = "**G**, Thm 6.5.1 / 8.2.11" 引用のみ)。⟹ BG の J = Gorenstein の J。
- Gorenstein §2 の全機構は **Lemma 2.1 (`A ∈ A(P) ⟹ A = C_P(A)`)** に乗る。証明は
  「`x ∈ C_P(A)` なら `⟨A, x⟩` が abelian でより大きい」— **全 abelian 部分群中の最大性**が
  本質で、elementary 版 (`⟨A,x⟩` が elementary と限らない) では**偽**。
- repo 既存 `Subgroup.thompsonJ` (`GroupTheory/ThompsonSubgroup.lean:64-72`) は
  **Isaacs/Aschbacher 版 (elementary abelian, 最大位数)** で別物。abelian 版は repo に無い
  (grep `maxAbelian|AbelianOfMaxOrder|thompsonJAbelian` 0 件、issue 3024 の事前検索とも整合)。

⟹ **elementary 版への adapt は不可能 (Lemma 2.1 が偽)**。abelian 版 `J_a` を新設して
Gorenstein Ch.8 §2 (pp. 270-279, mmd L5431-5622) を忠実移植する。

### ⚠ 副産物: S06_Thm62JS の hZJ は BG literal とミスマッチ

`S06_Thm62JS.lean:71` の `hZJ` は elementary `Subgroup.thompsonJ` で符号化されているが、
BG Thm 6.2 の J は Gorenstein 版。⟹ J_a 完成後、`hZJ`・結論とも J_a 形へ**言い直しが必要**
(reduction の証明構造は共変性 lemma を J_a 版に差し替えれば再利用可)。3017/3024 側で処理。

## やること

- [ ] 新 leaf `OddOrder/GroupTheory/ThompsonSubgroupAbelian.lean`:
      `Subgroup.maxAbelianIn P` (`p` 不要 — Gorenstein A(P) は素数に言及しない) +
      `Subgroup.thompsonJAbelian P` + G Lem 2.1 (`A = C_P(A)`, `Z(P) ≤ A`) +
      Lem 2.2 (a)-(d) + Lem 2.3 (`B ⊴ A ⟺ [B,A,A]=1`)。同 commit で `OddOrder.lean` 配線。
- [ ] G Thm 2.4 (Thompson: `M = [x,A]` abelian ⟹ `M·C_A(M) ∈ A(P)`)。
- [ ] G Thm 2.5 (Thompson Replacement) / 2.6 / Thm 2.7 (Glauberman Replacement)。
- [ ] G Lem 2.8 (`[B,A;i]` 下降列) / 2.9 / 2.10 (`B ⊓ Z(J(P)) ⊴ G`) / 2.11
      (**Glauberman ZJ**: p odd, p-constrained + p-stable, `O_{p'}(G)=1` ⟹ `Z(J(P)) ⊴ G`
      — 正確な仮定は原文 pp. 277-279 で着手時確定)。
- [ ] p-stability / p-constraint の供給: repo 既存 `BG.AppA.IsPStable`
      (`AppA_PStability.lean:127`) + `Isaacs.Ch07.centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot`
      と接続 (定義のずれは着手時に照合)。

## 進捗 2026-07-21 (lane c)

- ✅ 基盤 leaf `ThompsonSubgroupAbelian.lean` (commit 540fcdfb2): `maxAbelianIn` /
  `thompsonJAbelian` + **G Lem 2.1** (`eq_inf_centralizer_of_mem_maxAbelianIn`) +
  系 `Z(P) ≤ A` + **G Lem 2.3** (normalize ⟺ `⁅⁅B,A⁆,A⁆ = ⊥`)。
- ✅ **G Lem 2.2 (a)-(d)** (commit 58d7081da): `maxAbelianIn_subset_of_le` /
  `thompsonJAbelian_le_of_le` / `thompsonJAbelian_eq_of_le_of_le` /
  `thompsonJAbelian_map_of_injective` / conj 版 / characteristic 2 instance。
  sibling (elementary 版) の骨格ミラー + mathlib `map_isMulCommutative` 系で転送。

## ✅ Thm 2.4 (Thompson) 完全証明 (2026-07-21, commits fa5e84f27 / 44b313b65 / fa9cc3b05)

`thompson_mem_maxAbelianIn` sorry-free。計画どおり 6 部品 + G Lem 2.5(i) 対称性
(`commutatorElement_inv_rotate` — G 原文の `[x,G]` abelian 仮定を「使う 2 元の可換性」
まで弱めて `x⁻¹`-共役の観察で `[x^m,y]` 帰納を回避)。積公式は
`QuotientGroup.quotientInfEquivProdNormalizerQuotient` (ambient 正規性不要) で、
coset 単射は `Quotient.out` 経由 (well-definedness 不要)。

### ✅ Thm 2.5 (Thompson Replacement) + Thm 2.6 完全証明 (2026-07-21, commits 30e5eb6a6 / 1b332245b)

`thompson_replacement` / `exists_mem_maxAbelianIn_normalizer` sorry-free。
G Thm 2.6.4 の対応物 = `OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial`
(import 追加; GroupTheory→Ch01 は既存前例)。normalizer 3 補題
(`mem_normalizer_of_forall_commutatorElement_mem` / `conj_mem_normalizer` +
`mem_normalizer_normalizer` / `mem_normalizer_inf`) を新設。leaf = 842 行。

### 次 = Thm 2.7 (Glauberman Replacement) — mmd L5522 以降

`P = AB` 簡約 (Lem 2.2 使用) → `[B,A;i]` 帰納定義 → **Lem 2.8** (i)(ii)(iii) →
Case 1 / Case 2 (Thm 2.2.3(i) Hall–Witt + Lem 2.2.4(iii)/2.2.5(ii))。
class ≤ 2 の `B` が対象で p odd が効く。Lem 2.8 は独立の帰納補題なので先に立てる。

#### ✅ Lem 2.8 (i)(ii)(iii) 完結 (2026-07-21, commits c45ecf83b / 777668e24 / 2f65b5119)

- (i) `lowerCentralSeries_sup_eq_iterCommutator_sup` — sup-形直接証明 (quotient 不要;
  基底 `P' = ⁅B,⊤⁆` は正確な等式 `commutator_top_top_eq_commutator_left`)。
- (iii) `iterCommutator_min_abelian_le_two` — weight bound = 既存
  `Isaacs.Ch04.commutator_lowerCentralSeries_le_subgroup` (Mann.lean)。
- leaf = 1117 行 ⟹ **Thm 2.7 以降は新 sibling leaf
  `OddOrder/GroupTheory/GlaubermanReplacement.lean`** (ThompsonSubgroupAbelian を
  import、OddOrder.lean 配線を忘れない)。
- Thm 2.7 の入口 (mmd L5564-5580): P = AB 簡約 (`thompsonJAbelian_le_of_le` +
  `maxAbelianIn_subset_of_le` + Lem 2.1 で `Z(J(P)) ≤ A` ⟹ `B' ≤ Z(J(Q))` 継承) →
  n = 最小 abelian 指数で Case 1 (`[B,A;n+1] ≠ 1`: r 最小の `[B,A;r]=1`、
  `x ∈ [B,A;r-3]` で `A` が `[x,A]` を中心化しないものを取る → M = [x,A] abelian →
  Thm 2.4; A∩B の中心化は three-subgroup lemma `[B,A∩B,A]…`; `A* ≤ N(A)` は
  `[A*,A,A] ≤ [B,A;r] = 1` + **Lem 2.3**) / Case 2 (`[B,A;n+1] = 1`: Lem 2.8(iii)
  で n = 2、Hall–Witt (G Thm 2.2.3(i)) + `B' ≤ Z(P)` で `[x,A]` が全 x ∈ B で
  abelian に落ちる — **p odd はこの Case 2 の (2.13)-(2.15) で使用**、原文精読要)。

#### ✅ Thm 2.7 core 完全証明 (2026-07-21, commits d7053573f / 789b5cace / 31976f6af)

`glauberman_replacement_aux` (GlaubermanReplacement.lean, 505 行) sorry-free:
- wrap-up `replacement_of_elementCommutator` (three-subgroup + Lem 2.3 +
  `commutator_sup_le_of_centralizer`)
- Case 1 (`glauberman_replacement_case_one`): r = Nat.find 最小 ⊥ 添字
- Case 2: **Hall–Witt (2.11)-(2.14) は `hall_witt_identity` (sympy で形確定 →
  group tactic 検証) + B'-中心性で `z = ⁅⁅u⁻¹,⁅x,v⁆⁆,x⁆` の一撃形に潰した**
  (`commutator_commutator_eq_of_normal`)。(2.15)-(2.16) は exact 変形
  (`commutatorElement_inv_swap_eq`) + 商 G/B' での `commutatorElement_inv_rotate`。
  (2.19) = z² = 1 + hodd (`∀ g, g² = 1 → g = 1` 形で受理)。
- core は n := Nat.find (最小 abelian 正添字) で case 分岐。

#### ✅ Thm 2.10 (Glauberman) 完全証明 (2026-07-21, commits 7301fdd22 / 74547340e / ed87b2fbe)

`inf_zCenter_thompsonJAbelian_normal` sorry-free / **axiom-clean 確認済**
(propext, Classical.choice, Quot.sound)。GlaubermanZJ.lean ≈ 620 行。

- step (c) 後半 `le_sSupNormalNormalizing_of_isPStableOp`: C=C_G(B) ≤ L (最大性) +
  IsPStableOp + `map_opCore_le_opCore_of_surjective` (O_p の全射転送、新規) で
  AL/L ≤ O_p(G/L) = ⊥ ⟹ A ≤ L。
- step (d) `normalClosure_le_zCenter_thompsonJAbelian_inf`: A が A(P⊓L) の witness →
  J_a(P⊓L) ≤ J_a(P)、W ≤ X、Frattini + `normalClosure_le_of_sup_normalizer_eq_top`
  (g = n·l 分解の一般補題、新規) で B ≤ X。副産物: ThompsonSubgroupAbelian に
  `zCenter_thompsonJAbelian_le_of_mem_maxAbelianIn` (Lem 2.1 系 2、
  glauberman_replacement の local have を public 抽出) +
  `isMulCommutative_centralizer_inf`。
- 組立 `inf_zCenter_thompsonJAbelian_normal_of_card_le`: |B| ≤ n 帰納。
  B₁ := normalClosure(Z⊓B) < B なら IH 転送 / B₁ = B なら B' < B に IH
  (`commutator_lt_of_isPGroup_ne_bot`、新規: 冪零→可解→commutator_lt_of_ne_bot の
  subtype 転送) → step (a) → J_a(P) ≤ P⊓L なら step (b) で結論 / さもなくば
  (c)(d)(e) で矛盾 (A₁ ⊄ L を |A₁⊓B| 最大選択、Thompson replacement、X ≤ A*)。

#### 次 = Thm 2.11 (ZJ 定理) — 原文 pdftotext L15347-15363 精読済

1. **O_p'(G) = 1 ケース** (BG 側 consumer が使う形): `Z(J_a(P)) ⊴ G`。
   部品 = **G Thm 8.1.3**「p-constrained + O_p'(G)=1 ⟹ P の正規 abelian 部分群
   A ≤ O_p(G)」(repo 対応 = Isaacs Ch07
   `centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot` 系を実測して接続;
   p-constraint の repo 形も同時に確定)。Z(J_a(P)) ⊴ P abelian
   (`le_normalizer_zCenter_thompsonJAbelian` + `isMulCommutative_centralizer_inf`)
   ⟹ Z ≤ O_p(G) =: B ⟹ Thm 2.10 で Z = Z ⊓ B ⊴ G。
2. **一般形** `G = O_p'(G)·N_G(Z(J_a(P)))`: G/O_p' への簡約 (G Thm 1.1(ii)+1.3.7)。
   quotient を跨ぐ J_a 転送 (`thompsonJAbelian_map_of_injective` は単射版のみ —
   O_p' が p'-群なので P ≅ P·O_p'/O_p' の同型経由で転送) が plumbing の主コスト。

**残り (旧計画メモ; 原文 pdftotext L15282-15355; mmd は p.298 が MISSING)**:

1. **subgroup-level Thm 2.7 wrapper**: 仮定 = P ≤ N(B) (B ⊴ P), hclass2 :
   ⁅B,B⁆ ≤ centralizer B (class ≤ 2), hBZJ : ⁅B,B⁆ ≤ Z(J_a(P))-encoding,
   A ∈ A(P), ¬B ≤ N(A), P p-群 odd。手順: Q := A ⊔ B; **B' ≤ Z(Q)** は
   Z(J_a(P)) ≤ A (centralizer_inf_le_of_mem_maxAbelianIn = Lem 2.1 系) ⟹
   B' ≤ A abelian + hclass2 ⟹ Q = A⊔B ≤ centralizer B'。core を ↥Q に
   instantiate。**要 refactor**: thompsonJAbelian_map_of_injective の証明内
   key_map/key_comap を public lemma (maxAbelianIn の map/comap transport) に
   抽出。A(⊤_Q) → A(Q) → A(P) の引き上げは maxAbelianIn_subset_of_le (A₀ := A)。
   inf/lt/normalizer の subgroupOf transport が残りの plumbing。
2. **Thm 2.9** (2.7 の系、Thm 2.6 と同型): |A∩B| 最大の A ∈ A(P) を選ぶと
   B ≤ N(A) (さもなくば wrapper で真増加)。
3. **Thm 2.10** (Glauberman、帰納の主定理): B ⊴ G nontrivial p-部分群、G p-stable、
   P ∈ Syl_p ⟹ B ∩ Z(J(P)) ⊴ G。最小位数反例 B で:
   (a) B = (Z∩B) の正規閉包 (最小性); (2.20) 共役帳簿で B' ≤ Z∩B' ⟹ B' ≤ Z、
   B' ≤ Z(B) ⟹ cl(B) ≤ 2 + B' ≤ Z(J(P)) = 2.7/2.9 の仮定成立。
   (b) L := Z∩B を正規化する最大正規部分群; P∩L ∈ Syl_p(L) (Sylow-of-normal =
   G Thm 1.3.8); Frattini (G Thm 1.3.7) G = L·N_G(J(P∩L))。
   J(P) ≤ P∩L なら J(P) = J(P∩L) (Lem 2.2(ii) = thompsonJAbelian_eq_of_le_of_le)
   で N が Z∩B を正規化し ⊴ G 矛盾。ゆえ J(P) ⊄ L∩P。
   (c) Thm 2.9 + Lem 2.3 で [B,A,A] = 1 なる A ∈ A(P); **p-stability** で
   AC/C ≤ O_p(G/C) (C = C_G(B)); C ≤ L (最大性); O_p(G/L) = 1 (K 逆像、
   P∩K が Z,B を正規化 ⟹ ≤ L) ⟹ A ≤ L。
   (d) J(P∩L) ≤ J(P) (Lem 2.2(i)); Z ≤ A ≤ J(P∩L) ⟹ Z∩B ≤ X := Z(J(P∩L));
   Frattini G = L·N_G(X); B (= 正規閉包) ≤ X ⟹ **B abelian**。
   (e) A₁ ∈ A(P), A₁ ⊄ L (J(P) ⊄ L∩P から); [B,A₁,A₁] ≠ 1 (さもなくば (c) の
   論法で A₁ ≤ L); |A₁∩B| 最大選択; Lem 2.3 で B not ≤ N(A₁) ⟹
   **Thompson replacement (Thm 2.5、B abelian!)** で A*; 最大性 ⟹ A* ≤ P∩L ⟹
   X ≤ A* (Lem 2.1 系) ⟹ [B,A₁,A₁] ≤ [A*,A₁,A₁] = 1 矛盾。∎
   ⚠ p-stability の repo 形 (BG.AppA.IsPStable) と G の定義 (B ⊴ G, [B,A,A]=1 ⟹
   AC/C ≤ O_p(G/C)) の照合が必要。Frattini argument / Sylow-of-normal は repo 実測。
4. **Thm 2.11 (ZJ)**: G p-constrained + p-stable, p odd ⟹
   G = O_p'(G)·N_G(Z(J(P)))、特に O_p'(G) = 1 なら Z(J(P)) ⊴ G。証明 =
   O_p' 商への簡約 (G Thm 1.1(ii)+1.3.7) + Z(J(P)) ≤ O_p(G) (p-constrained、
   normal abelian in P ⟹ ≤ O_p; G Thm 1.3 = repo 対応要実測) + Thm 2.10
   (B := O_p(G))。
5. 3024 側: S06_Thm62JS の hZJ を J_a 形に言い直して discharge (3017 close)。

#### (参考) Thm 2.7 の完全分解 (2026-07-21 原文精読済 mmd L5560-5596)

**core 定理** (P = AB 簡約後、型レベル): 仮定 `⊤ = B ⊔ A`, `B ⊴ G`,
`hB' : ⁅B,B⁆ ≤ center G`, `hA : A ∈ maxAbelianIn ⊤`, `hBnA : ¬ B ≤ N(A)`,
`[Finite G]`, `[Group.IsNilpotent G]`, `hodd : Odd (Nat.card G)` (p odd の代替、
x² = 1 ⟹ x = 1 に使用)。結論 `∃ A* ∈ maxAbelianIn ⊤, A ⊓ B < A* ⊓ B ∧ A* ≤ N(A)`。

- **n**: 最小の正整数で `[B,A;n]` abelian (well-def = iterCommutator_eq_bot_of_
  isNilpotent_ambient で eventually ⊥ + Nat.find)。
- **Case 1** (`[B,A;n+1] ≠ ⊥`): r := 最小 `[B,A;r] = ⊥` (r ≥ n+2 ≥ 3)。
  「∃ x ∈ [B,A;r-3], ¬ A centralizes [x,A]」: さもなくば A が [B,A;r-2] の全生成元
  ⁅x,a⁆ を中心化 ⟹ [B,A;r-1] = ⊥ ✗ r 最小性 (⁅X,A⁆ = closure of ⁅x,a⁆ 生成元)。
  M := elementCommutator x A ≤ [B,A;r-2] ≤ [B,A;n] abelian → **Thm 2.4** で
  A* = M ⊔ C_A(M) ∈ A(⊤)。
- **Case 2** (`[B,A;n+1] = ⊥`): Lem 2.8(iii) で n ≤ 2; [B,A;2] ≠ ⊥ (**Lem 2.3** の
  対偶、B not ≤ N(A)) ⟹ n = 2 ⟹ `[B,A;3] = ⊥`。
  **核心: ∀ x ∈ B, [x,A] abelian** — Hall–Witt (G Thm 2.2.3(i)) を (x, u⁻¹, w = [x,v])
  で: 各因子が B' ≤ Z 込みで central 化し (2.12) `[x,u,w][u⁻¹,w⁻¹,x] = 1`;
  (2.13)-(2.16) で mod B' 変形 (G Lem 2.2.5(ii) = 「[x,y] が x,y と可換 ⟹
  [x,y]⁻¹ = [x⁻¹,y] = [x,y⁻¹]」の鏡映版が新規に必要; 2.5(i) は形式化済
  commutatorElement_inv_rotate) ⟹ (2.17)(2.18) 対称形 ⟹ `[[x,u],[x,v]]² = 1`
  ⟹ **hodd で = 1**。x の選択は Case 1 同型 ([B,A] が A を中心化しない)。
- **共通 wrap-up** (両 case): (α) A∩B ≤ C_A(M): three-subgroup
  (mathlib `commutator_commutator_eq_bot_of_rotate`): `⁅⁅B,A∩B⁆,A⁆ ≤ ⁅⁅B,B⁆,A⁆ =
  ⊥` (B' central) + `⁅⁅A∩B,A⁆,A⁆ ≤ ⁅⁅A,A⁆,A⁆ = ⊥` (A abelian) ⟹
  `⁅⁅A,B⁆,A∩B⁆ = ⊥` ⟹ A∩B centralizes ⁅B,A⁆ ⊇ M。
  (β) 真性 witness: M ⊄ A (A abelian が M を中心化することになり x-選択に矛盾)。
  (γ) **A* ≤ N(A)**: `⁅A*,A⁆ ≤ [B,A;r-1]` (Case 2 は [B,A;2]) — 分解 g = c·m
  (`coe_mul_of_left_le_normalizer_right`、C は M を中心化) で ⁅cm,a⁆ = c⁅m,a⁆c⁻¹
  (⁅c,a⁆=1、C ≤ A abelian)、⁅m,a⁆ ∈ ⁅[B,A;r-2],A⁆ = [B,A;r-1] は **A-正規**
  (le_normalizer_iterCommutator) ゆえ c-共役で閉じる ⟹
  `⁅⁅A*,A⁆,A⁆ ≤ [B,A;r] = ⊥` ⟹ **Lem 2.3** で A* ≤ N(A)。
  ⟹ helper `commutator_sup_le_of_centralizer` として一般化して実装する。
- **wrapper** (subgroup-level P): Q := A ⊔ B ≤ P で core を ↥Q に instantiate。
  A(Q) ⊆ A(P) (maxAbelianIn_subset_of_le、A₀ := A)。B' ≤ Z(J_a(P)) 仮定からの
  `B' ≤ Z(Q)` 導出: Z(J_a(P)) ≤ A (Lem 2.1: Z(J) centralizes A ≤ J_a ⟹
  ∈ ⊤ ⊓ centralizer A = A) ⟹ B' ≤ A ⟹ A centralizes B' (A abelian)、
  B centralizes B' (class ≤ 2 = hB'B : ⁅B,B⁆ ≤ centralizer B) ⟹ Q = A ⊔ B ≤
  centralizer B' ⟹ B' ≤ Z(Q)。type-level への transport (subgroupOf 往復) が
  plumbing の主コスト — maxAbelianIn の subtype-transport は
  thompsonJAbelian_map_of_injective の key_comap/key_map パターンを流用。

#### ✅ (旧記録) Lem 2.8(ii) + [B,A;i] 部品 (2026-07-21): `[B,A;i]` = 既存
`Isaacs.Ch04.iterCommutator B A i` を再利用。`le_normalizer_commutator_right` /
`le_normalizer_iterCommutator` / `iterCommutator_succ_le` (= (ii)) /
`iterCommutator_le_of_le` / `iterCommutator_le_base` sorry-free。

#### Lem 2.8(i)/(iii) の設計メモ (mmd L5536-5560 精読済)

- **型レベルで定式化** (ambient 群 = Gorenstein の P): 仮定
  `B A : Subgroup G`, `hsup : B ⊔ A = ⊤`, `[B.Normal]`, `hB' : ⁅B,B⁆ ≤ center G`,
  `hAcomm : IsMulCommutative A`, `[Finite G]` (+(iii) では `Group.IsNilpotent G`)。
  Thm 2.7 の適用は `P = AB` 簡約後に `↥Q` へ instantiate。
- **(i) の mathlib 番地換え**: G の `L_i(P)` = mathlib `lowerCentralSeries G (i-1)`。
  statement は mod-B' を sup で符号化:
  `∀ i ≥ 1, lowerCentralSeries G i ⊔ ⁅B,B⁆ = iterCommutator B A (i-1) ⊔ ⁅B,B⁆`。
  証明: B' 商 (⁅B,B⁆ ≤ center ⟹ normal) に落として B abelian ケースに帰着 —
  (a) `L_i ≤ B` (i≥1、P/B ≅ A/(A∩B) abelian)、(b) `[ba,x] = [a,x]` (x ∈ L_i, B abelian
  中心化) ⟹ `L_{i+1} = [L_i, A]`、(c) 基底 `P' = [B,A]` ((2.7): `[ab,x] = [a,x]^b [b,x]`
  + [a,x] ∈ B abelian で (2.8) 加法化 ⟹ P' ⊆ [A,P][B,P]、[B,P] = [B,A]、[A,P] = [A,B])。
  quotient 落としの plumbing が大きければ sup-形のまま直接証明も可 (要調査)。
- **(iii)**: [B,A;n+1] = 1 ⟹ (i) で `L_{n+2} ≤ B' ≤ Z(P)` ⟹ `L_{n+3} = 1`;
  m := ⌊(n+4)/2⌋ ≥ 2, 2m ≥ n+3; **weight bound** `[L_m,L_m] ≤ L_{2m}` (repo:
  Mann.lean:791 の γ 版を実測して使う) ⟹ L_m abelian ⟹ [B,A;m-1] ⊆ L_m·B'
  (B' 中心) abelian ⟹ n の最小性で n ≤ m-1 ≤ n/2+1 ⟹ n ≤ 2、cl(P) ≤ 4。
  n は「[B,A;n] abelian なる最小の正整数」— Lean では Nat.find か明示仮定
  `(hn : IsMulCommutative (iterCommutator B A n)) (hmin : ∀ k, 0 < k → k < n → ¬ ...)`
  の形で受ける (Thm 2.7 側の供給に合わせて決める)。

### (参考) 旧記録: Thm 2.5 の入口

必要な唯一の外部部品 = **G Thm 2.6.4** (冪零群の非自明正規部分群は中心と非自明に交わる;
`B/N ∩ Z(AB/N) ≠ 1` に適用)。repo/mathlib の対応物 (`IsPGroup.center_nontrivial` 系 /
BG Ch1 の正規×中心交わり) を着手時に実測すること。骨格: `N = N_B(A) ⊴ AB`、
`N ⊊ B`、`Z(AB/N) ∩ B/N ≠ 1` から `x ∈ B − N` を取り `M = [x,A] ⊆ N` abelian → 2.4。

## (参考) Thm 2.4 の当初実装計画 (2026-07-21 原文精読済، mmd L5487-5505)

**statement**: `A ∈ A(P)`, `x ∈ P`, `M := ⟨⁅x,a⁆ : a ∈ A⟩` abelian ⟹
`M·C_A(M) ∈ A(P)`。Lean 形:
`M := Subgroup.closure {y | ∃ a ∈ A, y = ⁅x, a⁆}`、結論
`M ⊔ (A ⊓ centralizer M) ∈ maxAbelianIn P`。
⚠ `⁅zpowers x, A⁆` は使わない (`⁅xⁿ,a⁆` 込みで Gorenstein の `[x,A]` と別物)。

**部品** (証明の分解、Gorenstein 順):
1. **可換性**: `M ⊔ C` abelian (M abelian 仮説 + C = C_A(M) ≤ centralizer M + C ≤ A abelian、
   既存 Lem 2.1 の sup パターン再利用)。
2. **対称性 (G Lem 2.2.5(i) 相当)**: A abelian + M abelian ⟹
   `⁅⁅x,u⁆,v⁆ = ⁅⁅x,v⁆,u⁆` (u,v ∈ A)。導出: `⁅x, u*v⁆ = ⁅x,u⁆ * u⁅x,v⁆u⁻¹`
   (free identity、`group` で閉じる) を u*v = v*u の両順で展開し M の可換性で比較。
3. **coset 単射**: `⁅x,u⁆⁻¹⁅x,v⁆ ∈ C_M(A) ⟹ v*u⁻¹ ∈ C_A(M)`
   (Gorenstein の y = [x,vu⁻¹] 計算 + 対称性 2)。⟹ `|A : C_A(M)| ≤ |M : C_M(A)|`。
4. **C ∩ M = C_M(A)**: `C_P(A) = A` (Lem 2.1) から `M ∩ centralizer A ≤ A` ⟹
   `C ⊓ M = A ⊓ M ⊓ centralizer A = C_M(A)` の鎖。
5. **積公式**: `|M ⊔ C| = |M|·|C|/|C ⊓ M|` (C が M を中心化 ⟹ 積が部分群)。
   repo/mathlib の card_sup 系を実測してから選ぶ (AppE `card_centralizer_R₀` に類例)。
6. 3+4+5 を接合して `|M ⊔ C| ≥ |A|` ⟹ maximality で membership。

**⚠ 交換子の慣習**: Gorenstein `[x,y] = x⁻¹y⁻¹xy` = mathlib `⁅x⁻¹,y⁻¹⁆`。
Lean 側は mathlib `⁅x,a⁆ = xax⁻¹a⁻¹` で M を定義し、Gorenstein の計算を `x → x⁻¹`
で鏡映して追う (x は全称なので statement は等価)。2 の対称性 lemma (G Lem 2.5(i),
Ch.2 p.20 mmd L579) の正確な仮定 = 「y,z 可換 + `x y⁻¹ x⁻¹ y` と `x z⁻¹ x⁻¹ z` が可換」
— 後者 2 元は mathlib 記法で `⁅x,y⁻¹⁆`, `⁅x,z⁻¹⁆` そのもの (y⁻¹,z⁻¹ ∈ A ゆえ M の
生成元) なので M abelian から直接出る。G 原文の `[x,G]` abelian 仮定より弱い仮定で足りる
(G 自身の証明がそれしか使っていない; `[x⁻¹,y]=[x^m,y] ∈ [x,G]` の帰納は不要になる)。
element lemma は raw な Commute 仮定 2 つで state し `group` + calc で閉じる。

**Thm 2.5 (Thompson Replacement, mmd L5507-5511)** は 2.4 の系に近い:
`N = N_B(A) ⊴ AB`、`B/N ∩ Z(AB/N) ≠ 1` (G Thm 2.6.4 = 冪零群の正規部分群と中心の交わり;
repo 対応物を実測) から x を取り `M = [x,A] ⊆ N` abelian → 2.4。
**Thm 2.6** (B abelian normal ⟹ ∃A ∈ A(P), B normalizes A): 2.5 + `A ∩ B` 最大選択。

## 完了条件

Glauberman ZJ (G Thm 8.2.11) が J_a で sorry-free / axiom-clean。下流 3024 → 3017
(S06_Thm62JS の hZJ discharge + J_a への statement 修正) が解錠。

## 事前検索 (claim-before-build, 2026-07-21)

- repo: `thompsonJ` = elementary 版のみ (上記)。`replacement` grep は Isaacs 3.31
  Hartley–Turull のみ (3024 実測)。Gorenstein §2 の鎖 (2.1-2.11) は**一つも無い**。
- mathlib: `Thompson` 0 件 (ThompsonSubgroup.lean header 実測 v4.29.1 時点、以後も未収載)。
- coq/: math-comp odd-order は ZJ を形式化せず Puig `L(S)` で代替 (`BGappendixAB.v:16`)。
- open 9xxx: 9130/9132/9133/9159/9164/9400/9401/9402 — ZJ/Thompson 関連の claim なし。

## 参照

- issue 3024 (親、規模見積 2,000-4,000 行 / 複数 session) / issue 3017 (最終 consumer)。
- `references/gorenstein/finite-groups.mmd` L5431-5622 (Ch.8 §2)。
- `references/bg/local-analysis.pdftotext.txt` L3040-3045 (Thm 6.2), L8611 (記号表)。
- repo: `GroupTheory/ThompsonSubgroup.lean` (elementary 版、API パターンの参照元)。
