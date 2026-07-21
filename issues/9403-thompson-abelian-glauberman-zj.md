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
