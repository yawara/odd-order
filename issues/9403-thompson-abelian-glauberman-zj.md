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
