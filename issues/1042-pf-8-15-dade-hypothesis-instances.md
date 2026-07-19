---
id: 1042
slug: pf-8-15-dade-hypothesis-instances
title: "(8.15) の残り主張: type-𝒫 (4.6)/(5.2) instance"
created: 2026-07-19
---

# (8.15) の残り主張: type-𝒫 (4.6)/(5.2) instance

## 教科書 (PDF p.48 で確定, 2026-07-19)

**(8.15)** M maximal, A = A₀(M), A(M), A₁(M) のいずれか。
1. **M = N_G(A) かつ Hypothesis (2.2)** が L = M, H(a) = R(a) で成立。
   証明: (2.2.a,b,c) は (8.13.a,c1,c2) から。
2. **M が type 𝒫, M′ = [M,M] なら Hypothesis (4.6)** が
   L = M, K = M′, A = A(M), A₀ = A₀(M), **H = M_F または H = M_s** で成立。
   証明: (8.4.a,d), (8.5.c), (8.10) から。
3. **M が type 𝒫 で 𝒮 ⊆ {Ind_{M′}^M θ | θ ∈ Irr M′, M_s ⊄ Ker θ} 非空・共役閉なら
   Hypothesis (5.2)** が L = M で成立。証明: (1.5.e) + (5.3.b) から。

(8.10): M_s = H (type I/II/V) / M′ (type III/IV)。A(M) (type 𝒫) = ⋃_{x∈M_s^#} C_{M′}(x)^#。

## 現状 (frontier note 2026-07-19 実測 + 本 issue での確認)

- 主張 1: `DadeSupportHypothesisData` (S10_StructureSetup.lean:710) + 型別 3 instance
  (typeI / typeP₁ / typeII) が存在。docstring に「(4.6)/(5.2) 特殊化は別 TODO」と明記。
- 主張 2: typeP₁ 消費側 ((4.6) = `S06.Hypothesis46`) は S12 が持つが、
  **(8.15) としての一般 statement (H = M_F / M_s の両方、type II 込み) は未形式化**。
- 主張 3 ((5.2) instance): **皆無**。
- ⚠ gate: type II/V では M_s = M_F ≠ M′ なので、repo の `typePA` ((M′)^# 添字固定、
  issue 9008 で IsTypeP1 に narrow 済) では A(M) が書籍と食い違う。9008 hub 裁定:
  「S-side honest 化の設計変更が起きた場合のみ Option A (typePA 訂正) を再検討・re-open」。
  **(8.15) の type-II 完全形式化がその trigger になり得る** — 着手時に 9000 issue で
  hub に設計確認 (typePA の M_s^# 添字化 or 別 def 新設) を出すこと。無断で typePA を
  再定義しない (shared infra、lane b の S12/S14 consumer に波及)。

## 進捗

- **着手順 1 完了 (2026-07-19)**: `OddOrder/Peterfalvi/S10_SubcoherentTypeP.lean` 新設。
  - (5.2) の repo 対応物 = `S07.Hypothesis` (既約メンバー形、2 元 `CharacterDifferenceImage`
    固定) と確認。可変長 R (可約 μ 列) は S07_Subcoherent の corrected module note
    (2026-07-06 hub 検証) どおり `S06.certainTypeR`/`columnImageFamilyCohFree` 側が正本 —
    `S07.Hypothesis` 形の (8.15.3) は既約部分家族が honest な全内容。
  - `inducedKernelFamily_subcoherent` (A = A₀(M)、consumer 形) +
    `inducedKernelFamily_subcoherent_sharp` (A = M^#、書籍 (5.2.b) 字義形; narrowing
    Z[S,M^#] ⊆ CF(M,(M′)^#) 込み) を `irrSubcoherent` 経由で構成。
    supporting: `mderivSharp_subset_supportInSubgroup_typePA0` ((8.10) 包含の §8 レベル形)、
    `inducedKernelFamily_member_support_subset_derivedInG`。
  - 全 4 宣言 axiom-clean (`propext`/`Classical.choice`/`Quot.sound` のみ、#print axioms 確認)。
  - 注: 文言は「type III/IV」でなく **P₁ regime** (typePA 忠実域 = 9008 裁定) で scoping。
    statement 自体は素の `TypePData` で成立 (IsTypeP1 は入力 datum `d` の producer 側)。

## 着手順 (ungated → gated)

1. ~~**主張 3 の type III/IV 形**~~ ✅ 上記 (2026-07-19)。旧計画:
   `Hypothesis (5.2)` の repo 対応物を確認 (S07 の coherence context;
   (5.2) = 「S ⊆ Irr L induced family + τ isometry」形の仮説) し、
   (1.5.e) + (5.3.b) 経由で instance を証明。
   ⚠ まず「repo に (5.2) 対応の Hypothesis オブジェクトが在るか」を grep
   (frontier note の (9.11) 行いわく「repo に Hypothesis (9.5) が無い」同様、
   (5.2) も handle が無い可能性 — その場合 (5.2) carrier の新設から)。
2. **主張 2 の一般形** (H = M_F と H = M_s の両方; type III/IV は M_s = M′):
   既存 S12 の Hypothesis46 producer を (8.15) 名義の一般 statement に持ち上げ。
3. **type II/V** (gated): 9000 issue で hub 設計確認後。

## 参照

- frontier note §8 (8.15) 行 / issue 9008 (closed; Option B 裁定と re-open 条件)
- S10_StructureSetup.lean:703-750 (DadeSupportHypothesisData + TODO)
- 書籍 p.47-48 (PDF pages 4-5)
