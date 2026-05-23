# BG §2: General Results on Representations — mini-roadmap

**スコープ**: BG §2 (pp.9–16, mmd L586–794), **6 結果** (Thm/Prop/Lem 2.1, 2.2, 2.3, 2.4, 2.5, 2.6).

形式化先 (予定): `OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`.

**ROADMAP 上の位置**: **Phase 2a 第 1 波 (optional 独立節)** — §3 (Frobenius 作用) の依存なし、独立して形式化可 (本文使用は限定的).

**役割**: operator group の表現論基礎、Fong–Swan 系 (Thm 2.3)、extraspecial p-群の加群構造 (Thm 2.5)、odd-order 2-次元表現 (Thm 2.6). **§9 周辺で 1–2 箇所のみ被引用**, optional 節のため形式化は必要時のみ.

## Audit log (2026-05-23 audit 訂正)

統合 doc: [`notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`](../meta/bg_phase2a_wave1_audit_2026_05_23.md).

- **"§9 周辺で 1-2 箇所のみ被引用" → 完全に誤り**. 実測 §9 = **0 cites**. 実際: §3 ×5 (Prop 2.1, Prop 2.2 ×2, Thm 2.5, Thm 2.6 ×2 + 別 cite), §4 Lem 4.17, §15 Thm 15.7, **App.A Thm A.1 proof (L4464) で Thm 2.6 cite**. 合計 **8+ cites**, §2 は FT 中核.
- **"optional 節, 形式化は必要時のみ" / "skip 推奨" → 完全に逆**. §3 + App.A の **前提** ⇒ Phase 2a 第 1 波必須.
- **"Short path Thm 2.3 only" 推奨 → INVERTED**. Lem 2.3 (Fong-Swan) は forward use **0**, defer 可. Thm 2.5 + Thm 2.6 + Prop 2.1 + Prop 2.2 が必須.
- **L70 "Jacobson Density mathlib 未実装" → 誤り**. `Mathlib/RingTheory/SimpleModule/Basic.lean:582` `Module.Finite.toModuleEnd_moduleEnd_surjective` ✓.
- §2 ⇒ Peterfalvi §3-§8 オーバーラップなし (Peterfalvi は character-theoretic `[Is]`=Isaacs *Character Theory* 別書).
- **§2 は Isaacs Ch.6 §6F Clifford 完成依存** (Prop 2.2 で必須). Ch.6 not started ⇒ §2 全体 blocker.
- 新規 shared modules: `IsExtraspecial.lean`, `AbsolutelyIrreducible.lean`, `Clifford.lean`, `PGroupFixedVector.lean`, `EigenspaceUnderCyclicAction.lean`.

## 実装ログ

- **2026-05-24** [`OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`](../../OddOrder/BG/Ch1_Preliminary/S02_Representations.lean) **skeleton 完成** (~330 行 docstring 中心). 6 sub-section (§2A Prop 2.1 / §2B Prop 2.2 / §2C Lem 2.3 / §2D Prop 2.4 / §2E Thm 2.5 / §2F Thm 2.6) に BG 本文 statement (mmd L598-793) + 形式化方針 + mathlib カバレッジ + 下流引用 (audit 実測) + Lean signature 案 を整理. **statement stub は全 6 結果未配置** (`RepresentationTheory/*` shared module 5 件未作成 + Isaacs Ch.6 §6F Clifford 未完成). 着手順 (audit 推奨): Thm 2.6 → Prop 2.4 → Prop 2.1 → Thm 2.5 → Prop 2.2 (Ch.6 待ち); Lem 2.3 (forward use 0, defer).

## TL;DR

**§2 は基本的な表現論モジュール**: operator group G に対する FG-加群の性質を 6 つの定理で系統化. 主な成果は:
- **Thm 2.1 (Schur 補題応用)**: 既約加群の自己準同型環と enveloping algebra の関係
- **Thm 2.3 (Fong–Swan)**: 可解群の絶対既約加群の次元は群の位数を割る
- **Thm 2.5**: extraspecial p-群と cyclic H の semidirect product における加群構造制約
- **Thm 2.6**: 奇数位数 2-次元加群 ⇒ G abelian or Sylow p-subgroup abelian (奇数位数限定)

**mathlib カバレッジ**: **高い**. mathlib `RepresentationTheory.Basic`, `Maschke`, `FDRep` API で大部分既存 (Schur 補題、既約性、制限・誘導加群).

**下流被引用**: §9 周辺 1–2 箇所のみ. 形式化優先度は **低い** (optional 節、本文必須性低).

---

## §2 全 6 結果一覧

| # | 種別 | mmd 行 | statement 要約 (1–2 行) | 依存 | mathlib | 優先度 |
|---|------|--------|--------------------------|------|---------|--------|
| **2.1** | **Prop** | **598–612** | **(Schur の補題 + 既約 ↔ absolutely irreducible)** (a) M 既約, FG-自己準同型環 = F ⇔ M absolutely irreducible; (b) G faithful on M, HomFG(M,M) = F ⇒ HomF(M,M) = E(G); (c) F 有限体, K = HomFG(M,M) ⇒ K 体, M は KG-加群 | Schur, Jacobson Density | `FDRep.IsIrreducible`, `Schur.lemma` | ★ |
| **2.2** | Prop | 614–652 | (Clifford + cyclic quotient) H ◁ G, G/H cyclic, F 代数閉, M 既約 FH-加群, M ≅ M^x (x ∈ G) ⇒ (a) L 既約 FG-加群, M ⊆ L_H ⇒ L_H ≅ M; (b) H の表現 ⇒ G へ lift 可 | Clifford Thm 3.4.1, Jacobson | (Clifford 標準, 新規 statement) | ★ |
| **2.3** | **Lemma** | **655–668** | **(Fong–Swan)** G solvable, F 体, M absolutely irreducible FG-加群 ⇒ dim M \| \|G\| | Fong–Swan Thm 72.1 (高度な結果) | (characteristic 制約なし新規) | ★★ |
| **2.4** | Prop | 670–712 | (線型代数 + 既約性) V 体 F 上、g ∈ Aut V (有限位数), h-th root of unity ε ∈ F ⇒ eigenspace V_i 分解 + dim E_{i,t} 公式 + G-module structure (10 部技術定理) | (純粋線型代数) | (既存概念, 新規 statement) | ★ |
| **2.5** | **Thm** | **716–772** | **(extraspecial p-群と cyclic action)** P extraspecial p-group (order p^{2n+1}), H cyclic coprime, C_P(x)=Z(P) (x ∈ H^#), F char ∤ \|G\|, G = P ⋊ H ⇒ h \| (p^n ± 1); h ≠ p^n+1 ⇒ C_V(H) ≠ 0 (faithful irreducible V に対し) | Thm 5.5.4–5.5.5, Jacobson | (新規 statement, extraspecial 使用) | ★★ |
| **2.6** | **Thm** | **774–793** | **(奇数位数 + 2-次元)** G odd order, F field, V faithful FG-加群 (dim 2) ⇒ (a) char F ∤ \|G\| ⇒ G abelian; (b) char F = p \| \|G\| ⇒ Sylow p-subgroup abelian ∧ contains G' | (Thompson, induction + GL(2,q)) | (新規 statement) | ★★ |

---

## Thm 2.1: Schur 補題 + 既約 ↔ absolutely irreducible

### Statement (mmd L598–603)

```
G: 群, F: 体, M: 既約 FG-加群
─────────────────────────────────

(a) M absolutely irreducible ⟺ HomFG(M,M) = F

(b) G faithful on M, HomFG(M,M) = F ⇒ HomF(M,M) = E(G)

(c) F 有限体, K = HomFG(M,M) ⇒ K 体, M absolutely irreducible KG-加群
```

### 前提条件

- **M は既約 FG-加群**: すべての proper 部分加群は 0
- **absolutely irreducible**: F̄ (F の代数閉包) 上でも既約
- **E(G)**: G が V に faithful に作用する時の enveloping algebra (FG-加群 V を生成する F-部分代数)

### 証明梗概 (BG L604)

- **(a)**: char F = 0 or coprime to |G| ⇒ Gorenstein Thm 3.5.7; 一般的: Jacobson Density Thm (G Thm 3.6.2) 経由
- **(b)**: Jacobson Density + HomFG(M,M) = HomE(G)(M,M) の事実
- **(c)**: Schur 補題 (K division algebra), Wedderburn 有限体定理 ⇒ K は field

### 形式化対応 (mathlib)

**mathlib 側**:
- `FDRep` (有限次元 G-表現): `FDRep.IsIrreducible` 既に定義
- Schur 補題: `Module.Schur.lemma` の variant
- Jacobson Density: mathlib 未実装 (phase 1 での Isaacs 참照 형식화 필요)

**形式化ロードマップ**:
```lean
-- Phase 1 Isaacs Ch.3 から Jacobson Density import
theorem thm2_1_a {M : FDRep F G} (hM : M.IsIrreducible) :
    M.IsAbsolutelyIrreducible ↔ (M.End).ker = ⊥ := by
  -- Jacobson Density Thm via Isaacs
  sorry

-- (b) は (a) + EndAlgebra 結合
-- (c) は 有限体上 division algebra ⇒ field (mathlib basic)
```

---

## Thm 2.3: Fong–Swan — 可解群の既約加群次元

### Statement (mmd L655–657)

```
G: 可解群, F: 体, M: absolutely irreducible FG-加群
──────────────────────────────────────────────
dim M | |G|
```

### 背景

**Fong–Swan Thm 72.1** (高度な結果): 可解群の既約表現次数は群の位数の因子。

### 証明梗概 (BG L659–668)

**帰納法** (|G| について):
1. H ◁ G, prime index p を取得 (§1 Lemma 1.1)
2. L ⊆ M_H 既約 ⇒ dim L | |H| (帰納仮説)
3. **Case 1**: L ≅ L^x (x ∈ G - H) ⇒ Thm 2.2 より L = M_H ⇒ dim M | p · |H| = |G|
4. **Case 2**: L ≁ L^x ⇒ M_H = L ⊕ L^x ⊕ ⋯ ⊕ L^{x^{p-1}} (pairwise nonisomorphic)
   - dim M = p · dim L | p · |H| = |G|

### 形式化対応

**mathlib 側**: 
- **既約性判定**: `IsIrreducible` (既存)
- **制限 (restriction)**: `RestrictScalars` 経由 (既存)
- **次数制約**: 新規 lemma 必要

**形式化難度**: **高い** (Clifford theorem 活用, 帰納構造). Fong–Swan 原理自体は Isaacs references から参照.

```lean
lemma fong_swan {M : FDRep F G} (hM : M.IsAbsolutelyIrreducible) 
    (hsolv : IsSolvable G) :
    FiniteDimensional.finrank F M ∣ Nat.card G := by
  -- BG L659 の帰納法スケッチ
  sorry
```

---

## Thm 2.5: Extraspecial p-群と Cyclic Action

### Statement (mmd L716–722)

```
P: extraspecial p-group (order p^{2n+1})
H: cyclic group, |H| = h, h ⊥ p
G = P ⋊ H (semidirect product)
Condition: ∀x ∈ H^#, CP(x) = Z(P)

F: 체 with char F ∤ |G|
V: faithful, irreducible FG-加群
──────────────────────────────────

⇒ h | (p^n - 1) or h | (p^n + 1)

If h ≠ p^n + 1, then CV(H) ≠ 0
```

### 前提条件

- **extraspecial p-group**: 中心 Z(P) = p, P/Z(P) elementary abelian, |Z(P)| = p
- **coprime action**: (|H|, p) = 1, faithful conjugation H → Aut P
- **条件 C_P(x) = Z(P)**: H の非自明元による固定点は中心のみ

### 證明梗概 (BG L726–772)

**主要ステップ**:
1. (L726–740) V̄ = F̄ ⊗_F V (代数閉体拡張)
2. W ⊆ V̄ irreducible G-submodule, M ⊆ W irreducible P-submodule
3. P は W に faithful に作用 (L743–744, C_V(Z(P)) = 0 から)
4. Thm 5.5.4–5.5.5 (extraspecial 表現): faithful irreducible P-表現 ⇒ dim M = p^n, P はモジュール M を faithful に作用
5. **Prop 2.4 (線型代数)**: E(P) = End_F(V), H 作用下での eigen-space 分解
   - E は H の作用下で "principal module" と "regular module" の直和 (L770)
   - Prop 2.4(j), (k) 条件チェック ⇒ h | (p^n ± 1)
6. (L772) Prop 2.4(k): C_V(H) = 0 ⟺ h = p^n + 1

### 形式化対応

**mathlib 側**:
- **extraspecial p-group**: 新規定義 (Phase 1 にて可能性)
- **Thm 5.5.4–5.5.5**: Isaacs 참조 (extraspecial representation 理論)
- **Prop 2.4 (線型代数)**: **テクニカル** — eigen-space 分解と H-module 構造の相互作用

**形式化難度**: **非常に高い** (extraspecial 표現론, 線型代数テクニック, 複雑な帰納).

```lean
theorem thm2_5 {P : Subgroup G} (hP : IsExtraspecial p P) 
    {H : Subgroup G} (hH : IsCyclic H) (hcoprime : (H.card, p) = 1)
    (haction : ∀ x ∈ H, x ≠ 1 → Centralizer P x = Subgroup.center P) :
    H.card ∣ p ^ n - 1 ∨ H.card ∣ p ^ n + 1 := by
  -- Prop 2.4 (j), (k) + extraspecial 理論
  sorry
```

---

## Thm 2.6: 奇数位数 2-次元加群 ⇒ Structure

### Statement (mmd L774–778)

```
G: finite group of odd order
F: field
V: faithful FG-加群, dim V = 2

──────────────────────────────────

(a) char F ∤ |G| ⇒ G abelian

(b) char F = p | |G| ⇒ Sylow p-subgroup abelian ∧ contains G'
```

### 証明梗概 (BG L779–793, MISSING_PAGE:29 を含む)

**帰納法** (|G| について):

**Step 1: 前処理**
- G ⊆ GL(V, F) と見做す
- G* = G ∩ SL(V, F)
- F を代数閉体に拡張 (可)

**Step 2: p-element と固定点**
- p = char F の場合分け
- K = Ω₁(Z(O_q(G*))) (K elementary abelian q-group, q | |G|, K ◁ G)

**Step 3a: q = p の場合**
- W = C_V(K) (K-不変部分加群)
- G Lemma 2.6.3: W ≠ 0
- dim V = 2, G faithful on V ⇒ dim W = 1 (L785–786)
- dim W = dim V/W = 1 (orthogonal decomposition)

**Step 3b: q ≠ p の場合**
- Sylow q-subgroup の可解 action
- induction 適用

### 形式化対応

**mathlib 側**:
- **GL(2, F), SL(2, F)**: 基本 linear group (既存)
- **odd order 仮定**: `Odd G.card` (既存)
- **Sylow subgroup**: `Subgroup.Sylow` (既存)
- **Lemma 2.6.3 (Gorenstein)**: G の代数的補助定理 (mathlib 未実装, Phase 1 Isaacs 参照)

**形式化難度**: **高い** (induction + case split, GL(2,q) embedding, Sylow characterization).

```lean
theorem thm2_6 {G : Type*} [Group G] [Fintype G] [Odd G.card]
    (V : Type*) [AddCommGroup V] [Module F V] [Module G V]
    (hfaithful : FaithfulSMul G V) (hdim : FiniteDimensional.finrank F V = 2) :
    (CharP F 0 ∨ ¬ Nat.Prime.dvd (CharP.char F) G.card) → IsCyclic G ∧ IsAbelian G := by
  -- induction + GL(2, F) argument
  sorry
```

---

## Thm 2.2 + Prop 2.4 (Technical Lemmas)

### Thm 2.2: Clifford + Cyclic Quotient

**目的**: H ◁ G cyclic quotient G/H 下で、M ≅ M^x (共役加群が isomorphic) なら M_H (restrict to H) is unique, lift 可.

**mathlib 対応**: Clifford 理論 (`Module.restrictScalars`) 既存、new statement として形式化可.

### Prop 2.4: Eigenspace Decomposition

**目的**: g ∈ Aut V (有限位数), ε ∈ F (primitive h-th root of unity) → eigenspace V_i = {v | vg = ε^i v} 分解 + End(V) の H-module 構造.

**形式化対応**: **線型代数テクニック** (basis 変更、行列ブロック分解). 10 部性質中 (j), (k) が Thm 2.5 の鍵.

---

## mathlib カバレッジ評価

| 結果 | mathlib 対応 | 新規実装 | 難度 |
|-----|------------|---------|------|
| **Thm 2.1** (Schur + 既約) | `FDRep.IsIrreducible`, Schur lemma basic | Jacobson Density variant | 中 |
| **Thm 2.2** (Clifford + cyclic) | Clifford basic, `RestrictScalars` | new statement (Prop 2.2) | 中 |
| **Thm 2.3** (Fong–Swan) | 既約性, 次数制約 new | **Fong–Swan 帰納** | 高 |
| **Prop 2.4** (eigenspace) | 線型代数基本 | **10 部技術定理** | 非常に高 |
| **Thm 2.5** (extraspecial) | 未実装 (extraspecial 理論新規) | **extraspecial 加群論** | 非常に高 |
| **Thm 2.6** (odd 2-dim) | GL(2,F), Sylow, odd order | **induction + GL embedding** | 高 |

**総評**: **Thm 2.1–2.2 は mathlib 基礎活用で中程度、Thm 2.3–2.6 は新規技術理論で高–非常に高難度**.

---

## §9 周辺への被引用

### 明示的引用 (予備調査)

**mmd grep** ("`Theorem 2\." or "Lemma 2\." + `§9|§8|§7` context):
- **§9 L2511~**: "Thm 2.3 (Fong–Swan)" — characterization (없을 가능성, 재확인 필요)
- **App.A L4500~**: "Prop 2.4 線型代数" — eigenspace 理論参照 (가능성)

### 予想される使用場면

1. **§9 (Uniqueness) character theory**: Fong–Swan (Thm 2.3) で 可解성 + representation 次数 제약
2. **App.A (p-Stability)**: Thm 2.5, 2.6 의 extraspecial structure 참조 (unlikely, 但し確인 필요)

**현재判단**: 本文使用は **최소 1-2 箇所 (§9 중심)**, Thm 2.3 (Fong–Swan) のみ likely.

---

## Phase 2a 形式化着手順

### 優先度判定

1. **Thm 2.1 (Schur + 既約)** ★★ — 기본, mathlib 기반, 短い. (2-3 日)
2. **Thm 2.3 (Fong–Swan)** ★★ — 본문 사용 가능성, solvable context. (3-4 日)
3. **Thm 2.2 (Clifford + cyclic)** ★ — 補助的, Thm 2.5 先행불必要. (2-3 日)
4. **Prop 2.4 (eigenspace)** ★★★ — Thm 2.5 의존, 기술적. (5-7 日)
5. **Thm 2.5 (extraspecial)** ★★★ — 非常に高難度, optional. (1-2 週)
6. **Thm 2.6 (odd 2-dim)** ★★ — odd-order 限定, 형식화 가치. (4-5 日)

### 推奨スケジュール

**§2 전체 형식化는 optional** (본문 1-2 箇所, Phase 2a 中盤以降):
- **Short path** (§9 対応のみ): Thm 2.3 のみ (3-4 日, 必須性低)
- **Full path** (complete module): Thm 2.1–2.6 all (3-4 週, 별도 담당者 가능)

**권고**: **Phase 2a §1–§9 완료後**, §2 필요성 재평가 후 착수 (현재는 skip 추천).

---

## 未解決 / TODO

| 項目 | 状態 | 확인先 |
|------|------|--------|
| **Fong–Swan citation** | BG L657 "Fong and Swan [5, Theorem 72.1]" — citation 설정 필요 | BG references 재확인 |
| **Lemma 2.6.3 (Gorenstein)** | BG L783 "G, Lemma 2.6.3, p. 31" — 내용 확인, Isaacs 대응 필요 | Isaacs FGT §2.6 재확인 |
| **MISSING_PAGE:29 content** | L787 이후 페이지 내용 누락 (Thm 2.6 증명 중단) — mmd 재스캔 필요 | BG PDF pp. 28–29 재OCR |
| **Prop 2.4(j)–(k) statement** | Thm 2.5 증명에서 핵심 but verbose. statement 정확성 재확인 | BG L696–712 정독 |
| **mathlib `Maschke` API** | §2 에서 언급 가능성 (L1.20에서 phase 1 참조) | `Maschke.completely_reducible` 확인 |

---

**작성**: 2026-05-22

**출처**:
- `references/bg/local-analysis.mmd` lines 586–794 (§2 완문)
- `references/bg/bg.pdf` pp. 9–16 (visual confirm)
- `notes/bg/_overview.md` (BG overview)
- `notes/isaacs/ch03_hall.md`, `notes/isaacs/ch07_thompson.md` (참조)

**다음ステップ**: 
- Phase 2a §1–§9 진행 상황에 따라 §2 형式化 필요성 재평가 (중기–후기 phase 2a)
- Thm 2.3 (Fong–Swan) 만이라도 선제적 형式화 고려 (§9 character theory 지원)
- Extraspecial 이론 (Thm 2.5) 형식화는 별도 스페셜리스트 담당 권고 (높은 난도)
