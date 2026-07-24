# BG Phase 2a 第1波 audit (2026-05-23)

BG Phase 2a 第 1 波の 6 節 (§1 Solvable / §2 Representations / §4 p-Groups Small Rank / §5 Narrow p-Groups / App.A p-Stability / App.B Puig L(S)) を **4 視点** (forward / internal hub-and-spoke / mathlib status incl. proof-internal API / preceding-chapter per-target deps) で並列再調査した結果の統合メモ. 既存の per-section ノート (`notes/bg/{s01,s02,s04,s05,appA,appB}_*.md`, 2026-05-22 作成) の上にかぶせる **sharp findings + 補正 + 設計提案** のみを記述. 各節の TL;DR / 結果一覧は per-section ノート参照.

## 統合観点での最重要 5 点

> **⚠️ 2026-05-28 反転 (点1)**: 下記「App.B + Thm A.5 を Phase 2a で完全スキップ可」は **撤回**。
> FT-citation-orphan の観察は正しいが、**Isaacs FGT が Glauberman Z(J)-定理 (= BG Thm 6.2) を省く** (Isaacs p.217) ため、no-Gorenstein 方針下では **App.B (Puig L(S), Thm B.4) こそが Thm 6.2 の唯一の自己完結代替**で必須。本監査は「App.B が Gorenstein 依存を断つ代替」という役割を見落とした。
> 詳細・依存閉包・J→L 大域置換の検証: [`bg_s6_appAB_route_2026_05_28.md`](bg_s6_appAB_route_2026_05_28.md)。

1. **App.B + Thm A.5 を Phase 2a で完全スキップ可** (~570 行, ~10-13 日節約): App.B は **FT 経路で完全孤立**. 唯一の本文使用箇所は §6 L1979 (advertisement) と App.D L5014 (FT 無関係, "may substitute L(P) for J(P)"). overview L95「App.B は App.A 不要で独立着手可」は **誤り** (Lem B.3 L4666 + Thm B.4 Step 3 L4735 が Thm A.5 cite). A.5 自体も App.B 唯一の消費者. **両方 skip し AppA docstring に omission note**. **【2026-05-28 撤回: 上記 banner 参照。App.B は 6.2 代替の本線で必須】**

2. **App.A は §6 の "下流" ではなく "上流"**. 既存 appA ノート L13-14「下流被引用 Thm 6.1, 6.2」は方向逆. BG 序文 L4452: "Theorems 6.1 and 6.2 ... are obtained by use of p-stability ... we outline these shorter proofs". したがって **Phase 2a 着手順は §1 + §2 → App.A → §6** (App.A は §6 直前, 並行ではない). さらに App.A は **BG §1 Prop 1.8 + Prop 1.15(b) + BG §2 Thm 2.6 完成必須**, 既存ノートが未捕捉.

3. **§2 は "FT 中核, 第 1 波で必須"**, 既存ノートの "skip 推奨" は **完全に逆**: §2 引用箇所は実測 **8+ 件** (§3 ×5 [FT クリティカル], §4 ×1, §15 ×1, **App.A Thm A.1 proof L4464 ×1**), 既存「§9 周辺 1-2 箇所のみ」は誤り. **§9 では §2 cite が実は 0**. Lem 2.3 (Fong-Swan) のみ forward 0 で defer 可, 既存ノートが推奨する "short path Thm 2.3 only" は完全に逆向きの判断. **§2 は §3 (Frobenius) + App.A の前提**.

4. **A.4(b) ≠ Isaacs 7.6 (同値ではなく系)**: 既存 appA ノート L29-61「論理同値 (odd-order solvable 下)」は overstate. 仮定: 7.6 は P=C_G(Z(P)) + O_{p'}(G)=1 等含む, A.4(b) は P Sylow のみ. 結論: 7.6 = J(P)⊴G (specific subgroup), A.4(b) = abelian normal of S ⊆ O_{p',p}(G) (collection bound). **7.6 ⇒ A.4(b)** trivial, 逆方向は **J(P) ⊴ G の追加 statement 必要**. 形式化的に "≅" ではなく "Isaacs 7.6 が A.4(b) を含む" 関係.

5. **`OddOrder/GroupTheory/` 新規 shared module 群** (Phase 2a 第 1 波の真の前提条件, Ch.4-7 audit 推奨を拡張):
   - `OpResidual.lean` (O_p, O_{p'}, O_{p',p}, Fitting series 2nd term) — **App.A 必須前提**. mathlib に何も無い. ~150-250 行.
   - `InvariantSubgroup.lean` (A-invariant Sylow/Hall under coprime action) — **§1 Prop 1.5 base**, §4 Prop 4.4 でも. mathlib Sylow.conj_eq_normalizer 部分 + Hall 拡張.
   - `ChiefSeries.lean` — **§1 Prop 1.2/1.3 base**. mathlib `CompositionSeries` Group 版**存在せず** (`grep` 確認).
   - `OmegaSubgroup.lean` (Ω₁, Ω_n) — §1 Thm 1.11/1.13, §4 全節, §5 全節.
   - `PRank.lean` (`m(A)`, `r_p(G)`, `r(G)`) — §4, §5 で必須. mathlib `Group.rank` は **min-generators で p-rank ではない** (`Rank.lean:31-33`). 命名衝突回避: `IsPGroup.pRank` 等明示.
   - `FrattiniPGroup.lean` (Lem 1.7(b)(d)) — mathlib `Frattini` は (a)(c) のみ.
   - `MinimalNormal.lean` — §1 Lem 1.1 "⊆ Z(F(G))" 部分.
   - `Thompson.lean` (J(P)) — Ch.7 / App.A 共有 (Ch.4-7 audit 既述).
   - `PStable.lean` (`IsPStable` + `IsPStableOddOrder`) — App.A.
   - `IsExtraspecial.lean` — §2 Thm 2.5, §4 Lem 4.15.
   - `IsMetacyclic.lean` — §4 Lem 4.10/4.12.
   - `RepresentationTheory/Clifford.lean` — §2 Prop 2.2 (mathlib upstream candidate).
   - `RepresentationTheory/AbsolutelyIrreducible.lean` — §2 Prop 2.1 (mathlib upstream candidate).
   - `RepresentationTheory/EigenspaceUnderCyclicAction.lean` — §2 Prop 2.4.
   - `RepresentationTheory/PGroupFixedVector.lean` — §2 Thm 2.6, §3 L1255 (Gorenstein Lem 2.6.3).
   - `AutElementaryAbelian.lean` (Aut(elem ab order p^n) ≃ GL(n, F_p)) — §2 Thm 2.5, §5 Thm 5.5.
   - `SCN.lean` (SCN_n) — §4, §5.

---

## 1. Forward to later sections (sharpened)

### 1.1 §1 → 後続 (引用頻度実測)

| §1 result | 実測 | 既存ノート claim |
|---|---|---|
| Prop 1.5 | 25 | 28+ |
| Prop 1.6 | 13 | 16 |
| Prop 1.16 | 10 | 11 ✓ |
| Prop 1.15 | 8 | 9 ✓ |
| **Prop 1.2** | **6** | "22" (大幅誇張) |
| Thm 1.8 | 4 | 6 |
| Lem 1.21 | 3 | — |
| Lem 1.22 | 2 | — |
| **Lemma 1.1** | **0 in §2+** | "43+" (**重大誤り**, Peterfalvi `[Is] Lem 1.5` Schur と混同と推測) |

### 1.2 §2 → 後続 (実測, 既存「§9 1-2 箇所」は完全誤り)

| §2 result | 実測 cites | downstream |
|---|---|---|
| Prop 2.1 | 1 (§3 Thm 3.16) | ☆ |
| Prop 2.2 | 2 (§3 Thm 3.4 ×2) | ☆ |
| **Lem 2.3 Fong-Swan** | **0** | DROP (defer) |
| Thm 2.5 | 2 (§3 Thm 3.4, §15 Thm 15.7) | ☆ |
| **Thm 2.6** | **4** (§3 ×2, §4 Lem 4.17, **App.A Thm A.1 proof L4464**) | ☆☆ |

§9 への §2 cite は **ZERO**.

### 1.3 §4, §5 forward (実測)

- §5 → 5 distinct downstream sites: §8 L2324, §9 L2629, §10 ×3, §12 L3373-3379, §14 L4130, §15 L4188, App.E L5164-5168. 既存「§10, §13, App.C」3 件は undercounted.
- §4 → §5, §7-§9 (5 cites), §10-§13, §16, App.E.
- §10 L2643 の "ideal prime" def は **§5 Thm 5.3 の contrapositive** = 視点 1 で重要な定義的 forward.

### 1.4 App.A → 後続

- A.4(b) ↔ Thm 6.1 (再述, §7 でも L2275, L2291 cite, **既存ノート未捕捉**)
- **A.4(c) は直接外部使用 0** (A.5 経由間接のみ)
- A.5 は **App.B 専用** (Lem B.3 + Thm B.4 Step 3); App.B 全体が FT-orphan ⇒ A.5 も orphan

### 1.5 App.B → 後続

- §6 L1979: advertisement only
- App.D L5014: FT 無関係 (CN-theorem detour, △)
- **§1-§16 + App.C + App.E から 0 cite**
- Peterfalvi も 0 cite (`phase2_cross_refs.md` L34 で確認)

⇒ **App.B 完全孤立**.

---

## 2. Internal hub-and-spoke (sharpened)

### 2.1 各節 hub

| 節 | hub | cites | 既存ノート評価 |
|---|---|---|---|
| §1 | **Prop 1.5(d)** | 6 §1 proofs (Prop 1.6, Thm 1.8, Lem 1.9, Prop 1.10, 1.15) | Lemma 1.1 を hub 誤認 |
| §2 | Prop 2.1, Prop 2.4 | 4 self-cites 各 | OK |
| §4 | **Lem 4.5** | 11 self-cites (Lem 4.6, 4.10, 4.12 ×3, **Thm 4.16 ×4**, 4.18) | 既存「Thm 4.18 / Thm 4.20 hub」と並列 (Lem 4.5 を ★★ → ★★★ 昇格) |
| §5 | **Lemma 5.1** | 4 self-cites | 既存「Thm 5.3 / Thm 5.5 hub」誤り |
| App.A | A.4 (3 parts critical) + A.5 | — | OK |
| App.B | **Lem B.1 (特に B.1(f) p-group + B.1(c) stabilization)** | All 3 of B.2/B.3/B.4 depend | OK |

### 2.2 物理 vs 論理順序 mismatch

- §1: 一致 (validated)
- §2: 一致
- §4: Thm 4.16 (L1640) → Prop 4.8 → Prop 4.3 chain (3 段). Lem 4.17 (L1712) は §1 Thm 1.13 (Thompson critical) 経由 = **§1 dep, §4 内ではない**
- §5: 一致
- App.A: 一致 (A.1→A.2→A.3→A.4→A.5)
- App.B: stabilization (B.1(c)) が hub

---

## 3. Mathlib status (proof-internal) — 統合観点

### 3.1 mathlib v4.29.1 で本質的に欠けている前提

| 概念 | 状態 | 必要箇所 | 工数 |
|---|---|---|---|
| **`O_p`, `O_{p'}`, `O_{p',p}`** | 完全に無し (`Sylow.lean` は Sylow p-subgroup のみ) | App.A 全体 | ~150-250 行 (新規 module) |
| **Chief series / `CompositionSeries`** Group 版 | 無し (`Mathlib/GroupTheory/` で grep 0 hit) | §1 Prop 1.2, 1.3 | 新規 module ~200 行 |
| **A-invariant Hall theorem** | mathlib `Sylow.conj_eq_normalizer_conj_of_mem_centralizer` Sylow 版のみ. Hall + coprime action 拡張 | §1 Prop 1.5(a-c) (最 hub), §4 Prop 4.4 | 新規 ~150 行 |
| **`Omega1`, `Omega_n`** (p-group の x^p=1 elements 生成) | 完全に無し | §1 Thm 1.11/1.13, §4 全節, §5 全節 | 新規 ~50 行 + 20 instance |
| **`IsPGroup.pRank`** | mathlib `Group.rank` は **min-generators**, BG `m(A)=log_p|Ω₁(A)|` には不適 | §4, §5 | 新規 ~40 行 |
| **`Subgroup.thompsonJ` (J(P))** | 無し | Ch.7, App.A, BG §6/§8/§9 全面 | Ch.4-7 audit 既述 |
| **`IsPStable` predicate** | 無し | App.A, Isaacs Ch.7 §7B | Ch.4-7 audit 既述 |
| **Frattini Φ(R) quotient elem ab + Φ = ⟨R',x^p⟩** | mathlib `Frattini` は基本 4 つのみ ((b)(d) 無し) | §1 Lem 1.7 | 新規 ~50 行 |
| **`IsExtraspecial`** | 完全に無し (`RootSystem` hit は無関係) | §2 Thm 2.5, §4 Lem 4.15 | 新規 ~50 行 |
| **`IsMetacyclic`** | 完全に無し | §4 Lem 4.10/Prop 4.11/Thm 4.12 | 新規 ~10 行 def + lemma |
| **`SCN_n`** | 完全に無し | §4 Prop 4.4, Lem 4.7, §5 Lem 5.1 | 新規 ~50 行 |
| **`Aut(elem ab) ≃* GL(n, ZMod p)` bridge** | 部分的 (`Matrix.GeneralLinearGroup` あるが elem ab 経由 isomorphism は構築要) | §2 Thm 2.5, §5 Thm 5.5 | 新規 ~80 行 |
| **`IsPGroup.fixedVector_ne_zero` (p-group on char-p F-vector)** | partial (`Representation.Coinvariants` 関連だが直接形は不明) | §2 Thm 2.6, §3 L1255 | 新規 ~30 行 |
| **Clifford decomposition** | 完全に無し (`Representation.Induced` のみ) | §2 Prop 2.2 | 新規 module |

### 3.2 mathlib 既存で活用可能 (既存ノートが過小評価していた)

| 既存 mathlib | 該当箇所 | 既存ノート評価 |
|---|---|---|
| `Module.Finite.toModuleEnd_moduleEnd_surjective` (= Jacobson Density) | §2 Prop 2.1 | "未実装" は **誤り** (`SimpleModule/Basic.lean:582`) |
| `LittleWedderburn` | §2 Prop 2.1(c) | OK |
| `IsZGroup.coprime_commutator_index` | **§1 Cor 1.19(b) 直接ヒット** | "derived" 評価で **直接ヒット見落とし** |
| `Sylow.normalizer_sup_eq_top` (= Frattini argument) | App.B Thm B.4 Step 1, Step 4 | OK |
| `Subgroup.Characteristic` class + instances | App.B Step 3 | OK |
| `IsPGroup.commutative_of_card_eq_prime_sq` | §4 Lem 4.1 | OK ✓ |
| Phase 1 `hall_higman_1_2_3` (2026-05-23 完成) | §1 Prop 1.15(a) | priority ★★★ → ★ (thin wrap) |

### 3.3 Phase 1 進捗との接続

| BG | Phase 1 dep | 状態 |
|---|---|---|
| §1 Prop 1.6 | Isaacs 4.28-4.29 (Ch.4 §4D) | IN PROGRESS |
| §1 Thm 1.8 | Isaacs Thm 1.8 (Ch.1 §1B) | TODO |
| §1 Thm 1.11 | Isaacs Thm 4.36 + Omega1 helper | IN PROGRESS + 新規 |
| **§1 Thm 1.13** | **Thompson critical (NOT Isaacs 4.31!)** | Ch.4 endgame or Ch.7 early. **既存 Isaacs 4.31 と混同** |
| §1 Prop 1.15(a) | Hall-Higman 3.21 | **✅ 2026-05-23** |
| §2 Prop 2.2 | Isaacs Ch.6 §6F Clifford | **Ch.6 not started ⇒ §2 ブロッカー** |
| §2 Thm 2.5 | Isaacs 7.5 path + Extraspecial helper | new |
| §4 Lem 4.5(a) | Isaacs Thm 4.36 (Ch.4 §4D) | gated on Cor 3.28 (Tier 1 ~1-2wk) |
| §4 Lem 4.17 | **BG §1 Thm 1.13, 1.8 + BG §2 Thm 2.6** | BG §1+§2 dep |
| §4 Thm 4.18 | Isaacs Thm 6.16 / Fitting (Ch.6 §6D) | Ch.6 not started |
| App.A.4(b) | Isaacs 7.6 + new `Op*` + `Thompson` | shared module ~250 + Isaacs 7.6 待ち |
| App.A.5 | A.4(c) + **BG §1 Prop 1.8/1.15(b)** | BG §1 dep |

---

## 4. Preceding-chapter dependencies — 統合表

### 4.1 BG §1 への依存集中

BG §1 は **dependency leaf**: BG §X.Y (X≠1) への proof body cite **0 件**. 全外部依存は `G` (Gorenstein) cite を Isaacs 経由再構築.

逆に **§1 への依存** は全 BG 構造を支配:

```
BG §1 Prop 1.5(d)  ─→ §1 Prop 1.6, Thm 1.8, Lem 1.9, Prop 1.10, Prop 1.15
                  └─→ Peterfalvi 04.* (FT 経路)
BG §1 Prop 1.8     ─→ App.A.5 (BG §1 dep 未捕捉)
BG §1 Prop 1.15(b) ─→ App.A.5
BG §1 Thm 1.13     ─→ §4 Lem 4.17, §5 Thm 5.5
BG §1 Lem 1.22     ─→ §4 Lem 4.6
BG §1 Prop 1.2     ─→ §4 Thm 4.20, §5 Thm 5.7
```

⇒ **BG §1 完成は §4, §5, App.A, App.B 全ての前提**. ROADMAP「BG §1 + §4 + §5 並行可」は **段階的に修正**:
- §4 Lem 4.1, 4.2, Prop 4.3, Prop 4.4, Lem 4.5(b,c), Lem 4.10, Prop 4.11, Thm 4.12, Lem 4.13-4.15, Thm 4.16 は §1 不要で並行可
- §4 Lem 4.5(a), Lem 4.17, Thm 4.18, Thm 4.20 は §1 + Phase 1 待ち

### 4.2 §2 への依存集中

| target | 依存 | 状態 |
|---|---|---|
| §3 Thm 3.4 | §2 Prop 2.2, Thm 2.5 | wave 1 必須 |
| §3 Thm 3.6 | §2 Thm 2.6 ×2 | wave 1 必須 |
| §3 Thm 3.16 | §2 Prop 2.1 | wave 1 必須 |
| §4 Lem 4.17 | §2 Thm 2.6 | wave 1 必須 |
| **App.A Thm A.1** | **§2 Thm 2.6** | wave 1 必須 |
| §15 Thm 15.7 | §2 Thm 2.5 | wave 3 |

### 4.3 Isaacs 読み替えの corrections

| BG | 既存ノート | 正 |
|---|---|---|
| §1 Thm 1.13 | "Isaacs 4.31" | **Thompson critical subgroup (G 5.3.11-13)** ≠ Thompson P×Q (Isaacs 4.31). 別物 |
| App.A Thm A.2 | "Isaacs Thm 3.8.1 weakening" | **Isaacs FGT に 3.8.1 存在せず** (Gorenstein §3.8 番号). Isaacs Thm 7.3 + 7.5 path |
| App.A Thm A.3 | "Isaacs Thm 3.8.3" | 同上 |

---

## 5. Per-section ノート corrections (最小 Edit 推奨)

### s01_solvable.md
- L23, L165: Lem 1.1 "43+" → **"0 in §2+; only 2 self-cites in §1"**
- L23, L160: Prop 1.2 "22" → **"6"**
- 表 Prop 1.5 "28+" → "25", Prop 1.6 "16" → "13"
- L34, L217: Thm 1.13 ↔ Isaacs 4.31 conflation → **"Thompson critical (G 5.3.11-13), distinct from Isaacs 4.31 (Thompson P×Q)"**
- L28: mathlib "high" for Lem 1.7 → **"partial — (b)(d) missing"**
- Cor 1.19(b) coverage → **"`IsZGroup.coprime_commutator_index` 直接ヒット"**
- L37: Prop 1.15 ★★★ → **★ (Phase 1 Ch.3 完成)**
- Add: chief factor / Omega1 mathlib 不在 TODO

### s02_representations.md
- L9, L21: "§9 1-2 箇所" → **"§3 ×5, §4, §15, App.A; §9 = 0"**
- L70: "Jacobson Density 未実装" → **"`SimpleModule/Basic.lean:582` ✓"**
- L280-289: speculative §9/App.A refs → **actual cite list**
- L297-310: "Short path Thm 2.3 only" → **"INVERTED: Lem 2.3 forward=0 (defer); Thm 2.5+2.6 required"**
- L311: "skip 推奨" → **"§3/App.A 前提, 第 1 波必須"**

### s04_pgroups_small_rank.md
- L49 "計 20 結果" → "20 numbered: Lem ×8, Prop ×5, Thm ×4, Cor ×1"
- L107 "Ch.4 軽前提" → **"Ch.4 §4D Thm 4.36 + Cor 3.28 = HARD GATE (Lem 4.5(a))"**
- L116 "Phase 1 Ch.5 必須" → "新規 `ElementaryAbelian.lean` + `omega1` 独立可"
- L312: Thm 4.12 ↔ Isaacs Thm 5.7 broken → "G Satz III.13.5 or BG inline"
- L327 "Peterfalvi §4 p-group" → Peterfalvi §4 は Coherence, remove
- `Subgroup.rank` claim → "`Group.rank` 全体群 min-generators, BG `m(A)` 無対応"

### s05_narrow_pgroups.md
- L13: "r(R)≤2 or ..." narrow def → **§1 L354 verbatim "no elementary abelian of order p³ or ∃ R₀ cyclic, C_R(R₀)=R₀×R₁"**
- L29: Lem 5.1 ★★ → **★★★ (内部 hub 4 cites)**
- L94-96: "r(R)≤2 ⇒ SCN₃ empty" → **iff (Lem 4.7)**
- L189: "並行可" → "Lem 5.1-Cor 5.4 partial parallel; Thm 5.5-5.7 sequential"
- L173: §1 dep "Solvable" → **"Thm 1.13 (Thompson critical) explicit + Lem 1.9"**

### appA_pstability.md
- L13-14: "下流被引用 Thm 6.1, 6.2" → **"App.A is upstream of §6"**
- L24: "Isaacs Thm 3.8.1" → **"Gorenstein 番号. Isaacs FGT に存在せず. Isaacs 7.3-7.5 reroute"**
- L25: "Isaacs Thm 3.8.3" → 同上
- L29-61: "A.4(b) ≡ Isaacs 7.6 論理同値" → **"corollary (7.6 ⇒ A.4(b) trivial, 逆非自明). J(P) ⊴ G の追加要"**
- L194-203: "Ch.7 import ~50%" → **"~30%; BG §1+§2 完成必須"**
- L207-213: 前提に **BG §1 Prop 1.8/1.15(b) + BG §2 Thm 2.6 追加**

### appB_puig.md
- L6, 333, 343, 408, 504: "Lem B.1-B.5" → **"Lem B.1, B.2, B.3 + Thm B.4 の 4 結果. **B.5 不在**"**
- L374 A.5 §6-§16 で使わない → **"ZERO §6-§16 use; A.5 + App.B 共に orphan"**
- L76: "J(S) = L(S)" → **"`J(S) ⊆ L(S)` のみ. `Z(J(S)) ⊆ Z(L(S))` substitutable but not equal"**
- 全体: **"Phase 2a で skip 推奨. mathlib polish only revisit"**

### `_overview.md` corrections
- L95 (Phase 2a 第 1 波 App.B): **"App.B は App.A 不要で独立着手可"** → **"App.B は Thm A.5 dep (Lem B.3, Thm B.4 Step 3). しかも FT-orphan ⇒ skip 推奨"**
- L100 (App.A 並行): **"§6 と並行 or 後"** → **"§6 の直前 (上流). BG §1+§2 完成依存"**
- L111-114 (第 6 波 App.C/D/E): App.B を独立スロット **削除**, "Phase 2a 範囲外" mark

### `phase2_cross_refs.md` L34 (App.B)
"App.B: App.A 補強, J(S) ↔ L(S)" → **"App.B: depends on Thm A.5 only; FT-orphan; Phase 2a skip"**

---

## 6. Implementation order revisions (Phase 2a 第 1 波)

### 6.1 真の Phase 2a 第 1 波 (修正)

```
Wave 1a (即着手可, Phase 1 不要):
  - 新規 shared module 群 (5-7 並列実装可)
    - OpResidual.lean (3-4 日)
    - InvariantSubgroup.lean (3-4 日)
    - ChiefSeries.lean (4-5 日)
    - OmegaSubgroup.lean (1-2 日)
    - PRank.lean (1-2 日)
    - FrattiniPGroup.lean (1-2 日)
    - MinimalNormal.lean (1-2 日)
    - SCN.lean (1-2 日)
    - IsExtraspecial.lean (1-2 日)
    - IsMetacyclic.lean (1 日)
    - AutElementaryAbelian.lean (3-4 日)
  - BG §1 軽量パート (1.17, 1.18, 1.19, 1.20, 1.21, 1.22): ~5 日
  - §4 軽量パート (4.1, 4.2, Prop 4.3, Lem 4.10, Prop 4.11, Thm 4.12, 4.13-4.15): ~10 日

Wave 1b (Phase 1 Ch.3 完成依存):
  - BG §1 中盤 (Prop 1.4, 1.5, 1.6, 1.10, Lem 1.7, Lem 1.9, Lem 1.14): ~10 日
  - §4 Prop 4.4, Lem 4.5(b,c), Lem 4.6, 4.7: ~5 日

Wave 1c (Phase 1 Ch.4 §4D + Ch.1 §1B 完成依存):
  - BG §1 残 (Thm 1.8, Thm 1.11, Cor 1.12, Thm 1.13, Prop 1.15(a),(b), Prop 1.16): ~10 日
  - §4 Lem 4.5(a), Thm 4.16 (本体), Lem 4.17, Thm 4.18, Cor 4.19, Thm 4.20: ~15 日
  - §5 Lem 5.1-Cor 5.4 (Phase 1 Ch.4 partial OK): ~5 日

Wave 1d (Phase 1 Ch.6 完成依存):
  - §2 Prop 2.1, Prop 2.2 (Ch.6 §6F Clifford 必須), Prop 2.4, Thm 2.5, Thm 2.6: ~5 週
  - §5 Thm 5.5, Thm 5.6 (§4 後): ~3 週
  - §5 Thm 5.7 (Fitting Ch.2 完成依存): ~1 週

Wave 1e (BG §1, §2 完成後):
  - App.A 全体 (~7-10 日, shared module 既設前提): ~11-15 日合計
  - § 6 (Thm 6.1, 6.2): App.A 上流入力

SKIP: App.B + Thm A.5 (Phase 2a 範囲外, mathlib polish のみ).
```

### 6.2 Critical path (FT 経路重要度順)

1. BG §1 Prop 1.5, 1.6 (Peterfalvi 04.* も依存)
2. BG §2 Thm 2.5, Thm 2.6 (App.A + §3 入力)
3. Phase 1 Ch.7 Thm 7.5, 7.6 (App.A 入力)
4. App.A.4(b), A.4(c), A.5 (§6 入力)
5. BG §3 (Frobenius), BG §6 (Thm 6.1, 6.2)

DEFER: Lem 2.3 (Fong-Swan, 0 forward use), App.B + Thm A.5 (orphan), Thm 1.13 軽量化版 (Phase 1 完成待ちで `sorry`/`axiom` 可).

---

## 7. 次のステップ

1. **本 audit doc を Phase 2a 着手前必読リスト入り** (ROADMAP Phase 2a section に link).
2. **既存 per-section ノート 6 件に minimal correction** (audit タグ `(2026-05-23 audit 訂正)` 付与, 上記 §5 リスト).
3. **`_overview.md` の Phase 2a 着手順 L88-114 を Wave 1a-1e 構造に書き換え**.
4. **shared module 16 件のスタブ作成** (各ファイル docstring に audit 引用 + ROADMAP link). Phase 1 と並行可能性が大きいので, 順に着手.
5. **App.B 削除判断**: ROADMAP Phase 2a チェックリストから App.B + Thm A.5 を削除, App.A docstring に "skip rationale" を残す.

---

*作成: 2026-05-23. 検証元: BG mmd L310-585 (§1), L586-794 (§2), L1359-1788 (§4), L1789-1968 (§5), L4450-4516 (App.A), L4517-4758 (App.B). per-section ノート 6 件 (2026-05-22) を validate target として 4 視点 fresh re-investigation. 4-6 並列 sub-agent + synthesis. 出力: per-section 訂正リスト + 横断観察 + 着手順 revision.*
