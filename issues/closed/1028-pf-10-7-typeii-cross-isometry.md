---
id: 1028
slug: pf-10-7-typeii-cross-isometry
title: "Pf (10.7) exists_typeIICrossIsometryData 形式化 (Coq Frob_der1_type2、3 items)"
created: 2026-07-13
---

# (10.7) type-II cross-isometry — lane-a frontier (hub RULING #2 割当)

> hub RULING #2 (9087、2026-07-13): 型III/IV char-core 完遂後の lane-a 次 frontier =
> `exists_typeIICrossIsometryData`。**localize 済 = genuine gap** (clean-heir rewire でない;
> S12_TypeIIFrobenius:1206 docstring が 3 items の未形式化数学を明示)。1020 (10.7)' cluster の続き。

## 対象

`exists_typeIICrossIsometryData` (`S12_TypeIIFrobenius.lean:1206`、bare sorry :1221)。
Peterfalvi **(10.7)** = Coq **`Frob_der1_type2`**。consumer = `TypeIICrossIsometryData.elim`
(:1235、**既に proven**、M-side pin `muColumn_tau1_pin` 使用) → `typeII_HU_frobenius_of_coherent`
(§10/§14 type-II 構造、S12_MaximalBasic 経由で spine 隣接)。⟹ gap は package (`TypeIICrossIsometryData`)
の**生成**のみ; その elimination (contradiction 導出) は済。

## 3 items (docstring S12_TypeIIFrobenius:1195-1204、全て genuine 未形式化)

1. **τ₂ 構成** (S-side cross-isometry map)。
2. **ν^{τ₂} の pin**: (5.8) (Coq `coherent_prDade_TIred`) via (3.7) 係数 rigidity + (3.2.d)
   V-vanishing → ν^{τ₂} を signed row sum に。**typeP_pair sphere (issue 0098 item 1)**。
3. **support disjointness** ((8.18.b) via (8.13.c4)): `Ã₁(M) ∩ Ã(S) = ∅` — M が kernel M_F の
   Frobenius でない (Hyp (10.1)) ゆえ S の共役が M を support しない; (8.10)/(8.15)/(4.7) で
   `cross_zero` + (共役 pair 差 trick で) `zeta_lam_ortho`。**§8 support geometry (S10)**。

## 進め方 (次 iteration、fresh context)

1. **Coq `Frob_der1_type2` (PFsection10.v 付近) 精読** — 3 items の証明構造・依存を把握
   (`coq/theories/PFsection10.v`、コメントで行間補完; [[feedback-ask-chatgpt-for-elided-gaps]] 可)。
   関連 PFsection3 (coefficient rigidity 3.7 / V-vanishing 3.2.d)、PFsection5 (5.8 coherent_prDade_TIred)、
   PFsection8 (8.18.b/8.13.c4 support)。
2. **上流優先**: item 3 (§8 support geometry、S10) が最も self-contained な可能性 → 先に精査。
   item 2 は typeP_pair (0098) に依存 — その state を先に確認。
3. `TypeIICrossIsometryData` structure (S12_TypeIIFrobenius 上方) の field を確認し、各 item が
   どの field を埋めるか map。
4. build-green + #print axioms 検証 (authoritative のみ、自作 metaprogram 不可 —
   [[verify-which-sorry-via-print-axioms-not-metaprogram]])。

## 参照

hub RULING #2 = 9087。1020 ((10.7)' axiom-clean chain)、0098 (typeP_pair、item 2)、
S12_TypeIIFrobenius:1206 (target) / :1235 (elim、proven)。Coq PFsection10.v `Frob_der1_type2`。

## ✅ UPDATE (2026-07-13、lane a): assigned target は既に done — off-spine LEGACY と確定、hub 裁定要請

RULING #2 handoff の STEP 0 (note 全読 + repo 全数 authoritative 検証) で **plan が stale と判明**。
handoff は `c8528167` (2026-07-10) snapshot で書かれたが、その後 **3 obligation 全て + honest heir が
pair-witness route で landed 済**(全て HEAD 祖先、tree clean)。**新規 Lean 変更は不要・不可**(anti-pattern)。

### 真の状態 (`#print axioms` authoritative、build 4150/4150)
- **obligation 1** `typeII_T2_coherent` (S12_TypeIIFrobenius:1019、`408e9650`) = AXIOM-CLEAN
- **obligation 2(a)** `typeII_nu_tau2_dichotomy` (S12_TypeIIColumnPin:794、`b5a20e11`) = clean
- **obligation 2(b)** grid transpose = 新 leaf `S12_TypeIIGridTranspose.lean` (sorry 0) ⟹ **issue 9079 完了**
- **obligation 3** support disjointness = `exists_typeIICrossIsometryData_at_pair` (S12_TypeIICrossIsometryPair:1345、**sorry 0**、AXIOM-CLEAN) の 4 field で discharge 済
- **honest heir (generic S)** `typeII_HU_frobenius_of_coherent'` (S12_TypeIICrossIsometryPair:1493) = **AXIOM-CLEAN** — spine (10.8) `S_not_coherent_unconditional` が consume
- **assigned target** `exists_typeIICrossIsometryData` (:1206) = `[propext, sorryAx, …]` — **off-spine legacy**

### ⟹ RULING #2 の "genuine gap (clean-heir rewire でない)" 分類は誤り
9087 census (lines 35-36) の「legacy import-DAG artifact (honest heir 既存)」が正しかった。(10.8) `S_not_coherent`
と完全同型の意図的 legacy/honest split(両ファイル docstring 明記)。`exists_typeIICrossIsometryData` は
Frobenius (上流) にあり、下流 `_at_pair` を cite すると import **cycle** ⟹ in-place 閉包不能。埋めるには pair 機構
の upstream 重複移設が要り、既に proven な heir があるのに sorry を消すための duplication = CLAUDE.md anti-pattern。
spine 文字核 `card_kappaHall_lt_of_isTypeIIIorIV` は既に axiom-clean (AxiomsCheck:7797)。詳細 =
notes/peterfalvi/s10_7_derived_frobenius.md update¹¹。

### hub 裁定要請 (lane-a owned char-core frontier 枯渇)
本 target は anti-pattern ゆえ埋めない。genuine な次手 = hub-level:
1. **legacy (10.7)/(10.8)/(10.10) subtree retire + `feitThompson` の honest-heir rewire** (issue 1025 を
   card_kappaHall → feitThompson capstone へ拡張)。`exists_typeIICrossIsometryData` 他 legacy sorry を
   **削除**でき feitThompson dirty を honest に減らす。feitThompson wiring + cross-lane §14/15/16 consumer に
   触れる ⟹ hub sequencing 要 (AxiomsCheck:7794)。
2. **9079 close** (obligation 2(b) 完了)。
3. **stale docstring cleanup**: `_at_pair` の false-sorry 記述、本 issue/`exists_typeIICrossIsometryData` の
   "genuine gap" 表記。
⟹ 本 issue は「done、legacy 分類」で close 候補。次 lane-a 方向を 9087 で hub に上げる。
本 session 完遂 = 型V (6.5) 9089 + card_kappaHall 1025。
