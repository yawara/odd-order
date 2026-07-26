---
id: 8005
slug: s16-tame-embedding-restore
title: "BG §16 Thm I/II tame-embedding 構造の faithful 復元 (Pf consumer gate)"
created: 2026-06-15
---

# BG §16 Thm I/II tame-embedding 構造の faithful 復元 (Pf consumer gate)

## 背景

FT-critical §16 faithful 精査 (2026-06-15, commit `fdd8798a`) で、Thm I / Thm II が
tame-embedding 構造を lossy に落としていると判明。substantive 復元はユーザー裁可で **defer**
(speculative encoding を避け、Peterfalvi consumer の実需要に合わせる)。本 issue はその
deferred 復元タスク。**正本プラン = `notes/bg/s15_16_audit.md` §12.3**。

落ちている句:
- **Thm I** (`theoremI_…dichotomy`, mmd L4526): W=W₁×W₂ の normalizer-V 性質
  「N_G(W₀)=W ∀ nonempty W₀⊆W−W₁−W₂」+ W_i≠1、S=W₁S'/T=W₂T'/S'∩W₁=1/T'∩W₂=1/S∩T=W。
  (条件(5)「S,T とも II-V型」は `IsTypeNonI` で捕捉済 ⟹ 復元不要)。
- **Thm II** (`theoremII_tame_embedding`, mmd L4548): (Tii) supporting-subgroup system
  (M₁..Mₙ, (a)-(e)) + (Tiii) (Frobenius/cyclic complement/M_F not TI)。

## トリガー条件 (この issue を着手すべきとき)

**Peterfalvi が落ちた構造を消費し始めるとき**:
- **Thm I**: Pf `S10_MinimalSimpleStructure` (8.8) を**超えて** W=W₁×W₂ tame-embedding を
  消費する Pf 補題が出現したとき。
- **Thm II**: Pf (8.12)/(8.13) (現在 BG §14-15 gate で未形式化) が tame-embedding を
  消費し始めるとき。

現 lossy statement は現 consumer ((8.8), `S10_BGInterface`) には十分ゆえ、現 spine は block
しない (s15_16_audit §12.4)。⟹ Pf §10-13 が BG §14-15 landing で駆動し始めるまで保留。

## やること

- [ ] **Thm I 復元** (notes §12.3): mmd (1)(2) を復元。**(8.8) の tuple 形状
  (5 binder+9 conjunct, `⟨S,T,_W1,_W2,_W,hS,hT,hST,_hW,_hWcyc,hSnonI,hTnonI,hII,hcov⟩`) を
  壊さないこと** — clean 復元は (8.8) 同時更新が必須 (Pf レーン協調) か shape-preserving folding。
- [ ] **Thm II 復元** (notes §12.3): (Tii)(a)-(e) + (Tiii)。M_i family encoding (`Fin n → Subgroup G`)、
  per-M_i K_i (A0Set が K 依存)、(e) の「C_{H_i}(y)C_M(y)」積構造、(Tiii) Frobenius kernel/complement
  の **モデル化は Pf 消費形に合わせる**。
- [ ] 各復元後 **full build (S10_BGInterface / S10_MinimalSimpleStructure 含む) で consumer
  非破壊を検証**。sorry-neutral (既存 sorry の結論強化) を保つ (新 sorry'd theorem 追加は monitor abort)。

## 完了条件

Thm I / Thm II の statement が mmd L4526 / L4548 と faithful に一致 (tame-embedding 構造を含む)、
かつ Pf consumer (S10_BGInterface / S10_MinimalSimpleStructure + 新規消費側) が build-green。

## 参照

- 正本プラン: `notes/bg/s15_16_audit.md` §12 (特に §12.3 復元プラン、§12.1 consumer マップ)
- docstring 修正 (済): commit `fdd8798a`
- consumer: `OddOrder/Peterfalvi/S10_BGInterface.lean` (Prop 16.1)、
  `OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean` (Thm I, (8.8))
- mmd: `references/bg/local-analysis.mmd` Thm I=L4526 / Thm II=L4548 / "tamely imbedded" 定義=L4560

## 🧾 pending 移行 (2026-07-02 hub 全体レビュー)

本 issue は **trigger-gated task で trigger 未発火のまま** (Pf 側に tame-embedding 構造を
消費する補題は依然出現していない; BG 側 frontier は凍結)。open に置く意味が無いため
`issues/pending/` へ移動 — trigger (Pf consumer 出現) 発火時に再 activate。

---

## 🔓 2026-07-25 再活性化 (ユーザー指示)

ユーザーが本 issue を含む pending 4 件 (0106/0131/2053/8005) の再着手を指示。
pending の凍結/トリガー待ち/ユーザー判断待ちはいずれも解除 — main セッションが引き取る
(3 レーンとも 2026-07-23 から停止中・未マージ 0 を確認済、territory 衝突なし)。

## 📝 2026-07-25 実測再監査 + Thm I 側完了

**状態 drift**: 本 issue と正本プラン (§12.3, 2026-06-15) は「Thm I/II は sorried、復元 =
sorry-neutral な結論強化」を前提していたが、現在は **theoremI が実証明済み**
(dichotomy 本体 = typeP_duality + typeP_pair_inf_eq + Prop 16.1 bridges)、
**theoremII_tame_embedding も wrapper の 2 義務 (hPieceInv/hMaxUnique) が inline 消化済み**
(hPieceInv = order-determination 経由、hMaxUnique =
`maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape`)。
⟹ 復元 = 「新句の実証明」に性質が変わった。

**✅ Thm I 復元 完了 (commit `0c03444b8`)** — mmd L4526 (1)(2) を全て**実証明**で復元
(sorry 追加ゼロ):
- `W₁ ≠ ⊥ ∧ W₂ ≠ ⊥` (`kappaHall_ne_bot_of_isTypeP` 新設 — hKM 仮説は不要と判明し省略)
- normalizer-V: `∀ nonempty W₀ ⊆ W∖W₁∖W₂, N_G(W₀) = W`。**§12.3 の想定より軽かった** —
  ≤ は typeP_duality が返す Ẑ TI-性質 (従来 discard slot)、≥ は W cyclic→abelian の
  pointwise 固定。W₀ は Set (mathlib 現行 `Subgroup.normalizer` は Set を直接取る)
- `S = W₁ ⊔ S'`, `T = W₂ ⊔ T'`, `S'⊓W₁ = T'⊓W₂ = ⊥` (S'=[S,S], T'=[T,T]) —
  Thm 14.7 part (h) の S 側 (discard slot) + Mstar 側 (typeP_duality 再適用)。
  `sup_eq_and_inf_eq_bot_of_isComplement'_subgroupOf` 新設
- (8.8) consumer 更新 = rcases に discard 4 slot 追加のみ (レーン停止中ゆえ
  §12.3 の「(8.8) 同時更新」を clean に実施、shape-preserving folding 不要)

**残 = Thm II (Tii)/(Tiii)**。実測に基づく再評価:
- (Tii)(a)-(e) + (Tiii) は現在の theoremII (Ti + D⊆A(M) + conjunct-3) の**先にある
  未形式化の本物の数学** (M_i family の構成 = D 上の N[x] の共役類代表系 + (a)-(e) の検証)。
  plumbing ではない。
- 統合先の候補 2 択: (i) 実証明 campaign (BG §16 深部、multi-session)、(ii) §12.3 の
  encoding で statement-first endpoint (`theoremII_supporting_structure` 新設、sorried)。
- ⚠ (e) の積構造 (`C_{H_i}(y)C_M(y)` — ⊔ は over-approx) と (Tiii) の
  Frobenius kernel/complement モデル化は §12.3 自身が「Pf 消費形に合わせる」と留保。
  Pf (8.12)/(8.13) の per-element 半分は BG §16 側に landing 済
  (`existsUnique_maximal_centralizer_le_typeI_or_typeII`) だが、(Tii) family を消費する
  Pf 側 statement は依然不在。encoding 確定にはこの consumer 形が最良の情報源。
- 次アクション: (ii) statement-first を §12.3 encoding で書き、(e)/(Tiii) は
  Set-積の honest 形を採る (⊔ over-approx は不可)。その後実証明 campaign を積む。

---

## 🧾 2026-07-26 実測 + Thm II の A₀(M) 拡張 (main/hub session)

着手前の実測で、**この issue の「やること」チェックリストは既に大幅に stale** と判明した。

### 実測結果 (着手時点)

* **Thm I 復元**: 完了済 (commit `0c03444b8`、上記の追記どおり)。
* **Thm II (Tii)(a)–(e) + (Tiii)**: 上の「次アクション」が想定した (ii) statement-first ではなく、
  **実証明で完了済**だった:
  - `SystemOfSupportingSubgroups` (`TamelyImbedded.lean`) が (a)–(e) を book の文言どおり保持
    ((e) は `⊔` over-approx でなく **Set の積**で honest に encode 済 — §12.3 の留保どおり)。
  - `TheoremIIPackaging.lean` (795 行) が (c) = `coprime_centralizer_of_neighbour` (Lemma 14.13(a))、
    (d) = `clause_d_of_neighbour`、(Tiii) = `frobeniusTypeI_of_neighbour_typeII` を**実証明**し、
    `theoremII_tamelyImbedded` は **unconditional**。
* repo 全体の実 sorry は **1 件のみ** (Q₈ Brauer–Suzuki、issue 0147) — comment-strip 済 census。
* ⚠ ただし `theoremII_tame_embedding` の docstring に残っていた「Not axiom-clean: `_of_inputs`
  skeleton が sorry-bearing な §16 structure theorem を cite」は stale。

### 実測で見つかった本物の gap → 本 tick で解消

書籍 Theorem II (p. 132) は **"let `X = A(M)` or `X = A₀(M)`"** と両方を主張するが、
`theoremII_tamelyImbedded` は **`X = A(M)` のみ**だった ((Ti) と preamble
(`D ⊆ A(M)`、`|𝓜(C_G(x))| = 1`) は `theoremII_tame_embedding` が既に両方を covering)。
これを書籍どおり両方に拡張した:

* `aSet_subset_A0Set` / `kappaHall_conjClassSet_isPiElement` を
  `Peterfalvi/S10_TypePSupportA0.lean` から BG §16 へ**移設** (statement も証明も完全に
  BG §14/§16 — Peterfalvi に置かれていたのは配置ミス)。
* `escapingSharpSet_a0Set_eq_aSet` — 書籍 p. 132 の証明第 1 段
  (「`A(M) − M_σ` と `A₀(M) − A(M)` は normalizer `M` の TI-subset ⟹ `D ⊆ M_σ`」) に対応:
  **`D` は `X` の選び方に依らず同一集合**。⟸ は `ASet ⊆ A0Set`、⟹ は
  `theoremII_tame_embedding` の preamble `D ⊆ A(M)`。
* `coprime_centralizer_of_neighbour` を `x ∈ ASet M U` から **`x ∈ hatMsigma M`** に一般化
  (書籍の証明も `x ∈ \widehat{M_σ}` しか使っていない)。両方の `X` を同時に covering。
* `exists_systemOfSupportingSubgroups` / `theoremII_tamelyImbedded` を
  `{X} (hX : X = ASet M U ∨ X = A0Set M K)` 形に一般化。

* 書籍 Theorem II の括弧書き **「(and therefore `Hᵢ ≤ M'ᵢ`)」** を
  `SystemOfSupportingSubgroups.supporting_le_derived` として追加
  (BG Thm 10.2(c) = `Ch3.S10.Msigma_le_derived` から即出る)。

### 残り

無し。Thm I / Thm II とも書籍 (PDF p. 126 / p. 132) と faithful に一致し、
`theoremII_tamelyImbedded` は両方の `X` について unconditional・axiom-clean。

⟹ **本 issue は closed**。今後 Pf 側が (Tii) family を消費し始めたときに encoding が
合わないことが判明したら、その時点で新規 issue を立てる (本 issue の再オープンではなく)。
