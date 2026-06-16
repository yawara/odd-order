# (5.6) norm-weighted reweighting — multi-session plan (endpoint A 完遂)

**着手**: 2026-06-16 (lane-b session 43 cont.²⁹) / ユーザー裁可「(5.6) reweighting 着手」(cont.²⁸ fork)
**目的**: case-B (6.8.3) を closえる。ChatGPT (Pro 拡張) 検証で確定: case-B は reducible column を含む S₁ に
(5.6) を適用、‖χ‖²-weighted 和が必須、sidestep 無し ([[s08_6_8_3_reducibleS_chatgpt_answer]])。
**正本の数学**: notes/peterfalvi/s08_6_8_3_reducibleS_chatgpt_answer.md (Q1-Q4、(5.6) 正確な形 + 証明構造)。

## 🎯 decisive scoping 発見 (cont.²⁹、計画の根拠)

**S07 の (5.6) core 機構は既に general / norm-agnostic** — 恐れた「S07 書き直し」は不要の見込み:
- `CharacterPsiDecomposition τ χ ψ` (S07:1110) = 抽象 decomposition (一般 χ, ψ, X, Y)。inner-product lemma 群
  (inner_X_eq_coeff/inner_self_X/inner_self_chi_add_psi_eq 等) は norm-1 非依存。
- (5.6.2) opening bound `inner_self_Y_re_le_inner_self_psi` (S07:1444) = 一般 ψ、`‖χ‖²+‖ψ‖²=‖X‖²+‖Y‖²` +
  (5.4.a) `‖χ‖²≤‖X‖²` のみ使用、**norm-1 仮定なし**。docstring「Stated for the general ψ」「‖Y‖²≤a²‖χ₁‖²」(‖χ₁‖² 明示)。
- (5.6.2) integer-forcing core `int_eq_zero_of_sq_mul_le_of_two_mul_lt` (S07:1780) = `D a z : ℚ` を**抽象に取る**
  (`2a<D ⟹ λ=0`)。D = ∑ aᵢ²/‖χᵢ‖² でも ∑ aᵢ² でも通る。**norm-weighting 非依存**。

⟹ **norm-1/irreducible/Frobenius 仮定の所在 (要 trace・generalize)**:
- **(a) S08 contrapositive `sMember_degreeSumBound_of_not_coherent` (S08_CoherenceCorePart2:2650)**:
  `hF : IsFrobeniusGroup` を取り、結論で S₁ を `χmem : Fin k → IrreducibleCharacter ↥L` 列挙 (‖χ‖²=1 implicit、
  bound = ∑ χmem(1)²、denominator 無し)。**最大の generalize 対象**。`sMember_degreeSqReBound_of_not_coherent`
  (`.re^2` 版) も同様。
- **(b) forward (5.6) union 定理の bound interface** (要精査・次タスク): degree-ratio bound が ∑ aᵢ² (norm-1) か
  ∑ aᵢ²/‖χᵢ‖² (general) か。core が抽象 D ゆえ general 化は容易のはず。(6.6) application (case-A) は ∑ χⱼ(1)²
  (norm-1) を渡す (S07:1818 note) が、これは application 選択であって定理の制約とは限らない。
- **(c) Hyp (5.2) / R(χ) data の case-B 確立 = (5.3.b)**: certain-type で R(μ_j)=ω_ij^σ。**構築済 σ-isometry に接続**
  ((3.x) sessions 13-19、`dadeOrthonormalCharacterImageFamily` / signed family)。これが概念的に最も新規だが
  σ-data は既存。

## ▶ 次タスク (build order、未確定部は ⚠)

1. ⚠ **scoping 完了**: forward (5.6) union 定理 (S07、`coherentUnion`/`coherentPairChain`/retarget 系) の bound
   hypothesis 形を確認。一般 D を取るなら (b) は無改修。S08 (a) だけが本体。**次セッション第一手**。
2. **(a) S08 contrapositive の norm-weighted 版を追加実装**: `sMember_degreeSqNormBound_of_not_coherent` (新名)、
   `hF` 落とし、結論を一般 character family + bound = ∑ χ(1)²/‖χ‖² に。既約版は特殊化として保持 (case-A 無傷)。
   ⟹ これが `2ψ(1)η₁(1) ≥ ∑_{S₁} χ(1)²/‖χ‖²` を case-B に与える。
3. **(c) case-B の Hyp (5.2) 確立 ((5.3.b))**: S = induced char 集合に対し R(μ_j)=ω_ij^σ で coherence axiom。
   構築済 σ-isometry / signed family から。⚠ 最も精査要 (§5 Hyp 5.2 の Lean encoding ↔ σ-data の対応)。
4. **case-B (6.8.3) L4 assembly**: 上記 + FPF tower (cont.²⁶、`false_of_w2_break_arith` 系) + (5.6) X-sum identity
   (mixed X、`∑_X χ(1)²/‖χ‖²=|W₁||H:Z|(|Z|-1)`) → `false_of_coherentXunionYset_caseB_of_not_coherentS` →
   capstone `sibleySetup_is_coherent` の case-B branch。

## 設計原則
- **additive**: 既約版 (`sMember_degreeSumBound_of_not_coherent` 等) は case-A が使う → 削除せず保持。
  norm-weighted 版を**追加**し、既約版をその特殊化に (可能なら) するか並置。
- **build-green + axiom-clean / commit per piece**。core (S07/S08 CorePart) 触る commit は full build。
- **(5.6) 正確な数学は chatgpt_answer.md Q1-Q4 が正本** (射影係数 1/‖χᵢ‖²、quadratic `λ²∑(aᵢ²/‖χᵢ‖²)−2aλ+‖Z‖²≤0`、
  `b=2a/∑(aᵢ²/‖χᵢ‖²)`、(5.4)(5.5) で τ₂ 等長)。

**正本=本ファイル + chatgpt_answer.md。S07 core は norm-agnostic 判明、reweighting は S08 application 層 (a)+(c) が本体。
次=forward (5.6) bound 形の scoping → S08 norm-weighted 版追加。**

## cont.²⁹ 続: scoping 完了 — core = 抽象エンジン `coherentDegreeSumBound_of_not_coherent` の一般化

S08 contrapositive の証明を trace して norm-1 の所在を**正確に**特定:
- `sMember_degreeSumBound_of_not_coherent` (S08CP2:2650) は抽象エンジン **`coherentDegreeSumBound_of_not_coherent`
  (S08_CoherenceCorePart1:2451)** を呼ぶ。`hF` は `sBreakPair_fields hF` で break-pair fields を**産む**のに使うのみ
  (定理本体の制約でない)。
- **🎯 真の (5.6) core = `coherentDegreeSumBound_of_not_coherent` (S08CP1:2451) が norm-1 を bake**:
  - `χmem : ι → IrreducibleCharacter ↥L` (既約族)。
  - `hmemortho : ∀i∈s,∀j∈s, ⟨χmem i, χmem j⟩ = if i=j then 1 else 0` (**正規直交**、対角 = ‖χmem i‖²=1)。
  - `hχχ : ⟨χ,χ⟩=1` (break member ψ も norm-1)。
  - 出力 bound = `∑ⱼ (degⱼ)² ≤ 2a` (norm-1 形、denominator 無し)。
- low-level (`CharacterPsiDecomposition` S07:1110 / opening bound S07:1444 / `int_eq_zero_of_sq_mul_le_of_two_mul_lt`
  S07:1780) は norm-agnostic と確認済 ⟹ **一般化は組立エンジンの再 thread が本体**。

### 🔴 core build target (次セッション focused)
**`coherentDegreeSqNormBound_of_not_coherent`** (新、additive、既約版は保持):
- `χmem : ι → IrreducibleCharacter` → 一般 character family (ClassFunction、または "coherent member" 型 + norm field)。
- `hmemortho … = if i=j then 1 else 0` → `… = if i=j then ⟨χmem i,χmem i⟩ else 0` (直交、一般 norm)。
- `hχχ=1` → `hχχ = ‖χ‖²` (or break member も一般 — 但し (6.8.3) では ψ=Ind θ 既約ゆえ ψ は norm-1 のまま可)。
- 出力 = `∑ⱼ (degⱼ)²/‖χmem j‖² ≤ 2a` (weighted)。
- 証明 = ChatGPT Q4 (chatgpt_answer.md): 射影係数 1/‖χᵢ‖²、quadratic `λ²∑(aᵢ²/‖χᵢ‖²)−2aλ+‖Z‖²≤0` →
  `int_eq_zero_of_sq_mul_le_of_two_mul_lt` (D=∑aᵢ²/‖χᵢ‖²、既に抽象 D 対応) で λ=0。低レベル norm-agnostic
  piece を最大流用。⚠ 規模大 (40-field 級エンジン)、focused session 推奨。

### 残 (core 後)
- **break-pair fields for reducible S**: `sBreakPair_fields` / `exists_coherentBreakPair` (S08CP1:965、`hSbirr` 全既約要求)
  を reducible 対応に。conjugate-pair enumeration は involution ベースで既約非本質の可能性 (要精査) だが、
  各 pair の norm-1 を使う箇所は要 weight 化。
- **(5.3.b)** Hyp(5.2) case-B 確立 (R(μ_j)=ω_ij^σ、σ-isometry 接続)。
- **case-B X-sum identity** (mixed X、`∑_X χ(1)²/‖χ‖²=|W₁||H:Z|(|Z|-1)`) + L4 assembly + FPF tower。

**正本=本ファイル。core build target = `coherentDegreeSqNormBound_of_not_coherent` (S08CP1:2451 の weighted 版)。
次=core build 着手 (focused、Q4 が証明正本)。**

## cont.²⁹ 続²: 完全 scoping — core = weighted `xAdjoinStep` (189 行 τ₂ 構築) + X-sum は既済
さらに trace して reweighting の**完全 scope** を確定:
- `coherentDegreeSumBound_of_not_coherent` (S08CP1:2451) は薄い contrapositive wrapper、本体は
  `exact hnc ⟨xAdjoinStep …⟩`。**真の core = `xAdjoinStep` (S08CP1:2262、≈189 行の τ₂ coherent-extension 構築)**。
  正規直交 member から S₁∪{ψ,ψ̄} の coherent 拡張を建てる ((5.6.3) τ₂)。norm-1 はここで本質使用。
- **`XAdjoinStepInput` 構造体 (S08CP1:2583、≈52 行)**: `χmem : ι → IrreducibleCharacter` + `hmemortho` (正規直交)。
  + **8 個の `xAdjoinStepInput_of_*` builders** (S08CP1×8 / S08Core×36ref / S08CP2×13ref)。
- **✅ X-sum 側は既に norm-weighted で形式化済**: `sum_div_normSq_induce_kernelFilter_eq` (S08CP1:~2520) =
  `∑_{χ∈S(A)} χ(1)²/‖χ‖² = [G:H]·(|H:A|−1)` (`χ 1 ^2 / inner χ χ` 形)。⟹ **case-B X-sum identity は無改修で使える**。

**⟹ 完全 scope**: (5.6) reweighting = (1) `XAdjoinStepInput` struct を weighted 化 (`χmem` 一般 character、
`hmemortho = if i=j then ‖χmem i‖² else 0`)、(2) **`xAdjoinStep` (189 行 τ₂) を weighted 一般化** [core、最重]、
(3) builders を weighted 化 (or case-B 用 1 builder のみ)、(4) `coherentDegreeSqNormBound` wrapper、
(5) break-pair for reducible S、(6) (5.3.b) Hyp(5.2)。証明正本 = chatgpt_answer.md Q4 (射影 1/‖χᵢ‖²、quadratic)。
**規模: major multi-file focused build (189 行 core + struct + builders)。clean context の focused session 推奨。**

**📍 現在地 (cont.²⁹ 完了時点)**: (5.6) reweighting は**完全 scoping 済・着手準備完了**。X-sum 済、core = weighted
`xAdjoinStep`。FPF tower (cont.²⁶) は別 obligation で H/H′ 実データ済 (H′/W₂+assembly 残)。次セッション第一手 =
weighted `XAdjoinStepInput` struct + `xAdjoinStep` core (Q4 が証明正本)。**正本=本ファイル + chatgpt_answer.md。**

## cont.³² (session 43 後半): (5.6) core 精密 diff-plan — weighting は member family のみに局所化
xAdjoinStep の norm-1 entry point を grep で精密特定 ⟹ **weighting は member family (χmem) のみ**:
- **break member ψ (=χ) と anchor χ₁ (=η₁) は (6.8.3) で常に既約** ⟹ `hχχ=1`/`hchi1chi1=1`/`hχbarχbar=1` は**不変**。
- 一般化対象 = **member family χmem の `hmemortho = if i=j then 1 else 0` → `if i=j then ‖χmem i‖² else 0`** +
  bound `hDeg : 2a < ∑ deg²` → `2a < ∑ deg²/‖χmem i‖²`。
- **🎯 最深核 = `crux1_of_memberFamily` (S08CP1:1888、92 行)**: weighted projection 計算。norm-1 使用 =
  L40 `hmemortho i j` (member 直交)、L68 `hmemortho i₁ i₁` (anchor、norm-1 のまま可)、L74 `hDeg` (∑deg²)。
  ⟹ ここを weighted 化 (1/‖χᵢ‖² 射影、quadratic D=∑deg²/‖χᵢ‖²、`int_eq_zero_of_sq_mul_le_of_two_mul_lt` は抽象 D 対応済)。
- `xAdjoinStep` (189 行) は大半 pass-through (crux1 + retarget 呼ぶ)、weighted crux1 を呼べば追従。
- struct `XAdjoinStepInput` (S08CP1:2583、52 行): `χmem : ι→IrreducibleCharacter` → 一般 character + norm field、
  `hmemortho` 対角 weighted。

**⟹ (5.6) core build 順 (additive、~280 行)**: (1) weighted struct → (2) **`crux1_of_memberFamilyW` (92 行、最重・Q4 正本)**
→ (3) `xAdjoinStepW` (189 行、pass-through) → (4) `coherentDegreeSqNormBound_of_not_coherentW` wrapper。
break-pair for reducible S は別途 (`exists_coherentBreakPair` の conjugate-pair enumeration、既約非本質の可能性)。

**📍 session 43 総括 (19 commits)**: FPF tower 完結 (hfpf 実 Sibley data) + ChatGPT #1 verdict (sidestep 無し) +
(5.6) core 精密 diff-plan (crux1 最深、weighting=member family のみ)。**残=(5.6) core build (crux1W 中心、major focused)。**
正本=本ファイル + chatgpt_answer.md。**次=weighted struct → crux1W build。**
