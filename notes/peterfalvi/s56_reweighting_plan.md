> ⚠ **2026-06-17 SUPERSEDED (部分)**: (6.8.3)/(5.6)-weighted/case-B capstone の現 source-of-truth は
> **[`s08_6_8_3_gap_resolution.md`](s08_6_8_3_gap_resolution.md)** (hub 13-agent workflow + 検証で確定:
> 数学 gap=0、norm-weighted (5.6) エンジン `S08_CoherenceWeighted` は既に repo に sorry-free、残務は glue のみ)。
> 本ファイルの cont.³⁴〜⁴⁷ には retract 済の overclaim が多数。**特に「S07 core を reweight する multi-session 作業」「main (5.6) を新規構築」系の本文は MOOT**: norm-weighted (5.6) エンジンは既に着地済 (`S08_CoherenceWeighted`)。残るのは case-B への配線 (glue) のみ。数学・残務の判断は resolution note を優先し、本ファイルは history として残置。

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

## cont.³³: 🎯 crux1W 大幅 de-risk — lambda engine 既に weighted、残=orthogonal projection
crux1_of_memberFamily の証明を精読 ⟹ **(5.6.2) forcing engine `lambda_eq_zero_and_Z_eq_zero` (S07_Coherence) は
既に完全 norm-general**: `mc : ι→ℝ` (norms)、`horth` 対角 `mc i`、`hψ : ‖ψ‖²=a²·mc i₁`、`hr₁ : rc i₁·mc i₁=1`、
bound `2a < ∑ rc²·mc` を取る。原 crux1 は `mc=fun _=>1`/`rc=deg` で instantiate。**weighted は `mc i=‖χᵢ‖²`、
`rc i=deg i/mc i` ⟹ `∑rc²·mc=∑deg²/‖χᵢ‖²` = ChatGPT Q4 と完全一致**。⟹ 最深 engine は無改修で使える。

**残る key piece = orthogonal projection** `exists_indexed_intProjection_of_orthonormal_ZIrr` (S08CP1):
orthonormal (`horth=if i=j then 1`) + **整数係数 `c:ι→ℤ`**。weighted は norm `mc i` 直交 + **有理係数 `⟨φ,vcᵢ⟩/mc i`**
(⟨φ,vcᵢ⟩∈ℤ だが /mc i で有理)。⟹ 新規 `exists_indexed_projection_of_orthogonal_ZIrr` 要 (~50 行、
Z=φ−∑(cZᵢ/mc i)•vcᵢ、⟨Z,vcᵢ⟩=cZᵢ−(cZᵢ/mc i)·mc i=0)。

**⟹ crux1W build**: (1) orthogonal projection lemma [新規 key] → (2) weighted hcoeffval/hY (rc i=deg i/mc i) →
(3) `lambda_eq_zero_and_Z_eq_zero` (無改修) で λ=0 → μ=−a。**当初の「92 行 monolith rewrite」より遥かに局所的**。
正本=本ファイル + chatgpt_answer.md Q4。次=orthogonal projection lemma build。

## cont.³⁴: ✅✅ crux1W (最難核) DONE — 残 xAdjoinStepW は 189 行コピー+4 変更 (機械的)
**(5.6) weighted core の最難 piece `crux1_of_memberFamilyW` COMPLETE** (commit、axiom-clean)。
de-risk (lambda engine 既 general) + mc-parameter 設計 (inner-self-real 回避) + orthogonal projection で、
maxed context でも build (4→1→green)。

**📍 (5.6) core 現状 (S08_CoherenceWeighted.lean)**:
- ✅ `XAdjoinStepInputW` struct
- ✅ `exists_indexed_projection_of_orthogonal_ZIrr` (orthogonal 整数射影、有理係数 cZ/mc)
- ✅ `crux1_of_memberFamilyW` (weighted (5.6.1)/(5.6.2) 核、mc/rc=deg/mc/lambda_eq_zero)

**残 = `xAdjoinStepW` = xAdjoinStep (S08CP1:2262-2451、189 行) のコピー + 4 変更のみ** (他は norm-agnostic で不変):
1. **signature**: `hmemortho` 対角 `(mc i:ℂ)` + `hDeg : 2a < ∑deg²/mc i` + 引数 `mc/hmempos/hanchorNorm` 追加。
2. **hchi1chi1** (L2352): `rw [hmemortho i₁ hi₁ i₁ hi₁, if_pos rfl, hanchorNorm]` (mc i₁=1 で 1)。
3. **hcoeffval の key** (L~2410): `rw [hmemortho i₁ hi₁ i hi] at key` 後、i=i₁ case で `mc i₁` を hanchorNorm で 1 化
   (rcases i i₁ の subst 枝で hanchorNorm 適用)。
4. **crux1 call** (L~2420) → `crux1_of_memberFamilyW … mc hmempos hmemortho hanchorNorm hcoeffval … hDeg`。
不変部: Da/hYeq/hDaY_ZIrr、hmemχ/hmemχbar/hmembarχ/hmembarχbar、Dmem/hortho_mem/hXortho/hfound、hcrux2/hτdiffZ、
`retarget_isCoherent_of_extensionImage` call (hχχ/hchi1chi1 norm-1 で不変)。
**→ その後 wrapper `coherentDegreeSqNormBound_of_not_coherentW` (xAdjoinStepW を contrapose、~10 行) + break-pair for
reducible S (`exists_coherentBreakPair` 一般化、別途)。**

**📍 session 43 総括 (23+ commits)**: FPF tower 完結 + ChatGPT #1 verdict + (5.6) core 最難核 crux1W 完成。
残 (5.6): xAdjoinStepW [189 行機械コピー+4 変更] + wrapper + break-pair。**正本=本ファイル。次=xAdjoinStepW コピー (fresh context 推奨、189 行ゆえ).**

## cont.³⁵: ⚠ 訂正 — xAdjoinStepW (IrreducibleCharacter) は vacuous、真の残務=reducible member-decomp (5.3.b)
cont.³⁴ の「forward engine COMPLETE」は **overclaim**。verbatim extract の xAdjoinStepW は `χmem : ι →
IrreducibleCharacter` のまま ⟹ hmemortho `⟨χmem i,χmem i⟩=if i=j then mc i` で既約は ⟨χmem i,χmem i⟩=1 ゆえ
**mc=1 強制 = vacuous weighting**(xAdjoinStep と同等、reducible-S に無価値)。

**🎯 χmem を ClassFunction に変えると line 360 で詰まる**: `Dmem := memberExtensionDecomposition hyp hconj hS₁
(χmem i) …` が **`memberExtensionDecomposition` (S08CP1:1585) の `(χ : IrreducibleCharacter ↥L)` 引数を要求**。
⟹ xAdjoinStep の **per-member ν-aux 分解 Dmem (= R(χᵢ) image family) は IrreducibleCharacter 専用**。
reducible μ_j では R(μ_j) を別構成 (σ-image) で与える必要。

**⟹ (5.6) reweighting の真の構造**:
- ✅ **crux1W** = member 分解 (Da, Dmem, R(χᵢ)) を**所与**とした weighted projection + λ-forcing。genuine・reusable。
- 🔴 **残 core = reducible member-decomposition**: reducible μ_j の per-member image family R(μ_j) を σ-isometry
  から構成 (= ChatGPT が言う **(5.3.b): R(μ_j)=ω_ij^σ で Hyp(5.2) を case-B 確立**)。`memberExtensionDecomposition`
  の reducible 版 (σ-image ベース) が要る。**これが (5.6) の本丸の残り**(projection でなく member の R 構成)。
  構築済 σ-isometry (`dadeOrthonormalCharacterImageFamily`、(3.x) sessions) に接続。
- その後 xAdjoinStepW を reducible Dmem で再構成 → wrapper → break-pair。

**📍 session 43 honest 総括**: FPF tower 完結 + ChatGPT #1 verdict + (5.6) の **projection 核 crux1W + orthogonal
projection + struct** 完成(genuine)。xAdjoinStepW は IrreducibleCharacter 版 (vacuous、committed だが要再構成)。
**真の残 = reducible member-decomp R(μ_j) via σ (=(5.3.b))** → これが (5.6) の最後の hard piece。**正本=本 cont.³⁵。**

## cont.³⁶: reducible member-decomp の精密構造 — ofProjection R(μ_j) via σ
`memberExtensionDecomposition` (S08CP1:1585) の本体 = `CharacterPsiDecomposition.ofProjection
(dadeOrthonormalCharacterImageFamilyOfDiff hyp hconj χ hreal hdiffsupp)` (IrreducibleCharacter χ の
χ−χ̄ の Dade σ-image を R(χ) image family として projection)。

**⟹ reducible μ_j の member-decomposition build target**: `CharacterPsiDecomposition.ofProjection (R(μ_j))` で
**R(μ_j) = reducible column μ_j の σ-image orthonormal family**。`dadeOrthonormalCharacterImageFamilyOfDiff` は
IrreducibleCharacter 専用ゆえ、μ_j 用の σ-image family producer が要る (= ChatGPT (5.3.b): R(μ_j)=ω_ij^σ)。
構築済 σ-isometry ((3.x) `dadeOrthonormalCharacterImageFamily` / signed family、sessions 13-22) に接続。

**▶ 次セッション (fresh context 推奨) の第一手**: (1) `dadeOrthonormalCharacterImageFamilyOfDiff` の output 構造
(R(χ) = OrthonormalCharacterImageFamily?) を読む → (2) μ_j (= certain-type column) の σ-image が同型 family を産むか
(構築済 σ-data から) → (3) `CharacterPsiDecomposition.ofProjection (R(μ_j))` で reducible member-decomp → (4) これを
xAdjoinStepW の Dmem に差し込み (memberExtensionDecomposition の reducible 版) → forward engine 完成 → wrapper。
**正本=本 cont.³⁶。crux1W (projection) done、残=R(μ_j) via σ の member-decomp (=(5.3.b)、§5↔§6 bridge、deep)。**

## cont.³⁷ (2026-06-16, lane-b 再開): 🚨🚨 **cont.³⁵/³⁶ 誤診を訂正 — R(μ_j) は `certainTypeR` として既存** + 一般 engine + bound wrapper landed

lane-b 再開セッション。cont.³⁶ の推奨第一手「R(μ_j) を σ から新規構成 (deep §5↔§6 bridge)」を実行しようとして
**grep/Explore で R(μ_j) が既に完全構築済と判明**。cont.³⁵/³⁶ の「deep bridge 未構成」評価は **誤診**だった
(lane-b 自身が 6/14 に S06_CertainTypeCoherence で構築したものを cont 系ノートが見落とし)。

### ✅ 既存と判明 (cont.³⁶ が「残 hard core」と誤認していた構造):
- **`certainTypeR`** (`S06_CertainTypeCoherence.lean:639`、commit `72798461`) = **reducible column μ_j の
  `OrthonormalCharacterImageFamily τ (columnSum χ₂)`**。`imageSet` = σ-image family (2w₁ 元、`certainTypeRImage`)、
  `mem_ZIrr`/`orthonormal`/**`image_eq` (= `dadeICM_columnDiff_eq_sum`: τ(μ_j−μ̄_j)=∑R(μ_j))** 全 4 field 充足。
  = **まさに (5.3.b) R(μ_j)=ω_ij^σ。cont.³⁶ の build target は完成済**。
- **`certainTypeDecompositionDa`** (`S06_…Coherence.lean:684`、commit `0987d047`) = reducible μ_j 用
  `CharacterPsiDecomposition τ μ_j (a·η₁)` (= `decompositionDaFromDadeOfDiff` の reducible 版、ofProjection 経由)。
- τ = `dadeIntegralCharacterMap h.dade0 h.tau` (h : Hypothesis46)。`xAdjoinStepW` の τ
  (`hyp.fullDadeIsometryData hconj`、hyp : S04.Hypothesis) との橋は **`certainTypeSet_isCoherent_tau`**
  (`S08_CaseBCoherence2.lean:1651`) が `hmapagree`/congrMap で既に処理。

### ✅ 本セッションの 2 commit (genuine、build-green+axiom-clean):
1. **`xAdjoinStepW` 一般化** (`6a59b41e`): `χmem : ι → ClassFunction`(was IrreducibleCharacter)+ `Dmem`/
   `hortho_mem`/`htau1Dmem` を**パラメータ化**(was 内部 `memberExtensionDecomposition` 構成)。cont.³⁵ の
   「vacuous」(全 member 既約) を解消。既約 member→`memberExtensionDecomposition`、reducible column→
   `certainTypeR` 経由 `ofProjection`。**crux1W は元から `χmem : ClassFunction` 一般** ゆえ engine 本体は無改修、
   既約依存は `Dmem`/`hortho_mem`/`htau1Dmem` obligation に hoist しただけ。
2. **`coherentDegreeSqNormBound_of_not_coherentW`** (`c7c3f6a0`): (5.6) weighted bound = `xAdjoinStepW` の
   contrapose (`∑deg²/mc ≤ 2a`)。case-A `coherentDegreeSumBound_of_not_coherent` (CP1:2451) の reducible 版。

### 🎯 **真の残務 = ~350-550 LOC の well-defined wiring 3 ピース** (Explore 2 件で精密 trace、deep bridge ではない):
sole sorry = `sibleySetup_is_coherent` (`S08_CoherenceTheorems.lean:59`) の case-B (CertainType) 枝。
全 case-B files (CaseBAssembly/CaseBCoherence2/CaseBEndgame/S06_…Coherence/CoherenceWeighted) は **sorry-free**。
glue shell **`coherentXunionYset_caseB_of_glued`** (`S08_CaseBCoherence2.lean:1616`、sorry-free) は
`cX : IsCoherent hyp.tau (Xset W2)` を**入力**に取り `IsCoherent (Xset W2 ∪ Yset)` を産む。残 gap:
- **(A) irreducible X-chain assembly → cX** [~200-300 LOC、最重]: reducible column base
  (`certainTypeSet_isCoherent_tau`) に irreducible X-members を **weighted `xChainCoherentW`**
  (= 本セッション engine `xAdjoinStepW`/bound wrapper を使う weighted X-chain、未構築) で adjoin → cX。
  case-A template = `Xset_commutator_isCoherent_…_of_frobenius` (`S08_CoherenceCore.lean:1884`)、
  unweighted chain = `xChainCoherent` (CP1:2701)。⚠ case-B は base に reducible column を含むので
  (5.6) sum が weighted → unweighted `xChainCoherent` 不可、**weighted 版が要る** (本セッション engine の用途)。
- **(B) `hmapagree`** [~50-100 LOC]: `certainTypeSet_isCoherent_tau` の Dade-map 一致 (h.dade0/tau ↔ hyp.tau on H^#)。
- **(C) extension assembly (ν, hagreeX/Y, hmixed)** [~100-150 LOC]: cX.extension + coherentYset.extension を
  ν に合成 → glue 呼び出し。glue の他入力 (hpair/D/hDτ/hgen) は ✅ 済 (`caseB_Xset_orthogonal_Yset` 等)。
- critical path: (B)→(A)→(C)→glue→L4 (`S08_CaseBEndgame` 算術 spine 済)→sorry 解消。

### ⚠ 注意 (次セッションへ):
- **R(μ_j) を新規構成しない** (= certainTypeR、再 build 禁止)。cont.³⁶ の「第一手 (1)-(4)」は obsolete。
- **`S08_CaseBAssembly` の per-constituent 機構** (`caseB_constituentDecomposition`/`caseB_phi_family`/
  `caseB_per_phi_anchored*`) が (A) の weighted X-chain と同一経路か別経路かは**未確認**
  (glue 入力 D=per-φ images を産む側に見える)。(A) 着手前にこの機構の終端定理が何を産むか精査要
  (weighted xChain を呼ぶのか、独立に cX を産むのか)。重複 build 回避のため必須 RECON。
- 見積 ~350-550 LOC は Explore agent 概算、multi-session だが各ピース bounded・deep math gap 無し
  (R(μ_j)/(5.6) projection core は全部済)。
- **正本=本 cont.³⁷。誤診訂正済: R(μ_j)=certainTypeR 既存、残=cX wiring 3 ピース (A/B/C)、本セッション
  engine 一般化+bound wrapper landed。次=(A) 着手前に CaseBAssembly per-constituent 機構を RECON。**

## cont.³⁸ (2026-06-16 loop): architecture RECON 完了 ((6.8.2) vs (6.8.3)) + `certainTypeMemberDecomposition` landed
cont.³⁷ の RECON 課題 (per-constituent 機構の位置付け) を解決。**(6.8) の二層構造を確定**:
- **(6.8.2)** = X-member 構造: per-constituent 機構 `caseB_hagg`/`caseB_per_phi_anchored`/`caseB_constituentDecomposition`/
  `caseB_phi_family` (= `Ind^L_{W₂}φ` の constituent `Ind^L_H θ` 分解、constituentWeight=⟨φ,Resθ⟩) + 二分
  `caseB_induce_column_or_irreducible` (各 X-member = column or irreducible) + cX。**これは (5.6) engine とは別ピース**
  (constituent 分解 = glue 入力 D / X-coherence 用)。
- **(6.8.3)** = 最終 X∪Y→S 拡張: `false_of_caseB_break_of_bounds` (`S08_CaseBEndgame:384`) =
  **`hbreak: w1·hZ·(cZ−1) ≤ 2w1²d` (nat 算術) + FPF tower ✅ + Cor2.30 → False**。⟹ **私の
  `coherentDegreeSqNormBound_of_not_coherentW` (∑deg²/mc ≤ 2a, 実数) が hbreak を産む経路** (cont.²⁵ #1 = これ)。
  残 = (i) engine を certain-type データで instantiate (Dmem/hortho_mem 要) (ii) **X-sum 恒等式 `∑deg²/mc = w1·hZ·(cZ−1)`**
  (notes 既述 `sum_div_normSq_induce_kernelFilter_eq` で X-sum 済) (iii) `2a ↔ 2w1²d` 接続 → `false_of_caseB_break_of_bounds`。

**✅ 本 loop landed (`08640b33`)**: **`certainTypeMemberDecomposition`** (`S06_CertainTypeCoherence:721`) =
reducible column の **ψ=0 member 分解** (tau1=ν=coherence extension、`certainTypeR` 経由 ofProjection)。
= `memberExtensionDecomposition` の reducible 版 (`certainTypeDecompositionDa` は tau1=τ の Da-style ψ=a·η₁、
これは ν-style ψ=0)。⟹ **weighted engine `xAdjoinStepW`/`coherentDegreeSqNormBound_of_not_coherentW` の `Dmem`
入力が reducible column 用に揃った** (`htau1Dmem`=`(Dmem).tau1=ν` は rfl)。certain-type 決定族完備: Da-style + member-style。

**▶ 次の bounded piece (次 loop)**: **reducible column の cross-family orthogonality `hortho_mem`**
= `(certainTypeMemberDecomposition …).imageFamily.Orthogonal (dadeOrthonormalCharacterImageFamilyOfDiff hyp hconj χ …)`
(= `(certainTypeR h hχ₂ hdeg).Orthogonal (R(break χ))`、ofProjection ゆえ imageFamily=certainTypeR)。
(5.2.e)-style: certainTypeR の σ-image 各々 ⊥ break χ の Dade image 各々。template = `certainTypeRImage` の構造 +
`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`。その後 engine instantiation (Dmem/hortho_mem/mc/χmem=columns)
→ `∑deg²/mc ≤ 2a` → X-sum 恒等式 → `false_of_caseB_break_of_bounds` で (6.8.3)。**正本=本 cont.³⁸。**
**⚠ τ 注意**: `certainTypeMemberDecomposition` は τ=`dadeIntegralCharacterMap h.dade0 h.tau` (certain-type)。
engine は τ=`hyp.fullDadeIsometryData` (S04)。instantiation 時に (B) reconciliation (`certainTypeSet_isCoherent_tau`
の hmapagree/congrMap) 経由で τ を一致させる必要。**正本=本 cont.³⁸。Dmem reducible 版 landed、次=hortho_mem。**

## cont.³⁹ (2026-06-16 loop): (B) reconciliation 既存判明 + Dmem を τ' 一般化 + assembly 重複の整理
**✅ (B) τ-reconciliation は既存 infra で discharge 済** (cont.³⁷ の「~50-100 LOC」は過大評価):
- `SibleyDadeHypothesis.dade0_map_eq_tau_of_support` (`S08_CaseBAssembly:149`) = hmapagree 無条件証明 (τ_ct=hyp.tau on H^#-supported)。
- `certainTypeSet_isCoherent_tau_canonical` (`:170`) = **column 基底 coherence を hyp.tau 上で構築済**。
- `caseB_column_mapagree` (`:194`) = column 共役差 map 一致 `hyp.tau(μ_j−μ̄_j)=τ_ct(μ_j−μ̄_j)`。
- `columnRFamilyTau` (`S08_CaseBCoherence2`) = **R(μ_j) を hyp.tau に transport 済** (= 私の inline transport と同等)。

**✅ 本 loop landed (`08640b33`+`fd821436`)**: `certainTypeMemberDecomposition` を **一般 τ' + hagree** に一般化
(image family を inline transport、`τ'=hyp.tau`/`hagree=caseB_column_mapagree`/`hS₁=certainTypeSet_isCoherent_tau_canonical`
で hyp.tau 上の reducible column ψ=0 Dmem が直接得られる)。

**🔑 architecture 整理 (重複/相補の確定)**: case-B assembly (S08_CaseBAssembly/CaseBCoherence2) は engine path と**相補的**:
- assembly = **材料** = `columnDecompositionTau` (ψ=a·η₁ Da-style, hyp.tau) / `irreducibleDecompositionTau` /
  `columnDecompositionTau_X_orthogonal` (via `inner_coherent_extension_certainTypeOmegaSigma_eq_zero`) /
  per-constituent `caseB_per_phi_anchored*` (6.8.2.3 anchored images)。
- engine = **(5.6) bound 産出** = `coherentDegreeSqNormBound_of_not_coherentW` (assembly に bound 産出器は無い)
  → (6.8.3) `false_of_caseB_break_of_bounds` の hbreak。⟹ **engine は redundant でない**。
- 私の `certainTypeMemberDecomposition` (ψ=0) = assembly に無い member-style 補完 (assembly は ψ=a·η₁ のみ)。
  transport は `columnRFamilyTau` と軽微重複だが **S06 層が S08 を import 不可**ゆえ inline 不可避 (将来 columnRFamilyTau を
  S06 へ移せば共有可、issue 候補)。

**▶ 残 (engine instantiation → (6.8.3))**: (1) **`hortho_mem`** = `certainTypeR ⊥ R(break χ)` (break χ=既約 X-member の
Dade family)。⚠ assembly の `inner_coherent_extension_certainTypeOmegaSigma_eq_zero` は σ-image ⊥ **Y-anchor extension**
で別物 (break χ の Dade family R(χ) との直交は新規の可能性)。(2) X-sum 恒等式 `∑deg²/mc=w1·hZ·(cZ−1)` (`sum_div_normSq_…` で X-sum 済)。
(3) engine を column data で instantiate → hbreak → (6.8.3)。**⚠ 統合は多ファイル横断で大きい**。次 loop=hortho_mem 着手 (tractability 評価)。
**正本=本 cont.³⁹。(B) 既存・Dmem τ' 化 landed・engine⊥assembly 相補確定。次=hortho_mem。**

## cont.⁴⁰ (2026-06-16 loop): hortho_mem (`certainTypeR ⊥ R(break χ)`) の完全 recipe — tractable 確認
hortho_mem tractability 評価完了。**構築可能**(crux fact 成立)、ただし **S08 層・~60-100 LOC・fiddly**。
- **必要形**: `(certainTypeR h χ₂ hdeg).Orthogonal (dadeOrthonormalCharacterImageFamilyOfDiff hyp.dade hyp.hconj χ …)`
  = `∀ α ∈ σ-images, ∀ β ∈ R(break χ), ⟨α,β⟩=0` (xAdjoinStepW の `hortho_mem`、column member Dmem の imageFamily)。
- **既存ツール (全て揃っている)**:
  - **`tau_apply_eq_zero_of_mem_ticVdiffV`** (`S08_CaseBCoherence2:1108`): H^#-supported α ⟹ `(hyp.tau α) v=0` on V。
    ⟹ break χ の `τ(χ−χ̄)` は V 上消える (χ−χ̄ は `hdiffsuppχ` で H^#-supported)。**crux 成立**。
  - **`inner_smul_chiFam_eq_zero_of_diff_vanishOnV`** (`:1181`): orthonormal ξ,ξ'∈±Irr で `c·ξ−c'·ξ'` が V 上消える
    ⟹ `⟨c·ξ, ω^σ⟩=0` (ω^σ=chiFam)。
  - **`certainTypeOmegaSigma_eq_chiFam`** (σ-image=chiFam 書換)、**`inner_coherent_extension_certainTypeOmegaSigma_eq_zero`**
    (`:1246`、ミラー対象 — ν-extension 版だが技法同一)。
- **構築**: R(χ)={ε·μ, −ε·ν} (`dadeOrthonormalCharacterImageFamilyOfDiff`→`toOrthonormalImage`)、`τ(χ−χ̄)=∑R(χ)=ε·μ−ε·ν`
  が V 上消える → `inner_smul_chiFam_eq_zero_of_diff_vanishOnV` で各 R(χ) 元 ⊥ ω^σ (2 元それぞれ partner を入替え)。
  共役対称で `⟨ω^σ, R(χ)元⟩=0` に flip。σ-image 側は ±certainTypeOmegaSigma の sign 処理。
- **build 層**: V-vanishing tools は S08_CaseBCoherence2 (S06 下流) ゆえ **hortho_mem は S08 層** (新 leaf or CaseBCoherence2 末尾、
  ただし 2164 行ゆえ新 leaf 推奨 `S08_CaseBHortho`)。`inner_coherent_extension_certainTypeOmegaSigma_eq_zero` を template に。

**📍 case-B (6.8.3) 残ロードマップ (収束、各ピース bounded)**: ✅ engine 一般化 / ✅ Dmem τ'化 / ✅ (B)既存 /
🔨 hortho_mem [recipe 完備、S08 層 ~60-100 LOC、次] → ⬜ X-sum 恒等式接続 → ⬜ engine instantiate (`coherentDegreeSqNormBound_of_not_coherentW`
を certain-type S₁/columns/Dmem/hortho_mem で) → hbreak → ⬜ `false_of_caseB_break_of_bounds` で (6.8.3) → cX wiring → glue → sole sorry。
multi-session focused だが deep math gap 無し・全ツール在庫。**正本=本 cont.⁴⁰。hortho_mem recipe 完備、次=S08 層で構築。**

## cont.⁴¹ (2026-06-16 loop): ✅✅ hortho_mem 完成 (`certainTypeR_imageSet_orthogonal_dadeOfDiff`)
**新 leaf `S08_CaseBHortho.lean` (163 行、`286f35d5`、build-green+axiom-clean+0 sorryAx)** に hortho_mem を構築
(recipe 通り、subagent 実装→自己検証)。`certainTypeR_imageSet_orthogonal_dadeOfDiff`:
`∀ α ∈ (certainTypeR h46 hχ₂ hdeg).imageSet, ∀ β ∈ (dadeOrthonormalCharacterImageFamilyOfDiff hyp.dade hyp.hconj χ …).imageSet, ⟨α,β⟩=0`
= R(μ_j) ⊥ R(break χ) の imageSet 形 (= `.Orthogonal`、transported certainTypeR の imageSet=certainTypeR.imageSet ゆえ直結)。
V-vanishing 技法 (each σ-image=scalar·chiFam、break diff `(χ−χ̄)^τ` が V 上消える `tau_apply_eq_zero_of_mem_ticVdiffV` +
`inner_smul_chiFam_eq_zero_of_diff_vanishOnV`、4 case + conj 対称)。⚠ 知見: toOrthonormalImage は ℤ-smul、key は ℂ-smul →
`Int.cast_smul_eq_zsmul` で橋渡し。

**📍 case-B (6.8.3) ロードマップ**: ✅engine一般化 ✅Dmem τ'化 ✅(B)既存 ✅**hortho_mem** →
⬜ **engine instantiation** [次・最後の山]: `coherentDegreeSqNormBound_of_not_coherentW` を certain-type データで instantiate
— S₁=certainTypeSet (coherent via `certainTypeSet_isCoherent_tau_canonical`)、χmem=columns、Dmem=`certainTypeMemberDecomposition`
(τ'=hyp.tau、hagree=`caseB_column_mapagree`)、hortho_mem=今回の lemma、mc=column норм、break χ=既約 X-member、deg data →
`∑deg²/mc ≤ 2a` → ⬜ X-sum 恒等式 `∑deg²/mc = w1·hZ·(cZ−1)` (`sum_div_normSq_…` で X-sum 済、要接続) +
`2a↔2w1²d` → `false_of_caseB_break_of_bounds` で **(6.8.3)** → cX wiring → glue → sole sorry。
全ツール在庫、deep math gap 無し。**正本=本 cont.⁴¹。hortho_mem landed、次=engine instantiation (最後の山)。**

## cont.⁴² (2026-06-16 loop): ✅ xChainCoherentW (weighted X-chain fold shell)
**`xChainCoherentW`** (`S08_CoherenceWeighted` 末尾、`cd5409f1`、build-green+axiom-clean) = `xChainCoherent` の
weighted verbatim analogue (`coherentOfPairChainCover` + `XAdjoinStepInputW.adjoin`、struct 差し替えのみ)。
base S₀ (case-B = certainTypeSet via `certainTypeSet_isCoherent_tau_canonical`) に既約 X-member pair を fold → X-coherence。
fold shell は per-step `hstep : XAdjoinStepInputW` を**パラメータ**に取る (xChainCoherent と同型)。

**📍 case-B (6.8.3) ロードマップ (構造ピース全完了、残は per-step 組立)**:
✅engine一般化 ✅Dmem τ'化 ✅(B)既存 ✅hortho_mem ✅**xChainCoherentW fold** →
⬜ **per-step `hstep` 構築 = 真の hard core** [次・最重 ~200-400 LOC]: 各 adjoin step で full `XAdjoinStepInputW` を
heterogeneous member family (accumulator = columns + 既 adjoin 済 irreducibles) から組む。要: (a) X の degree-monotone
enumeration (pair/χs/cover) (b) 各 member を column/irreducible に分類し Dmem (column=`certainTypeMemberDecomposition`、
irr=`memberExtensionDecomposition`)・hortho_mem (column=今回の lemma、irr=`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`)
を供給 (c) mc=norms (column ‖·‖²>1, irr=1) (d) deg data (e) hSgen/hgen/break facts。これが case-A
`Xset_commutator_isCoherent_…_of_frobenius` の hstepData に相当する case-B monolith。
→ cX → glue (`coherentXunionYset_caseB_of_glued`) → X∪Y coherence + (6.8.3) `false_of_caseB_break_of_bounds` (S₁=X∪Y、
hbreak=X-sum 経由) → S coherent → sole sorry の case-B 枝。**+ case-A 枝 + dispatch も sole sorry に要**。

**🔭 honest 見立て**: 構造・基盤ピースは全完了 (engine/Dmem/(B)/hortho_mem/fold)。残 = per-step monolith builder
(~200-400 LOC、heterogeneous 組立、deep math gap 無しだが大きい) + (6.8.3) wiring + case-A。**large focused assembly**
(60s loop の小刻みより腰を据えた multi-session 向き、但し全ツール在庫で unblocked)。**正本=本 cont.⁴²。fold shell landed、
次=per-step hstep monolith (subagent 候補) または (6.8.3) break wiring を先に。**

## cont.⁴³ (2026-06-16 loop): cX assembly の完全 RECON — enumeration ツール確定 + 残務 milestone 確定
cX (= `IsCoherent hyp.tau (Xset W2)`) の全構成要素を確定。**基盤・構造ピースは全完了**、残 = **cX assembly 本体 (large focused)**:

**X-enumeration ツール = `exists_conjugatePairCover_general`** (`S08CP1:816`、`exists_conjugatePairCover` (:673) と違い
`hXirr` 不要)。pairs は非-S₀ member から構成 ⟹ **S₀=certainTypeSet (columns) なら pairs=非-column=既約 X-members**
(`caseB_S_member_column_or_irreducible` :1949 で保証)。⟹ X = Xset W2、S₀ = certainTypeSet で適用 → conjugate-pair cover。
⚠ **要件 4 性質が未証明** (grep 確認、case-B cX 未着手の証左): `Xset W2` の Finite / `ClosedUnderConjugate` /
`HasNoRealCharacters`、`certainTypeSet` の `ClosedUnderConjugate`。これらの証明 (~50-100 LOC) が enumeration の前段。

**🔭 残 cX assembly = 1 個の大きな def** (xChainCoherentW を核に、~300-550 LOC):
1. **Xset/certainTypeSet 構造性質** (finite/conj/no-real、~50-100 LOC) — 未証明、enumeration 前提。
2. **X-enumeration** (`exists_conjugatePairCover_general` → pair/N/χs、非-column=既約で χs 抽出、~50 LOC)。
3. **hstep monolith** (per-step `XAdjoinStepInputW`、heterogeneous member: column→`certainTypeMemberDecomposition`+
   今回 hortho lemma、irr→`memberExtensionDecomposition`+`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`、
   mc/deg/hSgen/hgen/break facts、~200-400 LOC、case-A hstepData 相当の最難核)。
4. **wiring** (`xChainCoherentW` enumeration+base+hstep → cX、bounded)。
その後: cX → glue (`coherentXunionYset_caseB_of_glued`) + (6.8.3) `false_of_caseB_break_of_bounds` (S₁=X∪Y、
X-sum→hbreak) → S coherent → sole sorry case-B 枝。**+ case-A 枝 (cX 既存 `Xset_commutator_…_of_frobenius`、wiring) + dispatch**。

**📊 milestone**: 本セッション 8 Lean commit で **case-B (6.8.3) の基盤・構造ピース全完了**
(engine 一般化 / Dmem τ'化 / (B) reconciliation / hortho_mem / xChainCoherentW fold)。残 = cX assembly 本体
(~300-550 LOC、enumeration 前提性質 + hstep monolith + wiring) + (6.8.3)/glue/case-A wiring。**deep math gap は無い**
(全ツール在庫) が **large focused assembly** — 60s loop 小刻みより dedicated 多セッション or Workflow 向き。
**正本=本 cont.⁴³。enumeration=`exists_conjugatePairCover_general`、残=cX assembly 本体 (構造性質→hstep monolith→wiring)。**

## cont.⁴⁴ (2026-06-16 loop): ✅ X-enumeration landed + 🔬 degree-class 構造的発見
**新 leaf `S08_CaseBEnumeration.lean` (`93f3b670`、199 行、3 decl 全 axiom-clean)**:
- ✅✅ **`Xset_hasNoRealCharacters_caseB`** + **`certainTypeSet_closedUnderConjugate`** = **unconditional 再利用 helper** 2 本。
- **`caseB_Xset_conjugatePairCover`** = X = Xset W2、S₀ = certainTypeSet h46 k の conjugate-pair cover
  (`exists_conjugatePairCover_general` 経由、非-S₀ pairs から既約 χs 抽出、xChainCoherentW の hpair0/1/pairs/cover を産む)。

**🔬🔬 重要な構造的発見** (subagent が `hnonS₀_irr` 仮説を要したことで露呈): **`certainTypeSet h46 k` は単一 degree
class k に制限** (def に degree-match 条件 `∑μ_ij(1)=∑μ_ik(1)`)。⟹ 他 degree class の column は **reducible だが
certainTypeSet h46 k に非含** → 非-S₀ X-member が既約とは限らない。`caseB_Xset_conjugatePairCover` は
**2 honest 仮説**を持つ (workaround でない真の obligation): (1) `hbase`: certainTypeSet ⊆ Xset (column∈S(W2)、deferred)
(2) `hnonS₀_irr`: 非-certainTypeSet X-member は既約。

**⟹ cX base の構造的論点 (hstep 前に要解決)**: cX = IsCoherent (Xset W2) は**全 degree class の column** を要する
(X-sum は全 X over θ:W2⊄ker)。だが column 基底 coherence `certainTypeSet_isCoherent_tau_canonical` は**単一 k**。
要確認 = (A) certain-type 構造で全 column が同一 degree か (なら certainTypeSet h46 k=全 column、hnonS₀_irr 自動) /
(B) 全 class union ∪_k certainTypeSet h46 k が base か (なら union coherence 要) / (C) (6.8.3) が per-class か。
**この degree-class 構造の解明が cX assembly の次の鍵** (hstep monolith より先に要)。

**📊 進捗 (本セッション 10 Lean commit)**: 基盤・構造 (engine/Dmem/(B)/hortho_mem/fold) + enumeration helper +
cover (conditional)。残 = (i) **degree-class 構造解明** [次、cX base 設計] (ii) hstep monolith (iii) wiring → cX →
(6.8.3)/glue/case-A。⚠ subagent 委譲は ~155k tok/piece と高コスト、hstep は深く大きい。**正本=本 cont.⁴⁴。
enumeration landed (2 unconditional helper)、次=degree-class 構造解明 (cX base が単一 k か全 class union か)。**

## cont.⁴⁵ (2026-06-16 loop): 🔑 原典 (6.8) 精読 — `xChainCoherentW` アプローチが正しいと確認
`references/peterfalvi/04.8_…Some_Coherence_Theorems.mmd` の (6.6)/(6.8.1)/(6.8.2)/(6.8.3) を精読:
- **(6.8.3)** (S coherent): S₁ (X∪Y⊂S₁⊂S) coherent + S₂={ψ,ψ̄}⊂S not-coherent に **Thm (5.6)** →
  `2ψ(1)η₁(1) ≥ ∑_{S₁}χ(1)²/‖χ‖² > ∑_X = |W₁||H:Z|(|Z|−1)`、Cor 2.30 `d²≤|H:Z|`、case B `|H:Z|≥(2|W₁|+1)²`
  → 矛盾。**= 私の `false_of_caseB_break_of_bounds` と完全一致** (S₁=X∪Y、X-sum、FPF tower)。
- **(6.6)**: X⊂Irr L ⟹ X coherent via **「repeated use of Theorem (5.6)」= chain adjoin** (= 私の xChainCoherent 系)。
- **case (A)** [Z=Z(H)∩H']: (6.8.1) — (c1)(c2) 両方で「S と S(Z) が各 w₂−1 reducible」⟹ reducibles∈S(Z) ⟹
  **X=S−S(Z)⊂Irr L (全既約)** → (6.6) chain adjoin。X∪Y glue = τ₂ (τ on supported + η₁↦Y、(4.1) 直交 + 6.8.2.3 anchored)。
- **case (B)** [Z=W₂]: reducible columns ∈ X ⟹ **X非全既約**。⟹ cX = **certain-type 𝒯 coherence (4.9) を base に
  既約 X-member を (5.6) で adjoin** = **私の `xChainCoherentW` (reducible base + 既約 adjoin) がまさにこの構造**。

**⟹✅ アプローチ確認**: xChainCoherentW (reducible 𝒯 base + 既約 (5.6) adjoin) = 教科書 case-B cX の正しい構造。
hstep = per-step (5.6) data (column member は 𝒯-base 内ゆえ Dmem=`certainTypeMemberDecomposition`/hortho=今回 lemma、
adjoin 済既約は memberExtension)。X∪Y glue は別 (τ₂ 直接=`coherentXunionYset_caseB_of_glued`、case-B assembly 既存)。

**🔬 残 degree-class 詳細**: 𝒯=certainTypeSet h k=単一 degree class。case-B の reducible columns が全て同一 degree なら
𝒯=全 column (cX base 単純)、複数 degree なら base=∪_k 𝒯 (union coherence 要)。**要 (4.9) 原典確認** (column μ_j=Ind χ_j、
χ_j(1) が j で変動するか)。これが解ければ cX base 確定 → hstep monolith。

**📊 milestone (本セッション 11 Lean commit + textbook 確認)**: 基盤・構造・enumeration 全完了、**アプローチ正当性を原典で確認**。
残 = (i) degree-class 詳細 [(4.9) 原典、bounded] (ii) **hstep monolith** [最難核、~200-400 LOC] (iii) cX wiring →
(6.8.3)/glue/case-A。deep だが**経路は確定**。**正本=本 cont.⁴⁵。xChainCoherentW=正しい case-B cX 経路 (原典確認)、
次=(4.9) で degree-class 確認 → hstep monolith。**

## cont.⁴⁶ (2026-06-16 loop): ⚠⚠ 訂正 (cont.⁴⁵ course-correction) — (6.8.2) は τ₂ 直接、chain adjoin でない
**(6.8.2)「X∪Y is coherent in case (B)」の証明全体を精読** (`04.8.mmd` L178-224)。cont.⁴⁵ の「case-B cX = chain
adjoin (xChainCoherentW)」は **誤り**:
- **(6.8.2) は τ₂ を直接構成**: `τ₂ : Z[X∪Y]→Z[Irr G]`、`τ on Z[X∪Y,L^#]` 一致 + `η₁^{τ₂}=Y` (Y は (6.8.2.2) で固定)。
  per-χ の **(6.8.2.3)** `(χ−aη₁)^τ = X₁−aY` (R(χᵢ) families + (5.4.a/b) `‖Xᵢ‖²≥‖χᵢ‖²` 分解、bᵢ=aᵢ forcing) で
  τ₂ が内積保存 → X∪Y coherent。**chain adjoin (repeated (5.6)) は使わない** (case (A) の (6.6) のみ chain)。
- ⟹ **`xChainCoherentW` (`cd5409f1`) + `caseB_Xset_conjugatePairCover` (`93f3b670`) は case-B では DETOUR**
  (chain-adjoin cX を想定したが、教科書 case-B は τ₂ 直接)。両 lemma は valid だが case-B 経路上にない。
  case-B assembly の **`columnDecompositionTau`/`caseB_per_phi_anchored`/`caseB_constituentDecomposition`/glue
  `coherentXunionYset_caseB_of_glued` がまさに (6.8.2) τ₂ 経路**を実装中。

**✅ on-path (検証済)**: (6.8.3) break は **S₁=X∪Y に単一 break {ψ,ψ̄} を Thm (5.6)** で適用 →
`2ψ(1)η₁(1) ≥ ∑_{S₁} > ∑_X`。⟹ 私の **`coherentDegreeSqNormBound_of_not_coherentW` (= (5.6) bound) + Dmem
(`certainTypeMemberDecomposition`) + hortho_mem (`certainTypeR_imageSet_orthogonal_dadeOfDiff`) は (6.8.3) の
S₁ member family に on-path** (S₁ の column members 用)。単一 break ゆえ chain (xChainCoherentW) 不要。

**🧭 正しい case-B 経路 (再確定)**:
- **(6.8.2)** X∪Y coherence = **τ₂ 直接** (case-B assembly: columnDecompositionTau + caseB_per_phi_anchored の
  6.8.2.3 anchored images + glue)。**← my xChainCoherentW でない。case-B assembly の進捗を assess 要**。
- **(6.8.3)** S coherence = (5.6) 単一 break (my bound + Dmem + hortho_mem) + X-sum + FPF (`false_of_caseB_break_of_bounds`)。

**📊 honest reckoning**: 本セッション 11 Lean commit のうち **2 本 (xChainCoherentW + enumeration) は case-B detour**
(教科書 misread)。on-path = (5.6) engine/bound + Dmem + hortho_mem + FPF tower。残 = (6.8.2) τ₂ (case-B assembly、
進捗未 assess) + (6.8.3) 単一 break wiring。**正本=本 cont.⁴⁶ (cont.⁴⁵ 訂正)。次=case-B assembly の (6.8.2) τ₂
進捗を assess (columnDecompositionTau/caseB_per_phi_anchored がどこまで X∪Y coherence を産むか) → (6.8.3) wiring。**

## cont.⁴⁷ (2026-06-16 loop): cX 構築 infra 特定 + セッション consolidation
case-B assembly assess: **cX (`IsCoherent (Xset)`) を産む定理は無い** (glue `coherentXunionYset_caseB_of_glued` は cX を入力)。
per-χ (6.8.2.3) ingredients は揃う: `columnDecompositionTau`/`irreducibleDecompositionTau` (`S08_CaseBCoherence2`、
caseB_constituentDecomposition `:1104/1112` が消費) + `per_constituent_Y_eq_smul` (`:871`、(6.8.2.3) τ₂-Y pinning) +
X-orthogonalities (`columnDecompositionTau_X_orthogonal` 等)。
**cX 構築 infra (S07)**: `retarget_isCoherent_of_decompositions*` (`:3911-4126`) / `coherentImageMapGlue` (`:3092`) /
`exists_integralCharacterMap_glue_of_orthonormal` (`:3125`) = per-χ images から IsCoherent 構築。
**⟹ 残 cX = これら infra に per-χ (6.8.2.3) decompositions を投入し `IsCoherent (Xset)` を τ₂|_X 構築** (intricate、
case-B assembly/S07 領域、未着手)。

### 📊 セッション総括 (2026-06-16 lane-b、~18 loop iterations)
**landed (11 Lean commit、全 build-green+axiom-clean)**:
- ✅ on-path: `xAdjoinStepW` 一般化 + `.adjoin` + struct + **`coherentDegreeSqNormBound_of_not_coherentW`** ((5.6) bound) /
  `certainTypeMemberDecomposition` (ψ=0 Dmem、τ' 一般化) / **`certainTypeR_imageSet_orthogonal_dadeOfDiff`** (hortho_mem) /
  unconditional helper `Xset_hasNoRealCharacters_caseB`/`certainTypeSet_closedUnderConjugate`。← (6.8.3) 単一 break 用。
- ⚠ detour (valid だが case-B 経路外): `xChainCoherentW` (`cd5409f1`) / `caseB_Xset_conjugatePairCover` (`93f3b670`)。
**確定事項**: cont.³⁶ 誤診訂正 (R(μ_j)=certainTypeR 既存) / (B) reconciliation 既存 / **原典 (6.8) 構造確定**
((6.8.2)=τ₂ 直接 not chain、(6.8.3)=単一 (5.6) break)。
**残務 (正確)**: (a) **cX via per-χ (6.8.2.3) τ₂|_X 構築** [上記 infra、未着手、large] (b) glue → X∪Y (c) (6.8.3) 単一
break wiring [my (5.6) bound + X-sum + FPF] (d) sole sorry (case-A+B+dispatch)。**deep math gap 無し・全 ingredients/infra
在庫だが large focused assembly** (multi-session or Workflow 向き)。**正本=本 cont.⁴⁷。次セッション: cX via per-χ τ₂|_X
を `retarget_isCoherent_of_decompositions*` + columnDecompositionTau で構築 (xChainCoherentW は使わない)。**
