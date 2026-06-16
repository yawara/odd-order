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
