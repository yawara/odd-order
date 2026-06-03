# Peterfalvi (6.8) X-family coherence — 自走 assembly queue

**正本** (context 圧縮されても自走ターンはこのファイルを読んで従う). 2026-06-04 設定.
状況: crux1 hard core 完了 (notes/peterfalvi/s08_6_8_assembly_plan.md §J.3.5). 残 = 最終 assembly (§J.3.6).

## 不変則 (毎ターン厳守)

1. **build-green を transcript に報告してから commit**: `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems`
   が緑 (`Build completed successfully`) を Bash 出力で確認・報告。
2. **axiom-clean 確認**: 新 lemma を `#print axioms <名>` で確認、`[propext, Classical.choice, Quot.sound]`
   のみなら OK (sorryAx が出たら **revert**)。一時ファイル `OddOrder/AxCheckTmp.lean` で確認し削除。
3. **anti-scaffold gate** ([[scaffold-sorry-free-not-done]]): 新 `sorry`/`axiom`/過強仮定で hard 部分を
   逃がす偽進捗を**禁止**。honest に証明できないなら `git checkout -- . && git clean -fd` で**完全 revert**
   し、本ファイル下部「blocked ログ」に「欠落 primitive / 理由」を記録して次 task へ。
4. **commit 単位**: 完成した lemma 1 つ (+ その helper) ごとに build-green+axiom-clean で commit
   (descriptive message + `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`)。
5. **worktree のみ・main 不可侵**: commit 前に `git branch --show-current` =
   `claude/determined-hypatia-e67fd5` を確認。main への操作一切不可。
6. **逐次** (impl は 1 本ずつ; parallel build 不可)。詰まったら revert→次 task、全 task blocked で停止。

## 既存 landed lemma (S08, 全 axiom-clean — 再実装不要, 呼ぶだけ)

- `inner_dade_extension_of_supported` — `⟨τ u, ν δ⟩=⟨u,δ⟩` (supported u, δ∈ℤ[S₁]∩CF(L,A))
- `crux1_of_collapse` — himg+collapse+R直交+‖νχ₁‖²=1 ⟹ crux1
- `memberExtensionDecomposition` — member χ の ψ=0 分解 (tau1=ν), `ν χ∈ZIrr` 注入
- `inner_dadeDiff_conjDifference_eq_zero` / `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal` — 差分 family ⊥
- `inner_decomposition_X_extension_member_eq_zero` / `inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero` — `⟨Da.X, νχ₁⟩=0`
- `inner_Y_extension_member_eq` — `⟨Da.Y,νχⱼ⟩ = a·⟨χ₁,χⱼ⟩ − (a+μ)·aⱼ`  (μ=⟨τ(χ−a·χ₁),νχ₁⟩)
- `exists_indexed_intProjection_of_orthonormal_ZIrr` — indexed 直交射影 (φ,family∈ZIrr → 整数係数)
- **`crux1_of_memberFamily`** — member family + degree 不等式 ⟹ **crux1 `⟨τ(χ−a·χ₁),νχ₁⟩=−a`**
- `retarget_isCoherent_of_extensionImage` (bridge) — crux1+crux2+hSgen ⟹ `IsCoherent τ (S₁∪{χ,χ̄}) A`
- `retarget_mem_ZIrr` — retarget は ZIrr 保存 (route A の retarget site)

S07: `peterfalvi_66_coherence_of_X` (abstract chain fold, hstep を取る) / `decompositionDaFromDadeOfDiff`
(Da 構成) / `lambda_eq_zero_and_Z_eq_zero` / `coherentEqualDegree_fromDade` (base) / `two_mul_lt_sq_of_primePow_gap`
(6.6 degree gap).

## Task (安全順: additive 先 → invasive 後; 順に実装, blocked なら次へ)

### T-A1. per-step adjoin lemma `xAdjoinStep` [additive, 安全, 最優先]
`IsCoherent τ S₁ A` + 新非実既約 χ (χ̄ あり) + S₁ の member family
(`s:Finset ι`, `χmem:ι→CF`, `deg:ι→ℕ`, `i₁`, orthonormal `⟨χmem i,χmem j⟩=δ`,
`χmem i∈S₁`, `νχmem i∈ZIrr` 注入, degree 不等式 `2a<∑aᵢ²`, `deg i₁=1`)
+ Da (`decompositionDaFromDadeOfDiff`) + `Da.Y∈ZIrr` ⟹ `IsCoherent τ (S₁∪{χ,χ̄}) A`.
**構成**: 各 member に `inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero`(R直交)
+ `inner_dade_extension_of_supported`(hfound, δ=χmem i−aᵢ·χ₁ supported) → `inner_Y_extension_member_eq`
(hcoeffval) → `crux1_of_memberFamily`(crux1) → bridge `retarget_isCoherent_of_extensionImage`
(crux2 clean: `inner_dadeDiff_conjDifference_eq_zero` 系; hSgen clean: 整数次数比).
仮説に member family + ZIrr を取る (struct 強化はまだしない). build-green additive.

### T-A2. chain fold `xChainCoherent` [additive]
T-A1 を `peterfalvi_66_coherence_of_X` の `hstep` に供給し base block から共役 pair cover で fold
⟹ `IsCoherent τ X A`. per-step の member family/ZIrr/degree data は running accumulator
`pairUnion S₀ pair i` から供給 (= 各 step で member family を再構成; T8 `exists_conjugatePairCover`
の enum を使う). **注意**: member family enum を running accumulator から組むのが intricate.
blocked なら ZIrr/member family を ∀-仮説に取った中間版で commit し、enum 接続を T-A4 に回す.

### T-A3. route A: `IsCoherent` を ZIrr-codomain で強化 [invasive — 慎重に, 壊れたら revert]
field `extension_mem_ZIrr : ∀ φ∈ZIrr L, extension φ∈ZIrr G` 追加。discharge:
- `retarget_isCoherent` (S07:2916): `retarget_mem_ZIrr` 適用 (X,Xbar∈ZIrr 新仮説 + χ,χ̄∈ZIrr L 追加要)。
- `coherentEqualDegree`(3078)/`coherentEqualDegree_fromDade`(5109): base 構成の ν∈ZIrr (要証明).
- `galoisTransport`(1462): galois は ZIrr 保存。
- bridge/DadeChainStep に X,Xbar∈ZIrr 伝播。
**1 site ずつ**、各 site 後に full `lake build OddOrder` 緑を確認。base site の ZIrr 証明が hard で
blocked なら **field 追加ごと revert** し「base ZIrr 証明が要 primitive X」を blocked ログに記録、T-A3 skip。

### T-A4. T8 enum 接続 [hard, T8 backbone 依存]
`xChainCoherent` を `Xset Z`/`xBaseBlock`(=`xBaseBlock_isCoherent`)/`exists_conjugatePairCover` +
(6.6) degree gap (`two_mul_lt_sq_of_primePow_gap`) で特殊化 ⟹ `IsCoherent τ (Xset Z) A`.

### T-A5. glue + capstone [最終]
X∪Y glue → `sibleySetup_is_coherent` (S08 唯一の sorry) を埋める.

## 完了条件
`IsCoherent τ (Xset Z) A` が build-green+axiom-clean で commit 済 (= T-A4 達成), または T-A1..A5 が
全て「完了 commit」か「blocked 記録」のいずれか。

## 進捗ログ (2026-06-04 自走セッション)
- ✅ **T-A1 完了** (commit c0c2e43, build-green 3320 + axiom-clean): `xAdjoinStep` (S08, noncomputable
  def — IsCoherent は Type 値). member family + ZIrr injection を仮説に取り `crux1_of_memberFamily`
  (crux1) + crux2 (R(χ)⊥R(χ₁) clean) + bridge `retarget_isCoherent_of_extensionImage` で
  `IsCoherent τ (S₁∪{χ,χ̄}) A`. `Da.Y∈ZIrr`/`hχaχ1`/`hχbaraχ1` は内部導出. **Lean 罠**: `let Da`/`let Dmem`
  (set/have は opaque 化で defeq 壊す; let は isDefEq が semireducible def を unfold) + `open scoped
  Classical in` (hmemortho の `if i=j`).
- ✅ **T-A2 完了** (commit afb4819, build-green 3320 + axiom-clean): `XAdjoinStepInput` (per-step premise
  bundle, ι:Type field) + `XAdjoinStepInput.adjoin` (→xAdjoinStep) + `xChainCoherent` (coherentOfPairChainCover
  fold; hstep を accumulator coherence hcoh の関数として取る route-B custom fold). **中間版** (member
  family + ZIrr ∀-仮説; IsCoherent 未強化). enum 接続 (exists_conjugatePairCover→hstep 構成) は T-A4.
- 🔶 **T-A3/T-A4/T-A5 = blocked (ZIrr-codomain closure, multi-session; 下記ログ参照)**。T-A1/T-A2 で
  per-step adjoin + fold skeleton は完成したが、最終 closure は §J.3.6 が予告した「route A / route B / checkpoint
  の戦略判断」に帰着。S07 untouched (revert 不要), green な T-A1/T-A2 は保持。

## Blocked ログ (revert した task と欠落 primitive を追記)

### T-A3 (route A: IsCoherent に extension_mem_ZIrr field 追加) — blocked: 大規模 invasive cascade
**欠落 primitive**: なし (数学的には全 site 証明可能)。**blocker = 機械的 cascade 規模が予算超過 + all-or-nothing**。
- IsCoherent に field 追加すると **全 constructor site が新 field を強制** (sorry 不可ゆえ partial 不能):
  S07 の `galoisTransport`(1472)/`retarget_isCoherent`(2916)/`coherentEqualDegree`(3098)/`coherentEqualDegree_fromDade`(5109)/`coherentUnion_of_glued`(~3744) = 5-6 site。
- 加えて `retarget_isCoherent` は ZIrr field を出すのに **X,Xbar∈ZIrr G + χ,chibar∈ZIrr L の新仮説が必要**
  (retarget τ₁ χ χ̄ X Xbar の ZIrr 保存 = `retarget_mem_ZIrr`@S08:1010, ただし S07 に移送要)。この **signature 変更が
  全 caller に cascade** — S07:3159/3503 + **S08 の `retarget_isCoherent_of_extensionImage` bridge (= T-A1 が依存)**。
- **feasibility 確認済 (各 site は証明可能)**: base `coherentEqualDegree` の ν=`coherentImageMap χ X`,
  `coherentImageMap χ X φ = ∑ⱼ⟨φ,χⱼ⟩•Xⱼ` (S07:2737) ⟹ χⱼ∈ZIrr L (irreducible) + Xⱼ∈ZIrr G なら
  `⟨φ,χⱼ⟩∈ℤ`(inner_mem_ZIrr_int)•ZIrr ⟹ ∈ZIrr (≤20行)。galois も ZIrr 保存。retarget は retarget_mem_ZIrr。
- **判断**: 各 site は tractable だが coordinated multi-site refactor (5-6 constructor + 3 caller cascade,
  各 full `lake build OddOrder` 検証) は本セッション予算 (~8 turn) 超過、かつ **green な T-A1 bridge を壊すリスク**。
  **route B (T-A2 の xChainCoherent companion thread) が ZIrr を仮説で運ぶ代替を既に提供**ゆえ route A は optional。
  → 専用セッションで実施推奨 (multi-site script + 各 site 後 full build)。

### T-A4 (enum 接続: xChainCoherent を Xset Z に特殊化) — blocked: ZIrr companion 維持
**欠落 primitive**: per-step の `hmemνZ` (= accumulator member の ν∈ZIrr) を供給する **companion 維持機構**。
- xChainCoherent の hstep は `hcoh : IsCoherent (pairUnion S₀ pair i)` を受けるが、`hcoh.extension` が
  members 上 ZIrr 保存する事実 (`∀x∈acc_i, hcoh.extension x∈ZIrr`) は **IsCoherent に無い** (= §J.3.6 構造的発見1)。
- これを供給するには (a) route A (T-A3, IsCoherent 強化) か、(b) **fold を companion 付きに強化**:
  `Σ'(hcoh)(∀x∈acc_i, hcoh.extension x∈ZIrr)` を `Nat.rec` で thread (~50行 custom fold)、各 step で次 companion を
  `retarget_mem_ZIrr` で維持。だが (b) は **xAdjoinStep の出力 extension が `retarget hS₁.extension χ χ̄ X Xbar`
  であることの露出が必要** — 現状 `retarget_isCoherent` の出力 extension τ₂ は named lemma 未露出 (inline `refine ⟨?_,τ₂,…⟩`)、
  bridge の内部 X=τ(χ-a·χ₁)+a·νχ₁ も未露出。**露出補題群 (retarget_isCoherent_extension_eq + bridge extension_eq + X,Xbar∈ZIrr)
  が要新規** (~80-120行)。
- 加えて enum 構成本体: pairUnion accumulator から member family (χmem/deg/i₁/orthonormality/supports) の再構成、
  hSgen/hgen、degree 不等式 (6.6 gap `two_mul_lt_sq_of_primePow_gap`) の per-step 供給 = T8 backbone
  (`exists_conjugatePairCover`@S08, `xBaseBlock`) との接続。intricate (§J.2/J.3.6)。
- **判断**: ZIrr companion (露出補題 + custom fold) + enum 構成は合わせて multi-session。route A が入れば companion は
  自動化され enum 構成のみ残る ⟹ **route A 先行を推奨**。

### T-A5 (X∪Y glue + capstone sibleySetup_is_coherent) — blocked: T-A4 依存
- `coherentUnion_of_glued`(S07:3744) で X-coherence (T-A4) ∪ Y-coherence (T6 完了済 `coherentYFamily`) を glue。
- T-A4 未完ゆえ blocked。加えて (6.5) p-群還元 (M1, §G) / X∪Y=S (6.8.3) / m≥2 (B4) など §G STRATEGIC 項目も capstone
  には必要 (これらは T-A4 とは独立の別 blocker)。
- **判断**: T-A4 完了後に着手。capstone は本 queue scope 外の依存 (6.5 還元等) も持つ。
