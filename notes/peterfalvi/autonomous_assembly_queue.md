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
- 🔜 **T-A3 着手中** (route A invasive): IsCoherent に `extension_mem_ZIrr` field 追加で xAdjoinStep の
  hmemνZ 仮説を導出可能化. 1 site ずつ full build 確認, base ZIrr 証明 hard なら revert+blocked 記録.

## Blocked ログ (revert した task と欠落 primitive を追記)
(なし)
