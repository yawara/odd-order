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
- ✅✅ **T-A3 (route A) 完了** (commit a054bc8 + payoff be9cd14, full build 3562 + AxiomsCheck + axiom-clean):
  **§J.3.6 ZIrr-codomain blocker 完全解決**。`IsCoherent` に **`extension_mem_ZIrr : ∀φ∈zSpan S,
  extension φ∈ZIrr G`** field 追加 (= ℤ[S] 上の ZIrr-codomain; **global ∀φ∈ZIrr L は coherentPair で偽**
  ゆえ ℤ[S] が正しい)。全 6 constructor を uniform span_induction で discharge (各 generator が virtual char
  に行く)。新仮説は X,Xbar∈ZIrr のみ (χ,χ̄∈ZIrr/Dade-global 不要)。cascade = retarget_isCoherent の X,Xbar∈ZIrr
  を caller に thread (RetargetTargetPair.{X,conjImage}_mem_ZIrr / Da.imageFamily / classFunction_irreducible
  / bridge hτaχ1Z+hτdiffZ)。**payoff**: xAdjoinStep/XAdjoinStepInput から `hmemνZ` 削除 → field 導出
  (`hS₁.extension_mem_ZIrr (χmem i) (subset_span hmemS1)`)。⟹ chain fold が ν χⱼ∈ZIrr を無料で得る。
- 🟢 **T-A4 = ZIrr unblocked, 残 2 ピース** (commit d0d13af で enum-compat prep: xChainCoherent hpair0/hpair1 を
  ∀i<N に弱化 ⟹ exists_conjugatePairCover の partial hpairχ と直接互換; hcover は caller が hcoverIdx+hsurj から
  inline 導出):
  - **(a) member-family-from-accumulator**: pairUnion S₀ pair i の蓄積 X-members を orthonormal IrreducibleCharacter
    family (ι/s/χmem/deg/i₁) として列挙 + supports/orthonormality/conj-ortho/hSgen/hgen。enum 構成 (combinatorial)。
  - **🔴 (b) hDeg (degree 不等式 2a<∑deg²) は (6.5) 還元依存**: deg i=χmem i(1)/χ₁(1) の **p-power 構造**
    (`two_mul_lt_sq_of_primePow_gap` S07:1696) が要る。p-power は **(6.5) chief-factor 還元**から来る。

### 🔴 (6.5) 還元 = T-A4 の真の次 blocker (§6 degree-bound machinery, 未着手の大タスク)

**mmd 04.8 L56-** (精読済): (6.5) は Hyp(6.4) + S(M) 非 coherent 下で **(a)** K/H₁ は L の chief factor かつ
`|K:H₁|≤4|L:K|²+1` **(b)** ∃p, K/M は非可換 p-群 **(c)** |L:K|∤p−1。**(6.8) が使うのは (b)** (p-群還元)。
**proof 依存 chain**: (6.5) ⟸ **(6.3)** (degree bound `|K:H₁|≤4|L:K|²+1`) + (6.4.c) + nilpotency。
(6.3) ⟸ **(6.2)** + **(5.7)**。

**既存状態 (grep 確認)**:
- ✅ **(5.7)** (mmd 04.7 L107 「χ(1) が χ∈S で一定 ⟹ S coherent」= 等次数 coherence) ≈ **`coherentEqualDegree`/
  `coherentEqualDegree_fromDade` 既 landed** (S07)。実質形式化済 (要確認: 厳密一致か)。
- 🔴 **(6.2)/(6.3)** = degree-bound 定理 (Sibley 型 `|K:H₁|≤4|L:K|²+1`)。**未形式化**。これが (6.5) 還元の
  律速。§6 の coherence-degree machinery を新規形式化要 (substantial, 複数定理)。

**(6.2)/(6.3) 精読済 (mmd 04.8 L7-52)**:
- **(6.2)** `2|L:C|√|C:D|≥|K:A|−1`: proof は **(i) Theorem (5.6) 量的形** = 非coherence (S₁ coherent ∧ S₁∪{ψ,ψ̄}
  非coherent) ⟹ `2ψ(1)|L:K|≥∑_{χ∈S₁}χ(1)²/‖χ‖²` (= §G **B1** (5.6)反転, 未 landed; forward `retarget_isCoherent`
  の量的逆) + **(ii) degree-sum 恒等式** `∑_{S(A)}χ(1)²/‖χ‖²=|L:K|(|K:A|−1)` (= §G **B2**, X-side; `sumNonInflatedDegreeSq_eq_index_mul`
  類は Irr-L 側のみ landed, S(A) 側は要拡張) + **(iii)** θ(1)≤|K:C|√|C:D| (Sibley char-degree bound, 要確認)。
- **(6.3)** `|H:H₁|>4|L:K|²+1 ⟹ S(M) coherent`: (6.2) を C=H,D=A で適用 + minimal-A 帰納 (代数のみ, (6.2) 後は機械的)。
- **(6.5)** `K/H₁ chief factor + p-群`: (6.3) の対偶 (`|K:H₁|≤4|L:K|²+1`) + (6.4.c) + nilpotency (代数)。

**⟹ (6.8) capstone への完全残路 (bottom-up)**:
1. **§G B1** = Theorem (5.6) 量的形 (非coherence⟹degree-sum下界)。`retarget_isCoherent` の hypotheses (特に
   degree 不等式 `2a<∑aᵢ²`) の対偶。**foundational・未 landed**。
2. **§G B2** = S(A)-side degree-sum 恒等式 `∑_{S(A)}χ(1)²/‖χ‖²=|L:K|(|K:A|−1)`。**部分既 landed**:
   `sumNonInflatedDegreeSq_eq_index_mul` (InflationCharacter:374) が **case A の Irr-L-side**
   `∑_{χ∈Irr L, Z⊄ker χ}χ(1)²=[L:H][H:Z](|Z|−1)` を Burnside on L で供給 (case A は X⊆Irr L ゆえ X-side と一致)。
   **(6.2) の S(A)-side は追加要**: `∑_{S(A)}χ(1)²/‖χ‖²=|L:K|∑_{θ∈T}θ(1)²` (induced-char の W₁-orbit
   |L:K|-to-1 counting) + `∑_{θ∈Irr(K/A)∖1}θ(1)²=|K:A|−1` (Burnside on K/A, core=`sumIrreducibleDegreeSq`+inflation 既存)。
   orbit counting (S(A)={distinct Ind θ} ↔ T={θ} の |W₁|-to-1) が新規部分。
3. θ(1)≤|K:C|√|C:D| bound。
4. (6.2)→(6.3)→(6.5) (上記, B1/B2/bound 後は代数 + 帰納)。
5. T-A4 part(a) member-family enum → T-A4 assemble → T-A5 glue (coherentUnion_of_glued, Y=coherentYFamily)。

route A で ZIrr は解決済。残は §6 degree-bound machinery (B1/B2 が foundation) + enum 構成 (ZIrr 非依存)。

### §6 degree-bound machinery 進捗 (2026-06-04, route A 後の継続)
- ✅ **B2 ingredient 1** (commit 90d67af, axiom-clean, full build 3562): `sumInflatedDegreeSq_ntrivial`
  (`OddOrder.RepresentationTheory`, InflationCharacter.lean:332) = `∑_{χ∈Irr G, N⊆ker χ, χ≠1}χ(1)²=|G⧸N|−1`
  (= (6.2) の `∑_{θ∈T}θ(1)²=|K:A|−1`, G=K/N=A)。`sumInflatedDegreeSq` − trivial(1)。
- 🔴 **B2 残 (orbit counting)**: `∑_{S(A)}χ(1)²/‖χ‖²=|L:K|∑_{θ∈T}θ(1)²` = induced-char の W₁-orbit
  |L:K|-to-1 counting (χ=Ind θ, χ(1)=|L:K|θ(1), inertia=K で Ind 既約)。substantial・要 induced-char inertia 機構。
- 🔴 **B1 = (5.6) 量的形**: `S₁ coherent ∧ S₁∪{ψ,ψ̄} 非coherent ⟹ 2ψ(1)d₁≥∑_{χ∈S₁}χ(1)²/‖χ‖²`。
  forward (`retarget_isCoherent`/`xAdjoinStep`) の対偶だが aux 仮説 (member family 等) の Sibley-setup-packaging
  が要 ⟹ **member-family 構成と共有** (T-A4 part(a) と同じ foundational piece)。
- 🔴 **θ-degree bound**: `θ(1)≤|K:C|√|C:D|` (D/B⊆Z(C/B))。基本 Schur bound (`finrank_sq_le_index`/
  `exists_degree_sq_le_index`@SchurCenterBound, θ(1)²≤[K:Z(K)]) では不足、section D/B⊆Z(C/B) の Clifford 論証要。
- **(6.2)→(6.3)→(6.5)**: 上記 B1/B2/θ-bound + Sibley-setup ((C).b 抽出) を組めば (6.2)、以降 (6.3)(6.5) は代数+帰納。
- ✅ **(6.3) arithmetic core** (commit a6a2082, axiom-clean): `degreeBound_le_of_sqrt_bound`
  (S08) = `b·x−1 ≤ 2ab√x (b,x≥1) ⟹ x ≤ 4a²+1`。(6.3) の degree-bound 帰結 (mmd L33) の純 ℝ/ℕ 算術核。
  (6.3) は (6.2) + これ + minimal-A/maximal-B 帰納で完成。
- **recurring 算術 motif** (記録): (6.5)(a)(c) は `(2c+1)²>4c²+1 ⟺ c≥1` を多用 (chief-factor 不在背理法,
  |L:K|∤p−1)。小さく landable だが (6.2)/(6.3) の本体待ち。
- **(6.5)(b) p-群還元の群論核**: 「G nilpotent finite + G/[G,G] が p-群 ⟹ G が p-群」(nilpotent=Sylow 直積,
  G/[G,G]=∏ Sylow_q/[..] ⟹ p-Sylow のみ非自明)。self-contained・mathlib nilpotent/Sylow で landable 見込み。
- **最高レバレッジ次ピース = member-family 構成** (B1 と T-A4 part(a) で共有)。Sibley-setup framework
  ((6.1)/(6.4) = SibleyDadeHypothesis 拡張) の formalization が要。focused effort 推奨。
- ✅ **(6.5)(a) 算術核 landed** (commit 353298c, axiom-clean): `two_mul_add_one_le_of_odd_dvd`
  (Odd c, Odd a, c∣a−1, a>1 ⟹ a≥2c+1)。chief-factor 不在背理法で |K:H₂|≥2|L:K|+1。
- 🔴 **(6.5)(c)** = 非可換 p-群⟹p²∣|G^{ab}| は **Frattini/Burnside-basis 要 (mathlib に Frattini API absent)** ゆえ
  blocked; (6.8) critical path は (6.5)(b)✅ ゆえ非必須の見込み。
- **landed §6 bricks (6 this session)**: sumInflatedDegreeSq_ntrivial (B2 core) / degreeBound_le_of_sqrt_bound
  ((6.3) arith) / isPGroup_of_quotient_of_subgroup (p-群拡大) / Abelianization.map_surjective +
  subsingleton_of_isPGroup_of_not_dvd (汎用) / **isPGroup_of_isNilpotent_of_isPGroup_abelianization
  ((6.5)(b) reduction core)** / two_mul_add_one_le_of_odd_dvd ((6.5)(a) arith)。
  **🆕 (6.2) 精密分解 (2026-06-04, mmd 04.8 L7-22 精読)** — (6.2) 証明は **5 ingredient**:
  - **step2 (S(A) 非空)** = ✅✅ **LANDED this session** (existence layer 4 補題):
    `exists_monoidHom_units_ne_one_of_commutator_ne_top` (Γ→*ℂˣ) → `_irreducibleCharacter_ne_trivial_degree_one_`
    → `_subset_kernel_` (= θ∈S(A)) + `inflate_trivial`/`inflate_eq_trivial_iff` (InflationCharacter.lean)。
    **earlier「`HasEnoughRootsOfUnity ℂ` absent」で blocked と誤判定 → `IsSepClosed.hasEnoughRootsOfUnity` instance
    (ℂ sep closed + char 0) を `NeZero ((exponent:ℂ))` provision で発火させ攻略**。commits 6243ef1/9797ed4/684c9ac。
  - **step4b (`∑_{θ∈T}θ(1)²=|K:A|−1`)** = ✅ **LANDED** (`sumInflatedDegreeSq_ntrivial`, B2 core, T≅Irr(K/A)∖1)。
  - **step4a (B2-orbit, `∑_{S(A)}χ(1)²/‖χ‖²=|L:K|∑_Tθ(1)²`)** = ✅✅✅ **COMPLETE (commit 8acc696, axiom-clean, full build 3571)**。
    `sum_div_normSq_induce_image_eq (T conjBy-invariant Finset ⊆ Irr H) : ∑_{Ind θ}χ(1)²/‖χ‖²=[G:H]∑_Tθ(1)²`。
    abstract 形 (T-不変性を仮説化、K/A subgroup friction 回避)。組み立て: `Finset.sum_fiberwise_of_maps_to`
    で T→S(A) fibre 分解; 各 fibre = θ₀ の G-軌道 (下記 sub-lemma) → degree 一定 + fibre-card で telescoping。
    **sub-lemmas (全 axiom-clean, 再利用可)**:
    (1) `induce_eq_induce_iff_conj` (3d29f2e): Ind θ=Ind ψ ⟺ ∃g conjBy g θ=ψ (fibre=軌道)。
    (2) `card_conjByOrbit_eq_index_inertia` (3547d3c): Nat.card(conjByOrbit θ)=[G:I] (Clifford `conjByOrbitEquivLeftCosets`)。
    (3) `conjBy_apply_one` + `card_filter_induce_eq_index_inertia` (fd8d8f0): degree 保存 + fibre-card=[G:I]。
    算術 [G:H]|H|=|G|=[G:I]|I| (`Subgroup.index_mul_card`) → `linear_combination`。
  - **step3/5 (B1 = 5.6 quantitative, `2ψ(1)≥|K:A|−1`)** = 🔴 残, **Pf Thm 5.6 (quantitative coherence) keystone 要**。
  - **step6 (θ-bound `θ(1)≤|K:C|√|C:D|`)** = 🔴 残。**中心 case `θ(1)²≤|K:Z|, Z⊆Z(K)` = ✅ `exists_degree_sq_le_index`**。
    **🆕 重要: (6.6) p-群 path (mmd 04.8 L80) は [Is]Cor2.30 = 中心 case を直接使う (✅済)**; section case
    (D/B⊆Z(C/B)) は (6.3) 一般形でのみ (Clifford restriction 要)。
  - **(6.5)(c)** = Frattini absent (上述, ただし (6.5)(b)✅ ゆえ (6.8) critical path 非必須見込み)。
  **次着手推奨**: (a) **B2-orbit** (self-contained 文字理論, proof sketch 確定済, framework 不要で着手可能) →
  (b) **Pf Thm 5.6 quantitative coherence** (= B1 keystone, (6.2)/(6.3)/(6.6) 共通) → (c) **θ-bound section**。
  framework は IsCoherent (S07) 既存; 残 keystone は **Thm 5.6 の量的不等式**。

### ✅✅ 2026-06-05 (peterfalvi worktree) — B1 + (6.3)/(6.5) 還元 backbone landed
- ✅ **B1 = Pf (5.6) quantitative** (commit 5a5e0bd, axiom-clean, full build 3555): `coherentDegreeSumBound_of_not_coherent`
  (S08) = forward engine `xAdjoinStep` の対偶。非 coherent(S₁∪{χ,χ̄}) ⟹ `∑ᵢ(deg i)² ≤ 2a` (= `∑χ(1)² ≤ 2ψ(1)χ₁(1)`)。
  `by_contra`+`push_neg` で xAdjoinStep の `hDeg : 2a < ∑deg²` を対偶。**member-family 仮説は明示のまま** (forward と同じ;
  Sibley setup での discharge = T-A4 enum)。⟹ §G 「B1 (5.6) 反転欠落」blocker 解消。step3/5 ✅。
- ✅ **(6.3)/(6.5) 還元 arith** (commit 810faf5, axiom-clean): `six_three_HH1_le` ((6.3): (6.2) index-bound +
  `degreeBound_le_of_sqrt_bound` + `|H:H₁|≤|H:A|` ⟹ `|H:H₁|≤4|L:K|²+1`) / `six_five_index_contradiction`
  (共有 `(2c+1)²≤n≤4c²+1` 不能) / `six_five_chief_factor_contradiction` ((6.5)(a) chief factor) /
  `six_five_c_contradiction` ((6.5)(c))。**(6.5)(b) p-群 core ✅ + two_mul_add_one ✅ と合わせ (6.5) backbone は (6.2) を除き完成**。
- **残 (option 1 の (6.2) 本体 + glue)**: (i) **θ-bound section case** `θ(1)≤|K:C|√|C:D|` (D/B⊆Z(C/B), Clifford
  restriction; 中心 case ✅) 🟡 **半分 landed (下記)**, (ii) **Sibley packaging** (S₁/ψ 構成 + B1 を member-family enum 経由で適用 + B2 接続 ⟹
  (6.2) `2|L:C|√|C:D|≥|K:A|−1`; 算術 shell は自明、構成が hard) 🔴, (iii) (6.3)/(6.5) を SibleyDadeHypothesis の
  実 index に結線。

### ✅ 2026-06-05 θ-bound section degree bound (b-half) landed
- ✅ **`degree_sq_le_index_of_central_quotient`** (commit b61b834, `OddOrder.RepresentationTheory` @InflationCharacter,
  axiom-clean, full build 3555): φ∈Irr G が N 上自明 + N≤D + `D/N≤Z(G/N)` ⟹ **`φ(1)²≤|G:D|`**。inflation
  (`exists_inflate_eq_of_subset_characterKernel`+`inflate_apply_one`) で G/N に落とし中心 case `exists_degree_sq_le_index`
  適用 + quotient index `(D.map mk' N).index=D.index` (`index_comap_of_surjective`+`comap_map_eq`+`ker_mk'`)。
  = θ-bound の `φ(1)≤√|C:D|` 半分 (中心 case は N=⊥ 特殊化)。InflationCharacter に SchurCenterBound import 追加 (cycle 無)。
- 🔴 **θ-bound 残 = Clifford restriction (a-half)** `θ(1)≤|K:C|·φ(1)` (φ=Res_C θ の constituent, 乗数 `e²≤|I:C|`):
  **mathlib/repo に induced/restricted character の multiplicity/inertia 機構が無い** = 真の gap。これが full θ-bound
  ⟹ (6.2) を塞ぐ。**次着手 = (a) Clifford restriction infra 新規構築 (substantial, mathlib gap) または (b) T-A4
  member-family enum (Sibley packaging と共有)**。

### mathlib API 知見 (substantial ピースの調査削減, 2026-06-04 確認済)
- ✅✅ **(6.5)(b) reduction core 完成** (commit bf4fcf2, axiom-clean, full build 3562): 
  `isPGroup_of_isNilpotent_of_isPGroup_abelianization` (S08) = finite nilpotent Γ + Abelianization Γ が
  p-群 ⟹ Γ が p-群。**quotient route で直積回避が成功**: P=Sylow_p normal (tfae idx 0→3) → Q=Γ⧸P の
  Abelianization が p-群(image)かつ p'-群(order coprime, `Sylow.not_dvd_index`)⟹ trivial ⟹ Q perfect
  nilpotent ⟹ trivial (`IsSolvable.commutator_lt_top_of_nontrivial`) ⟹ P=⊤。**API 罠解決**: tfae は tactic-mode
  `(isNilpotent_of_finite_tfae (G:=Γ)).out 0 3 |>.mp ‹_› p ‹_› P` + `haveI hPnormal`; `commutator_lt_top` は
  `(G:=Γ⧸↑P)` 明示; `@Nat.card_of_subsingleton α 1 inst` (引数順 α a inst)。
  + helper `Abelianization.map_surjective` / `subsingleton_of_isPGroup_of_not_dvd` (汎用, mathlib に無)。
- ✅ **(6.5)(b) ingredient** (commit 8215e94): `isPGroup_of_quotient_of_subgroup` (p-群拡大, Lagrange+iff_card)。
- **(6.5)(b) 全体の clean strategy (Pi-type 直積 回避)**: P_p=Sylow_p(G) (nilpotent ⟹ normal·unique)。
  Γ⧸P_p は p'-quotient (order coprime p)。`(Γ⧸P_p)^{ab}` は **G^{ab} の商ゆえ p-群** かつ **order|Γ⧸P_p| ゆえ
  p'-群** ⟹ trivial (p^k coprime p ⟹ k=0)。⟹ Γ⧸P_p perfect nilpotent ⟹ **trivial** (← nontrivial nilpotent は
  commutator<⊤ = `IsSolvable.commutator_lt_top_of_nontrivial`+nilpotent⟹solvable) ⟹ Γ=P_p ⟹ p-群。
  **完全 recipe (全 mathlib 補題確定済, ~60-80 LOC の assembly のみ残)**:
  1. `obtain ⟨P⟩ : Nonempty (Sylow p Γ) := inferInstance`。
  2. `(↑P).Normal := (isNilpotent_of_finite_tfae (G:=Γ)).out 0 3 |>.mp inferInstance p inferInstance P`
     (tfae idx 0=IsNilpotent, 3=∀ Sylow Normal)。
  3. Q:=Γ⧸↑P。`Abelianization.map (QuotientGroup.mk' ↑P) : Abelianization Γ →* Abelianization Q` 全射
     (mk' 全射 + Abelianization.map 全射性) ⟹ `IsPGroup p (Abelianization Q)` = `h.of_surjective …`。
  4. `|Abelianization Q|` ∣ `|Q|` = `(↑P).index`, `Sylow.not_dvd_index P : ¬p∣(↑P).index` ⟹ Abelianization Q は
     p-群(3)かつ order coprime p ⟹ `p^k coprime p ⟹ k=0` ⟹ `Subsingleton (Abelianization Q)`。
  5. Abelianization Q trivial ⟹ Q=⁅Q,Q⁆ (perfect)。Q nilpotent (quotient)。nontrivial nilpotent は
     `IsSolvable.commutator_lt_top_of_nontrivial` で commutator<⊤ ⟹ 対偶で `Subsingleton Q`。
  6. Q=Γ⧸↑P trivial ⟹ `(↑P)=⊤` ⟹ **landed `isPGroup_of_quotient_of_subgroup` を N=↑P で直接消費**
     (P:Sylow は IsPGroup p ↥P, Q:trivial は IsPGroup p Q) ⟹ `IsPGroup p Γ`。
  directProductOfNormal 不要。
  **🔶 bounded attempt 実施→revert (2026-06-04, anti-scaffold gate)**: full (6.5)(b) を書いたが 3 API friction
  で 6 iteration 後 revert (p-群拡大 lemma は committed 保持)。**残 friction (focused continuation 用)**:
  (i) **tfae 抽出構文**: `((isNilpotent_of_finite_tfae (G:=Γ)).out 0 3).mp …` が "Function expected"/
  "instance expected" — `.out i j` の bounds autoParam か `IsNilpotent` instance 渡しの構文要調整 (代替:
  Sylow normal-for-nilpotent の直接 instance 探索 or `normalizerCondition`/別 tfae index 経由)。
  (ii) **perfect⟹trivial の type 整合**: `IsSolvable.commutator_lt_top_of_nontrivial` の `[Nontrivial Q]`
  instance 化 + `(commutator Q).index = Nat.card (Abelianization Q)` の defeq/rw。
  (iii) `Nat.card_of_subsingleton` の Subsingleton instance synthesis (haveI 化済だが 1712 で未解決)。
  **✅ 2 helper は build 成功・正しい (revert 済だが再利用可)**: `Abelianization.map_surjective`
  (f 全射⟹map 全射, `QuotientGroup.induction_on`+`Abelianization.map_of`), `subsingleton_of_isPGroup_of_not_dvd`
  (p-群 + order coprime p ⟹ Subsingleton, `iff_card`+`dvd_pow_self`+`card_eq_one_iff_unique`)。
- **B2 orbit counting**: `card_mul_inner_self_induce_eq_card_inertia` (InducedIrreducible:172, `|H|·‖Ind θ‖²=|I_G(θ)|`)
  + `induce_apply_one` (χ(1)=[L:K]θ(1)) で per-θ。残 = S(A)={distinct Ind θ}↔T の W₁-orbit 分割 (fiber=inertia-orbit,
  Frobenius で size=|L:K|・degree 一定) の degree-sum 組立。
- **(6.5)(c) arith motif**: `(2c+1)²>4c²+1 ⟺ c≥1` (inline 可, lemma 不要)。
- **B1/θ-bound**: B1=Sibley-setup packaging (xAdjoinStep aux 仮説の always-true 化 + 対偶); θ-bound=Clifford
  中心 section (基本 Schur `exists_degree_sq_le_index`@SchurCenterBound では不足)。両者 framework/Clifford 要・最重。
- 🟢 **T-A5 = T-A4 後** (coherentUnion_of_glued で X∪Y glue, Y=coherentYFamily; field 追加で hνZ 不要に)。

## Blocked ログ (revert した task と欠落 primitive を追記)

> ⚠️ **更新 (2026-06-04 後続セッション)**: 下記 T-A3 blocked は **解決済** (route A 完遂, commit a054bc8 +
> be9cd14)。当初「大規模 cascade で予算超過」と判断したが、open-ended goal で実施し full build green。
> **重要な設計訂正**: field は global `∀φ∈ZIrr L` でなく **`∀φ∈zSpan S`** (ℤ[S] 上) が正しい
> (global は coherentPair の `retarget (Dade τ)` で偽; Dade map は supported lattice のみ isometry)。
> 全 constructor が uniform span_induction で discharge 可、新仮説は X,Xbar∈ZIrr のみ。T-A4/T-A5 も unblock。
> 以下は当時の分析記録 (歴史的参考)。

### T-A3 (route A: IsCoherent に extension_mem_ZIrr field 追加) — ✅ 解決済 (当時 blocked 判断)
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
