# 自走 goal: (6.8) B step 3-4 — X-family coherence path 配線 (2026-06-03)

## 作業場所 (厳守)
- **ONLY** `/home/ywr/odd-order-pf-engine` (branch `pf-engine-support`)。
- **絶対に触らない**: `/home/ywr/odd-order` (main = 不可侵) / `/home/ywr/odd-order-repr-infra` (別セッション LIVE)。
- Bash cwd は毎回 main にリセット ⟹ 全コマンドで `cd /home/ywr/odd-order-pf-engine && …`。

## 現状 (この goal の出発点)
- ✅ T7 c1 (`X⊆Irr L`) + **B step1-2 完了・build-green・commit 済** (0ba7572 / 0a664bf)。
- **B の核心 blocker `htau1_mem0 : τχ∈ZIrr` は step1 で解消済** (`retarget_isCoherent_of_supportedDecomposition`
  が X:=Da.X を supported route で構成)。残るは support-surgery + 配線のみ。

## ゴール (1 つ)
**X-family の coherence path を配線**: `retarget_isCoherent_fromDade_X` を構築し `DadeChainStep` を X 対応にして、
`peterfalvi_66_coherence_of_X_from_dade`(S07:5249) 系が**実 induced X-family** (`χ=Ind_H^L θ`, χ(1)≠0,
差分 χ−a·χ₁ は 1 で消え H^# supported) で **instantiate 可能**にする。build-green + AxiomsCheck green + commit。

## 計画 (step 3 → 4; §I = notes/peterfalvi/s08_6_8_assembly_plan.md も参照)
- **step3a — `dadeOrthonormalCharacterImageFamily`(S07 ~4500) を差分-support に弱化**:
  現状 `hχsupp`/`hχbarsupp` (個別 `χ.support⊆A`) を要求するが X-member で偽。R(χ) は `τ(χ−χ̄)` の
  ±既約分解ゆえ **χ−χ̄ (1 で消え A-supported) のみ**で足りる。内部の
  `dadeIntegralCharacterMap_inner_eq_on_supported_span`(4460, 個別 `hS:∀s∈S,supp⊆A` 要求) を
  **差分集合 S={0, χ̄−χ}** で適用 (0 は常に supported, χ̄−χ は差分 hyp で supported)。
  hyp を `hdiffsupp:(χ.conj−χ).support⊆supportInSubgroup A L` 単一に弱化、内部 span 生成元を差分集合に。
  ⚠️ 既存の supported-χ caller を壊さないこと (個別 supp を持つ場合は差分も導けるので後方互換 helper を残す or
  caller 側で差分を供給)。
- **step3b — `retarget_isCoherent_fromDade_X`**: 既存 `retarget_isCoherent_fromDade`(4946) を template に、
  **D₀/htau1_mem0/個別 support を除去**。Da を `CharacterPsiDecomposition.ofProjection`(htau1_mema のみ;
  decompositionPair の `.2` と同じ構成, S07:1138 参照) で構成し、差分-support 版 imageFamily を渡して
  **step2 `retarget_isCoherent_of_supportedDecomposition_and_memberFamily`** を呼ぶ。`hchi1chi1:⟨χ₁,χ₁⟩=1`
  は χ₁∈S₁ 既約から供給。
- **step4 — `DadeChainStep`(5065) rewire**: field `hχsupp`/`hχbarsupp`/`haχ1supp` を差分-support 化、
  `advance`(5146) を `fromDade_X` 経由に。`peterfalvi_66_coherence_of_X_from_dade`(5249) が compose 確認。
  抽象 `peterfalvi_66_coherence_of_X`(3934) は不変。

## ANTI-SCAFFOLD GATE (絶対)
- sorry/admit/新 axiom を**足してビルドを通さない**。hypothesis を vacuous/False に弱めない。
- **各 commit `lake build OddOrder` green 必須** (transcript に Bash 出力で報告 — /goal 評価器は transcript のみ読む)。
- `lake build OddOrder.AxiomsCheck` green、弱化 lemma は axiom-clean (sorryAx 無, `#print axioms` で確認)。
- build-green に**できない**なら → 本ファイル WIP に done/stuck/why を追記して **STOP**。**scaffold より停止**。
- 既存の supported-χ path (Y-family / base case `coherentPair_fromDade`) を壊さない (full build で検証)。

## 完了条件
`retarget_isCoherent_fromDade_X` + DadeChainStep X-wiring 完成、`peterfalvi_66_coherence_of_X_from_dade` が
実 induced family で instantiate 可能 (or その手前まで build-green に到達)、`lake build OddOrder` + AxiomsCheck green、
新 sorry 無、全部 commit 済 → 本ファイルに完了 summary を書いて **STOP** (再 schedule しない)。

## 各 iteration / wake で
1. `cd /home/ywr/odd-order-pf-engine`; `git status` (branch=pf-engine-support, clean 確認)。
2. 本 spec + §I + 下の WIP を読み、続きから。Edit → `lake build OddOrder.Peterfalvi.S07_Coherence` (速い) →
   green なら `lake build OddOrder` → green なら commit。
3. **自分の status を信じず独立再検証**: build green / `grep -rn "sorry\|admit" OddOrder/Peterfalvi/S0{7,8}*.lean`
   で新規無 / AxiomsCheck。
4. 完了 → summary 書いて STOP。stuck → WIP report 書いて STOP。それ以外 → 続行。

## WIP log
- 2026-06-03 setup: step1-2 完了済 (htau1_mem0 解消)。未着手 = step3a (`dadeOrthonormalCharacterImageFamily`
  差分-support 弱化)。まず S07:~4500 の def を Read し、`hχsupp`/`hχbarsupp` の使用箇所 (特に 4451 付近の
  `hSsupp`→`dadeIntegralCharacterMap_inner_eq_on_supported_span`) を trace、差分集合 {0,χ̄−χ} 化の最小 diff を設計。

## 🛑 LOOP STOPPED (2026-06-03, anti-scaffold gate) — step1-2 が scaffold と判明, 真の fix は structure-field 弱化

**結論**: B step1-2 (`retarget_isCoherent_of_supportedDecomposition[_and_memberFamily]`, commits
0ba7572/0a664bf) は **X-family に対して scaffold**。build-green だが、入力の
`Da : CharacterPsiDecomposition τ χ (a•chi1)` が **X-member では構成不能**。

**精密な blocker**: `CharacterPsiDecomposition` の field
`tau1_inner_eq_on_support : ∀ φ ζ ∈ zSpan{χ,χ.conj,ψ}, ⟨tau1 φ, tau1 ζ⟩=⟨φ,ζ⟩` は **full lattice**
(χ 単体を含む) で要求。Da 構成には tau1=τ (Dade) でこれを供給する必要があるが、unsupported χ=Ind θ では
`⟨τχ,τχ⟩≠⟨χ,χ⟩` (Dade は off-support 任意延長)。`dadeIntegralCharacterMap_inner_eq_on_supported_span`
は generators supported を要求するゆえ χ で使えない。⟹ **Da は X で構成不能** = step1-2 の hypothesis は
unmeetable ([[scaffold-sorry-free-not-done]] の hoist パターン)。**「htau1_mem0 解消」は誤り** — blocker が
D₀ から「Da 構成」へ移っただけ。**step1-2 は supported-χ では valid な conditional 定理** (削除不要だが X には効かない)。

**🟢 真の fix を sharpening (loop iter2 の "core framework restructuring" を具体化)**:
`tau1_inner_eq_on_support` の **4 つの使用箇所 (S07:1227/1296/2216/3473) は全て差分** (χ−ψ, χ−χ.conj) で、
**χ 単体では一度も使われない** (grep 確認済)。⟹ field を **差分 sublattice `zSpan{χ−χ.conj, χ−ψ}`** に
弱化すれば: (a) 使用側は差分ゆえそのまま valid、(b) X でも供給可 (差分 supported → step3a と同じ差分集合 isometry)。
**blast radius**: htau1_inner_eq param が ofProjection(1052)→decompositionPair(1104)→
retarget_isCoherent_of_sharedDecomposition(3437)→retarget_isCoherent_fromDade(4983) を貫流、各所で供給
(現状 full {χ,χ.conj,..} supported S 経由 → 差分集合へ re-target) + helper `chi_sub_{psi,conj}_mem_zSpan_support`。
~7-10 関数の mechanical だが invasive な structure 改修 = **attended 推奨** (autonomous で structure field 型変更は
cascade 破壊リスク; loop が flag した intricate core surgery そのもの)。

**✅ genuine な成果 (keep)**: **step3a `dadeOrthonormalCharacterImageFamilyOfDiff` (commit 18238b9)** は
正しく X で構成可能な差分-support R(χ) = field 弱化後の X-path の正当な部品。T7 c1 + step1-2 (supported-χ 用) も build-green。

**なぜ STOP**: structure field 弱化は ~7-10 関数貫流の invasive 改修で、autonomous 14-turn では cascade 破壊して
broken build を残すリスク大。gate 通り scaffold せず停止。**stuck**。attended で field 弱化を実施推奨。
