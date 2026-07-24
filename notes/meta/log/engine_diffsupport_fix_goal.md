# 自走 goal: (6.8) engine support-interface 修正 (§G-A) — 2026-06-03 overnight

> ⚠ **DEAD（退役 worktree `odd-order-pf-engine` 向け 2026-06-03 goal; 終了済）**。本ノートは履歴。(注記 2026-07-02)

## 作業場所 (厳守)
- **ONLY** `/home/ywr/odd-order-pf-engine` (branch `pf-engine-support`)。
- **絶対に触らない**: `/home/ywr/odd-order` (main = 不可侵) / `/home/ywr/odd-order-repr-infra` (別セッション稼働中)。
- Bash cwd は毎回 main にリセットされる ⟹ 全コマンドで `cd /home/ywr/odd-order-pf-engine && …` か絶対パス/`git -C`。

## ゴール (1 つ)
監査 (notes/peterfalvi/s08_6_8_assembly_plan.md §G-A) が見つけた engine interface bug を修正:
`DadeChainStep` と consumer が **個別** support `χ.support ⊆ supportInSubgroup A L` を要求するが、
実 (6.8) X-family `χ = Ind_H^L θ` は χ(1)=|W₁|θ(1)≠0 ⟹ 1∈χ.support、だが A=sharpImage H は 1 を除外
⟹ **充足不能**。これを **差分 support** に弱化する。**既 landed の `coherentEqualDegree_fromDade`
(S07_Coherence.lean ~4842, Y-family 用に同じ弱化を受け `hsuppdiff:(χ_i−χ_0).support⊆…` を持つ) が完全な template**。

## 弱化対象 (S07_Coherence.lean)
- `DadeChainStep` (~5065): `hχsupp`/`hχbarsupp`/`haχ1supp` (個別) → (χ−χ̄)・(χ−a·χ₁) の差分 support。
- `retarget_isCoherent_fromDade` (~4946) の `hχsupp` (~4952)。
- `dadeOrthonormalCharacterImageFamily` (~4410): 個別→差分 (proof は ~4440-4443 で既に `hdiff_supp` に
  collapse している。それを hypothesis 側に上げる)。
- `coherentPair_fromDade` (~4787)。
- `dadeIntegralCharacterMap_inner_eq_on_supported_span` (~4326) の `hS:∀s∈S,s.support⊆A` link。
- `peterfalvi_66_coherence_of_X_from_dade` (~5249): DadeChainStep を consume — 弱化後も compose 確認。
- **抽象 `peterfalvi_66_coherence_of_X` (~3934, support field 無) は正しい ⟹ 変更しない**。修正は `_from_dade` 層のみ。

## 進め方
`coherentEqualDegree_fromDade` (~4842) を逐語 template に。各 lemma の proof が**実際に何を使うか**を trace
(監査確認済: 差分 χ−χ̄, χ−a·χ₁ のみ isometry に渡る; 個別 support は over-strong)。hypothesis を差分形に弱化し
proof を差分で thread、rebuild。

## ANTI-SCAFFOLD GATE (絶対)
- sorry/admit/新 axiom を**足してビルドを通さない**。
- hypothesis を vacuous/False に弱めない、genuine な義務を削除しない。
- **各コミットは `lake build OddOrder` green 必須**。coherent な小単位ごとに commit。
- 差分 support 弱化で build-green に**できない**なら → 本ファイルに WIP report (done/stuck/why) を追記して **STOP**。
  **scaffold するくらいなら止まる**。
- `lake build OddOrder.AxiomsCheck` green、弱化 lemma は axiom-clean (sorryAx 無) を確認。

## 完了条件
`lake build OddOrder` + `AxiomsCheck` green、差分 DadeChainStep が**実 induced X-family で充足可能**
(χ_i=Ind_H^L θ_i、χ_i−χ_j は 1 で消え H^# 上 supported)、抽象 `peterfalvi_66_coherence_of_X` 不変、
新 sorry 無、全部 `pf-engine-support` に commit 済。→ 本ファイルに完了 summary を書いて **loop を STOP**。

## 各 iteration / wake で
1. `cd /home/ywr/odd-order-pf-engine`; `git status` (自分の branch・clean 確認)。
2. 下の WIP section を読み、続きから。Edit → build → (green なら) commit。
3. **自分の status を信じず独立再検証**: build green / `grep -rn "sorry\|admit" OddOrder/Peterfalvi/S07_Coherence.lean` で新規無 / AxiomsCheck。
4. 完了 → summary 書いて STOP (再 schedule しない)。stuck → WIP report 書いて STOP。それ以外 → 続行。

## WIP log
(各 iteration はここに「やったこと・build 状態・次の一手」を追記)
- 2026-06-03 setup: worktree 作成・warm build green (3562)。未着手。次 = `coherentEqualDegree_fromDade`
  と `DadeChainStep`/`dadeOrthonormalCharacterImageFamily` の proof を読み、差分 support 弱化の最小 diff を設計。
- 2026-06-03 iter1 (調査・feasibility ✅、コード変更なし・build green 維持): `dadeOrthonormalCharacterImageFamily`
  (S07:4410) の個別 `hχsupp`/`hχbarsupp` の使用箇所を trace。2 箇所: (a) `hdiff_supp`(4440, 差分 support 導出=OK)
  (b) **`hSsupp`(4451) → `dadeIntegralCharacterMap_inner_eq_on_supported_span`(4326) が span 生成元 {χ,χ̄} の
  個別 support `hS:∀s∈S,s.support⊆A` を要求** ← X-member (Ind θ, χ(1)≠0) で偽。**確定した修正方針**:
  isometry を {χ,χ̄}-span でなく**差分集合 {diff 0=0, diff 1=χ̄−χ}-span** に適用する (diff 0=0 は常に supported、
  diff 1=χ̄−χ は新仮説 hdiffsupp で supported)。`dadeIntegralCharacterMap_inner_eq_on_supported_span` は
  S={差分} で適用でき、個別 support 不要。`hdiff_zspan` も {χ̄−χ}-span に。⟹ agents の「差分のみ使用」裏付け。
  **実行計画**: (1) `dadeOrthonormalCharacterImageFamily` の hyp `hχsupp`/`hχbarsupp` → 単一
  `hdiffsupp : ((χ:CF).conj − (χ:CF)).support ⊆ supportInSubgroup A L`、内部 hSsupp/hdiff_zspan を差分集合に。
  (2) caller 連鎖を伝播: `DadeChainStep`(5065) の hχsupp/hχbarsupp/haχ1supp → 差分形、`retarget_isCoherent_fromDade`(4946)、
  `coherentPair_fromDade`(4787)。(3) consumer `peterfalvi_66_coherence_of_X_from_dade`(5249) が差分 support を供給できるか確認。
  各 step build-green + AxiomsCheck。抽象 `peterfalvi_66_coherence_of_X`(3934) は不変。
  **次 iter**: 計画(1) = `dadeOrthonormalCharacterImageFamily` の差分化 edit に着手 (まず DadeChainStep/retarget の
  hχsupp 使用箇所も精読して signature 連鎖を確定してから編集、build-green 維持)。

## 🛑 LOOP STOPPED (2026-06-03 iter2, anti-scaffold gate) — spec の前提が誤り、attended 必要

**結論**: この goal の前提（「X-path の engine fix = `coherentEqualDegree_fromDade` の差分-support 弱化を mirror」）
は**誤り**だった。X-path は `coherentEqualDegree_fromDade` を**通らない**。経路は
`peterfalvi_66_coherence_of_X_from_dade` → `DadeChainStep.advance` → `retarget_isCoherent_fromDade` (4946)
→ `retarget_isCoherent_of_sharedDecomposition` (3430) → **`decompositionPair` (1101)** → `ofProjection` (1049)。

**真の blocker (support 弱化では解決不能)**: `decompositionPair` (S07:1101) が
**`htau1_mem0 : tau1 (χ - 0) ∈ ZIrr G` (1109)** を要求。`χ − 0 = χ` ゆえこれは **τχ ∈ ZIrr G**。
X-member `χ = Ind_H^L θ` は χ(1)=|W₁|θ(1)≠0 で **unsupported**、τ=dadeIntegralCharacterMap は off-support で
**任意延長**ゆえ **τχ ∈ ZIrr は証明不能**。⟹ `decompositionPair`/`retarget_isCoherent_fromDade`/`DadeChainStep`
は X-family で**呼び出し不能**。個別 support fields (hχsupp 等) は二次的症状にすぎず、**htau1_mem0 が一次 blocker**。
(対照: Y-path の `coherentEqualDegree_fromDade` は χ_j−χ_0=1 で消える真の差分のみ使い、個別 χ を χ−0 で分解しないので
この問題が無い。だから T6 Y-family は差分-support 弱化だけで通った。両者は parallel でない。)

**監査 §G-A の sharpening**: 「support 仮説を差分形に弱化」では不十分。真の修正 =
**`decompositionPair`/`ofProjection` を restructure して ψ=0 (χ−0) 成分が τχ∈ZIrr を要求しないようにする**。
Agent2 監査の主張「χ−0 分解 (D₀=`.1`) の出力 X/Y/coeff は `retarget_isCoherent_of_sharedDecomposition` で
never read (使うのは `.2` = supported 差分 χ−a•χ₁ 由来)」が正なら、htau1_mem0 を drop / supported 差分へ置換できる。
**要検証**: `decompositionPair` (1101) の `.1`/`.2` 消費を `retarget_isCoherent_of_sharedDecomposition` (3430,
特に 3461-3481) で精査し、`.1` が本当に未使用かを確認。真なら htau1_mem0 を除去/置換 + `ofProjection` を supported
差分専用に。これは **core 分解フレームワーク (decompositionPair 1101 / ofProjection 1049 / sharedDecomposition 3430
+ 全 consumer) を触る intricate surgery** で、**下流多数を壊しうる**。

**なぜ STOP したか (anti-scaffold)**: 無人自走で core フレームワークを restructure すると (a) flail (τχ∈ZIrr を
証明しようとして無限ループ) か (b) scaffold (htau1_mem0 を vacuous に弱める/誤 restructure で consumer を壊す) の
リスクが高い。本セッションで一日戦ってきた scaffolding 罠そのもの。⟹ **gate 通り STOP**。コード変更なし、
build green 維持 (3562)、新 sorry 無し。

**attended セッションでの推奨手順**: (1) `decompositionPair`(1101)+`ofProjection`(1049)+
`retarget_isCoherent_of_sharedDecomposition`(3430) を精読し `.1`(χ−0) 出力の消費を確定。(2) `.1` 未使用なら
htau1_mem0 を除去 (or supported 差分へ)、要 `ofProjection` 一般化。(3) `DadeChainStep`/`retarget_isCoherent_fromDade`
の support fields を差分形に弱化 (この部分は iter1 設計済の `dadeOrthonormalCharacterImageFamily` 差分-span 化も含む)。
(4) `peterfalvi_66_coherence_of_X_from_dade` が実 induced family で instantiate 可能になることを確認。各 step build-green。
