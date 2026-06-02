# 自走 goal: (6.8) engine support-interface 修正 (§G-A) — 2026-06-03 overnight

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
