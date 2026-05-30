# BG 自走証明キュー (2026-05-31〜, workflow bg-prove 駆動)

> ユーザー指示 (2026-05-31 夜): 「workflow で進めて。直近が終わっても**できるだけ長く自走**し続けて
> BG の定理を証明し続けて」。main loop が `bg-prove` workflow を 1 ターゲットずつ起動 → 完了通知で
> 再起動 → 監査して commit維持/revert → 次ターゲット launch、を繰り返す。
>
> **workflow**: `.claude/workflows/bg-prove.js` (scriptPath で起動)。args にターゲット仕様を渡す。
> 返り status: `PASS` (緑+verify合格→commit維持), `VERIFY_FAILED` (commit を `git reset --hard HEAD~1` で revert),
> `BLOCKED_DESIGN`/`BLOCKED_IMPL` (着手不可/未達, ツリーは緑のまま→skip して次へ)。
>
> **main loop の各ターン手順**:
> 1. 直前 workflow の返り値を読む。PASS なら issue 0051 / 該当 notes を更新 (必要なら)。VERIFY_FAILED なら revert。
> 2. `git status` 緑確認 (念のため `lake build OddOrder` は workflow 内で確認済)。
> 3. 下記キューの次の未完ターゲットを選び `bg-prove` を launch。
> 4. ターン終了。完了通知で 1 に戻る。
> 5. キューが尽きる/全 BLOCKED なら、新たな BG ターゲット (§5, §7…) を mmd から発掘してキュー追記。

## ターゲットキュー (依存順 / 優先順)

| # | ターゲット | decl 候補 | 依存 (✅=ready) | 状態 |
|---|---|---|---|---|
| 1 | **Thm 4.12(a)** metacyclic+[R,A]=R⇒abelian | `OddOrder.BG.Ch1.S04b.isMulCommutative_of_metacyclic_actionCommutator_eq_top` | a-2✅ N-4✅ Lem4.10✅ LEAF-4✅ LEAF-1✅ Lem4.1✅ | ✅**PASS** (commit 034d4c4, S04b_Thm412.lean, 独立監査済: build green 3360 / axiom-clean / 署名一致) |
| 2 | **Thm 4.12(b)(c)** T∩C=1, T/C cyclic, R'⊆T | `actionCommutator_inf_fixedPoints_eq_bot` (b) + `actionCommutator_isCyclic_and_fixedPoints_isCyclic_and_commutator_le` (c) + `IsMetacyclic.subgroup` | (a)✅ Prop1.6(a)(d)✅ Lem4.10✅ LEAF-4✅ | ✅**PASS (忠実版)** (commits 8e8240e/09192d2/2a18823, 独立監査済 build green/axiom-clean)。⚠ 目標署名(c)は偽 (Nougat が "1⊂T⊂R" を欠落) → workflow が検出し `hT_ne_bot/hT_ne_top` 付き忠実版を着地 (status=BLOCKED_IMPL だったが genuine 成功)。**BG Thm 4.12 (a)(b)(c) 完全形式化完了** |
| 3 | **I-0d GL橋** Aut(Eₚⁿ)≅GL(n,p) | `IsElementaryAbelian.mulAutEquivGeneralLinearGroup` + `card_mulAut` | gate無 | ✅**PASS** (commit bba6410, PRank.lean に4 decl, 独立監査済) |
| 4 | **Lem 4.15** extraspecial S, [S,R]⊆S'⇒R=S·C_R(S) | `mul_centralizer_eq_top_of_isExtraspecial` | Gorenstein 5.4.6 | ✅**PASS** (commit 3f7f99d, S04 §4E, 独立監査済)。構造定理回避: 変位準同型 δ_g:S→Z(S) の 𝔽_p 線形化 + 基底埋込 squeeze (genuine counting) |
| 5 | **Prop 4.3(a)(b)** cl≤3/p>3 collection | — | ⚠ γ₄=1 + BG f/g exponent が mathlib convention で誤 → **mirror で f/g 再計算要**。precursor `commutatorElement_pow_left_of_triple_central`@S04 あり | **IN PROGRESS** (root gate: #6,#7,#8 を開く, risk大)。block時 pivot→§1 0015 banking |
| 6 | **Prop 4.8** r≤2+exp p⇒\|R\|≤p³, p>3⇒Ω₁ exp p | — | gate: #3, #5, Lem4.5b✅ | queued (gate: #3,#5) |
| 7 | **Lem 4.9** \|Ω₁(R/T)\|≤p² | — | gate: #6 | queued (gate: #6) |
| 8 | **Prop 4.11 (Huppert)** p>3,\|Ω₁\|≤p²⇒metacyclic | `isMetacyclic_of_omega1_card_le_prime_sq` | gate: #7 + agemo✅ + Lem4.5b✅ + abelian case | queued (gate: #7) |
| 9 | **Lem 4.13/4.14** q∣\|Aut R\|⇒q∣p²-1, q<p | — | gate: #3 + SCN₃=∅✅ | queued (gate: #3) |
| 10 | **Lem 4.5(c) noncyclic 半** Ω₁(Z₂(R)) noncyclic | — | Gorenstein 5.4.10, Lem4.5(a)general | queued (§5 でも要) |
| 11 | **Thm 4.16 (Blackburn) apex** rank≤2 分類 | `blackburn_rank_two_classification` | gate: #2,#6,#8,#9,#4 + central product API✅ + GL engine✅ | queued (gate多, 最後) |

## §4 後 (§5 以降, 後で発掘して追記)

- §5 Narrow: Lem 5.1(a)=Lem4.7⇐ (Gorenstein 5.4.15), Lem 5.1(b)/5.2/Thm 5.3/Cor 5.4/Thm 5.5-5.7。
  設計 = `notes/bg/s05_design_2026_05_30.md`。§4 完成 + Lem4.7⇐ が gate。
- §7-§16 直列スパイン (§4+§5 完成後)。`notes/meta/ft_master_roadmap_2026_05_29.md`。

## メモ
- 各 PASS 後、issue 0051 (§4) の進捗欄に 1 行追記すると cold-start 引き継ぎが楽 (任意、毎回でなくてよい)。
- 同一ファイルを複数 workflow が触らないよう、1 ターゲット = 1 workflow を**逐次**に (並行起動しない)。
- BLOCKED が続いたら独立ターゲット (#3,#4,#5,#10) に切替えて前進を絶やさない。
