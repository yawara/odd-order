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
| 5 | **Prop 4.3(a)(b)** cl≤3/p>3 collection | — | ⚠ γ₄=1 + f/g mathlib convention 再計算要 | ⏸ **BLOCKED_DESIGN** (full は1ショット intractable; 詳細 skeleton を `notes/bg/s04_prop43_design_2026_05_31.md` に保存)。**将来 GATE-1 (4.4)collection を単独 workflow 化**。cl≤2 部分は wrapper 気味で見送り |
| 6a | **Prop 4.8(a)** r≤2+exp p ⇒ \|R\|≤p³ | `card_le_prime_cube_of_pRank_le_two_of_exponent_prime` | I-0d✅ + SCN✅ + Prop4.4(a)✅ | ✅**PASS** (commit 73df7e1, S04 §4D, 独立監査済)。SCN+GL counting, Ch07 import 回避 |
| 5b | **Prop 4.3 GATE-1 (4.4) collection** | `mul_pow_eq_collect_of_triple_central` | precursor S04:378 + Lem4.2 + γ₄=1 | ✅**PASS** (commit 3190008, S04 §Prop43ClassThreeCollection, 独立監査済)。FF n=C(n+1,3), GG n=2·C(n+1,3) を BCH モデルで確定 (design note 訂正済)。⚠ agent が branch 切ったので main に ff-merge 済 |
| 5c | **Prop 4.3 (a)(b)** Ω₁ exp p / φ=x^p hom | `omega1_pow_eq_one` (a) + `pow_mul_eq_mul_pow_of_commutator_le_omega1` (b) | **collection 5b✅** で assemble 可。GATE-2(b)=collection\|n=p+divisibility (tractable), GATE-3(a)=\|R\|-induction+Ω₁closure (やや重)。skeleton = s04_prop43_design GATE-2/3 | **IN PROGRESS** (collection 後の本命; #6b Prop4.8(b)→#7 Lem4.9→#8 Prop4.11 を開く) |
| 5c | **Prop 4.3 (a)(b)** Ω₁ exp p / φ=x^p hom | `omega1_pow_eq_one` + `pow_mul_eq_mul_pow_of_commutator_le_omega1` | collection 5b✅ | ✅**PASS** (commit 03a40d7, S04 §Prop43ClassThree, 独立監査済, main直)。(a)=\|R\|-induction product-closure, (b)=collection\|n=p。hR追加は忠実 |
| 6b | **Prop 4.8(b)** p>3⇒Ω₁(R) exp 1/p | `omega1_pow_eq_one_of_pRank_le_two_of_three_lt` | Prop4.3(a)✅+Prop4.8(a)✅ | ✅**PASS** (commit 07024dc, S04 §Prop48ExponentP, 独立監査済, main直)。helper F1(\|G\|≤p^(j+1)⇒class≤j) + F2(cl≤3⇒γ₃central)。**Prop4.8 完全** |
| 7 | **Lem 4.9** \|Ω₁(R)\|≤p²⇒\|Ω₁(R/T)\|≤p² ∀T◁R | — | **Prop4.8✅(a+b) + Prop4.3(b)✅ (pow_mul_eq_mul_pow_…) + Lem4.5b✅**。二重 minimal-counterexample (R,T): \|T\|=p に帰着→r(R/T) 場合分け→\|R\|=p⁴,R/T exp p→φ=x^p hom (Prop4.3b)→ker φ=Ω₁(R)→p≥p² 矛盾 | **IN PROGRESS** (Prop4.11 の必須gate, hard) |
| 7 | **Lem 4.9** \|Ω₁(R)\|≤p²⇒\|Ω₁(R/T)\|≤p² ∀T◁R | `card_omega1_quotient_le_prime_sq` | Prop4.8✅+Prop4.3(b)✅+Lem4.5✅ | ✅**PASS** (commit c721aad, S04, +458行, 独立監査済, main直)。二重 minimal-CE + Fact F |
| 8 | **Prop 4.11 (Huppert)** p>3,\|Ω₁\|≤p²⇒metacyclic | `isMetacyclic_of_omega1_card_le_prime_sq` | **Lem4.9✅ + agemo✅ + Lem4.5(b)✅ + Lem4.2✅ + Lem4.1✅**。design §3 に full skeleton (8 step)。逐次分解で landing 中 | ✅ **PASS** (`0ed392e` `isMetacyclic_of_omega1_card_le_prime_sq`, 独立監査済: build green 3362 / axiom-clean / faithful 追加仮説0)。逐次分解 base(f637e7f)+(4.7)lift(be039f2)+step8(630cd73)+main(0ed392e), 新 private helper 4個含む。**§4第2の山, Thm4.16 CaseA を開く** |
| 9 | **Lem 4.13/4.14** q∣\|Aut R\|⇒q∣p²-1, q<p | `dvd_prime_sq_sub_one_and_lt_of_scn3_empty` | **2 precursor 欠落** (= G Thm4.15) | ⏸ **BLOCKED_DESIGN** (#9 run wf_aa5d5280-3ff が精密 map)。設計note「gate=GL橋のみ」は誤り — Lem4.13=G Thm4.15(ii) は (i)=**precursor(1) `pRank_le_two_of_scn3_empty`** (SCN₃=∅⇒pRank≤2, §5/§7 共有ゲート) と **precursor(2)** (minimal ψ-inv⇒special exp p=G Thm3.7/3.10) を消費。底辺補題は present (3.9(i)/3.12/1.3.4/GL橋)。**ロードマップ = `notes/bg/s04_lem413_gorenstein_precursors.md`**。実装順: G Lem4.12+4.13(小)→Lemma4.14(大engine)→Thm4.15(i)→precursor(1)→precursor(2)→BG Lem4.13/4.14→Thm4.16 |
| 8.5 | **G Lem 4.12 + 4.13** (Lemma4.14 前提, 新規小) | INLINE in S04d | gate無 | ✅ **PASS** (commits e0378e9 INLINE-1 Lem4.12 / 34f04fb INLINE-2 Lem4.13, `S04d_GorThm415.lean` inline, sorry-free) |
| 8.6 | **G Lemma 4.14** Ω₁(C_P(Ω₁(A)))=Ω₁(A) | `omega1_centralizer_omega1_eq_omega1_of_maximal_rank` | gate: 8.5✅ + 3.9(i)✅/3.12✅/1.3.4✅ | ✅ **PASS** (commit 17d0c0e, @S04d:857, sorry-free, 独立検証済 — S04d 全体 sorry-free) |
| 8.7 | **precursor(1)** `pRank_le_two_of_scn3_empty` (=G Thm4.15(i)) | `pRank_le_two_of_scn3_empty` | gate: 8.6✅ + GL橋✅ | ✅ **PASS** (2026-05-31 直接証明, commit c1d23e8, S04d, sorry-free / **AxiomsCheck axiom-clean**): translation half + companions@SCN + GL-squeeze kernel@PRank + G Thm4.15(i) 本体 assembly (`pRank_le_two_of_normalAbelian_pRank_le_two`, Lemma4.14 + conjNormal index + rank arithmetic) すべて着地。**§5 と Thm 4.16 の gate が開いた**。詳細 issue 0051 |
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
