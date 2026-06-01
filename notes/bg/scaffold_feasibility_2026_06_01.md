# BG §5/§7–§16 + App C/D/E — scaffold feasibility 調査 (2026-06-01)

**目的**: 各 BG section の Lean 雛形化 (= 定義は filled-in な real def、定理は faithful な statement + `sorry`、**true-stub 不可**) の実現可能性を per-section で評価。
**方法**: 章ごと 5 並列エージェントで notes + mmd + 既存 Lean infra を精査。
**出典統合元**: `_overview.md`, `s05_*`,`s07_*`…`s16_*`, `appC/D/E_*`, `references/bg/local-analysis.mmd`, 既存 `OddOrder/`.

---

## 核心発見 — 「各 section 独立に雛形化」は faithful には不可

§7 で **固定最小反例 G** を本書全体で fix し (mmd L2133)、§8–§16 は次の **FT-foundation 定義の塔**の上に建つ:

```
§7  : 固定 G + ℳ(maximal族) + 𝒰(uniqueness) + ℋ_H(A;π)/ℋ* + Hypothesis 7.1
§10 : σ(M)/α(M)/β(M) + M_σ/M_α/M_β  (+ ideal prime, F_σ(M))
§12 : τ₁/τ₂/τ₃(M) + 部分群 E + E₁/E₂/E₃
§13 : ActsPrimeOn / ActsRegularlyOn
§14 : κ(M) + type 𝒫 (ℳ_𝒫/ℳ_𝒫₁/ℳ_𝒫₂/ℳ_ℱ) + σ-decomposition + R(x)/M̃
§15 : M_F (nilpotent normal Hall)
§16 : Z/Ẑ/A(M)/A₀(M)/π* + Type I–V + Thm A–E/I/II
```

**これらは Lean に一切存在しない** (BG frontier は §4)。§8–§16 の全 numbered result は hypothesis か conclusion でこれらを参照する。したがって §8–§16 を独立ファイルとして今書こうとすると、`M_σ` 等を自由変数で axiomatize するしかなく、memory `scaffold-sorry-free-not-done` が警告する **「hard content を未充足仮説に hoist する」 anti-pattern** に陥る (= sorry-free に見えても faithful でない)。

**faithful な道筋 = foundation-first**: foundation 定義を先に埋める (=「埋められる定義を埋める」) → dependency 順に statement を sorry 化。

---

## per-section feasibility 一覧

Tier: **A** = 今すぐ faithful に書ける (参照対象が既存) / **B** = その section 自身の新 def を埋めれば書ける / **C** = 他の未構築 section の対象に依存 (または encoding が未解決)。
「結果数」は **エージェントが mmd で実測した正しい数** (既存 notes は大幅 undercount、下記データ品質参照)。

| § | 題 | 結果数 | Tier 内訳 | 今すぐ section file? | 主ブロッカー |
|---|---|---|---|---|---|
| **5** | Narrow p-Groups | 7 | A~2, C~5 | **YES** | def infra は `NarrowPGroup.lean` に完成済。proof は §4 capstone (Lem 4.5c-nonab/4.14/4.16/4.17/4.18) 待ち。statement は今 faithful に書ける |
| **7** | Transitivity | 6 | B×6 | foundation 後 | ℳ/𝒰/ℋ*/Hyp7.1 を埋めれば 6 statement writable。encoding open 無し |
| **8** | Fitting of Maximal | 2 | (B once §7) | foundation 後 | 新 def 無し。§7 def + 固定 G で writable。helper `fittingInG` |
| **9** | Uniqueness | 6 | (B once §7) | foundation 後 | 新 def 無し。**最も scaffold-ready** (短い linear chain 9.1→9.6) |
| **10** | M_α/M_σ | **14** | C×14 | §7 後 | σ/α/β/M_σ を**この節で定義**。`oPiCore`+`fitting` で組める |
| **11** | Exceptional Maximal | **7** | C×7 | §7+§10 後 | Hyp 11.1 bundle。§10 の M_σ/σ に全依存 |
| **12** | Subgroup E | **19** | C×19 | §7+§10 後 | E/τ_i を**この節で定義**。最大。3分割推奨 |
| **13** | Prime Action | **13** | A:2def, C×13 | 一部今 | `ActsPrimeOn`/`ActsRegularlyOn` def は今書ける。13 定理は §10/§12 後 |
| **14** | Type 𝒫 Counting | **13** | A:1, B:5def, C×13 | §10–§13 後 | `conjClassSet` のみ今。type-𝒫/κ/R(x) を定義 |
| **15** | M_F | 9 | A:1def, C×9 | §10–§14 後 | `MFitting` def のみ今 (sSup of nilpotent normal Hall) |
| **16** | Main Results (apex) | 8 | C×8 | §10–§15 後 | Thm A/B/C/D/I/II + Prop16.1 + Type I–V。Peterfalvi §10 と共設計 |
| **A.C** | Final Contradiction | 4 | C×4 | **cross-ref 推奨** | Peterfalvi §9 と同役割の有限体双対。**再述せず** §9 への docstring cross-ref |
| **A.D** | CN-Groups | 2 | B:1def, C×2 | **SKIP 推奨** | critical path 外 + Gorenstein 3-step group 必要 |
| **A.E** | Further Results | 5 | B:2, C×3 | E.1/E.2 のみ | critical path 外。P.Hall collection E.1/E.2 は今 writable (mathlib backed) |

---

## 今すぐ埋められる共有 foundation 定義 (open problem 無し、encodable now)

新規 `OddOrder/GroupTheory/` モジュール (§7–§16 横断で再利用):

| 定義 | 内容 | 置き場所 | 備考 |
|---|---|---|---|
| `maximalSubgroups` (ℳ), `maximalSubgroupsContaining` (ℳ(H)), `IsUniquelyMaximal` (𝒰) | maximal 族 / uniqueness | new `MaximalSubgroup.lean` | mathlib `IsCoatom` 利用 (Isaacs Ch07 で実績) |
| `hInvariant` (ℋ_H(A;π)), `hInvariantStar` (ℋ*) | A-不変 π-subgroup と極大 | new `AInvariantPiSubgroups.lean` | `Subgroup.IsPiGroup` 再利用 |
| `elemAbOfRank` (ℰ_p^n), ℰ* helper | rank 指定 elem-ab 族 | extend `ElementaryAbelian.lean` | `IsMaximalElementaryAbelian` 既存 |
| `conjClassSet` (𝒞_G(T)) | conjugacy 閉包 | new or `TISubset.lean` | §14/§15/§16 で再利用 |
| p-length-one predicate | `H/O_{p',p}(H)` が p'-群 | new `PLength.lean` | `oPiPrimePiCore` + quotient |
| Z-group predicate | 全 Sylow cyclic | new `ZGroup.lean` | §10 Lem 10.4 |
| regular-action predicate | `∀α∈A#, C_R(α)=1` | `CoprimeAction.lean` | mathlib `MonoidHom.FixedPointFree` 既存 |
| **固定 G setup** | minimal FT counterexample bundle | new `BG/Ch2_Uniqueness/Setup.lean` or class | **keystone**。simple/odd/proper-solvable/minimality |

**既存で再利用できるもの (新規不要)**: `fitting G` = F(G) (`Isaacs.Ch01`, **単体 Fitting あり**), `oPiCore π G` = O_π, `oPiPrimePiCore` = O_{π',π}, `pRank`/`rank` (BG `m`/`r`), `IsSCN₃`, `IsElementaryAbelian`, `IsNarrow`, `IsExtraspecial`+`IsCentralProduct`, `Omega`, `IsTISubset`, `IsFrobeniusGroup`, Hall (Isaacs). **BG `m(Z(A))≥3` = `3 ≤ pRank (Subgroup.center A) p`**。

---

## データ品質の問題 (要 backfill into per-section notes)

- **結果数 undercount**: §10 既存note"6"→実 **14**, §11 "4"→**7**, §12 "15"→**19**, §13 "7"→**13**。
- **§10 Lem 10.3/10.4/10.5/10.12/10.13** は mmd `MISSING_PAGE_FAIL` 内。Agent が PDF text layer から statement 回収済 (s10 note へ反映要)。
- **§12 Lem 12.1(g)** は `A∈ℰ_p²(M) ⇒ A∈ℰ_p*(G)∧p∉β(G)` (= 下流多用)。既存 note は (f) の `C_{E₃}(E)=1` と取り違え。mmd 準拠。
- **§13 Lem 13.10/13.11** は Nougat が conclusion bullet を欠落 (mmd L3672/L3696)。PDF p.116 から再構成要 (proof から (a)(b)(c)(d) 推定可)。
- **§14 Lem 14.6** = `MISSING_PAGE_EMPTY:123`; **§16 Thm A–D の proof + Thm D statement 末尾** = `MISSING_PAGE_EMPTY:139,140`。statement 本体 (Thm A/B/C, Type I–V, Prop16.1, Thm I/II) は mmd に在り、scaffold には影響なし。proof 段階で PDF 要。
- **App.C**: Peterfalvi §9 header (`S09_NonexistenceCertain.lean` L49–63) の監査が正; Thm C (`p≤q`) は §9 (7.11) と**別 statement** (双対だが literally 等価でない)。既存 `appC` note (案A) は古い。

---

## 推奨実行計画 (phased, foundation-first)

- **Phase 0 (今すぐ・独立)**: `S05_NarrowPGroups.lean` (7 結果 faithful sorry, 1–2 close) + App.E E.1/E.2 + per-section notes の結果数/欠落修正。
- **Phase 1 (foundation = keystone)**: 上記共有 module 群 + 固定 G setup。→ これで §7/§8/§9 が unlock。
- **Phase 2 (Ch2)**: §7(6)+§8(2)+§9(6) = 14 statement。§9 から着手が楽。
- **Phase 3 (Ch3)**: §10 定義+14 → §11(7) → §12(19, 3分割) ∥ §13(2def+13)。
- **Phase 4 (Ch4 apex)**: §14(13) → §15(9) → §16(8, Peterfalvi §10 共設計)。
- **App**: A.C = §9 cross-ref (Phase 2b 同期) / A.D = skip / A.E = low priority。

各 phase は build-green を維持 (`lake build OddOrder` + AxiomsCheck)。深い未構築 section は **`-- TODO (BG N.N): <blocker>`** で traceability 保持 (true-stub も hoist もしない)。

---

*作成: 2026-06-01。5並列調査エージェント (Ch2/Ch3a/Ch3b/Ch4/§5+App) 統合。詳細 per-result inventory は各 agent 出力 (本 session transcript) 参照。*
