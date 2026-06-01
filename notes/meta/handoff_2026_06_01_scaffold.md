# 引き継ぎ: BG + Peterfalvi scaffold (2026-06-01)

> **次セッションはここから開始**。現在地・継続タスク・確立した workflow / encoding tips をまとめる。
> 横断スナップショット = memory `ft-master-roadmap`。BG 計画 = `notes/bg/scaffold_feasibility_2026_06_01.md`。
> Peterfalvi 計画 = `notes/peterfalvi/scaffold_feasibility_2026_06_01.md` (本セッション末に workflow で生成)。

## ✅✅ 更新 (2026-06-01 後半): scaffold **全完了** (build-green)

下記「継続タスク」は**すべて landed**。現 HEAD で `lake build OddOrder` green (3410 jobs)、AxiomsCheck 不変。
- **BG**: §12=19/19 (2708462/a519a4d), §13 (S13_PrimeAction, 11結果+2def; 13.10(c)/13.11 結論を PDF 画像読みで復元→mmd splice 705dd47), Ch4 §14/§15/§16 (S14_TypePCounting/S15_MF/S16_MainResults, **faithful 実 statement**, §16 に BG↔Pf Type 対応), App.C/D/E。
- **共有 module**: `GroupTheory/MaxNilpotentNormalHall` (M_F) + `GroupTheory/MaximalSubgroupType` (Type I–V 塔, **完全 faithful**)。
- **Peterfalvi** §10–§16 (S10–S16) + Appendices (Suzuki/Huppert/NearFields/FeitSibley/Suzuki2Groups)。§15 で ω/η/μ/ν を実型 field 化。
- **最上位** `OddOrder/FeitThompson.lean` (`feitThompson` sorry + honest final-contradiction bridge)。
- **design**: 群論=faithful 実構造、文字理論の恒等式のみ opaque `_formula:Prop` placeholder (217箇所; gate#3 ω/η/μ/ν 未材料化; sorry 化済で laundering 無)。convention = `notes/meta/scaffold_opaque_prop_convention.md`。
- **フォローアップ**: opaque `_formula` rider 含む定理結論は部分 vacuous; `GroupTheory.derivedInAmbient`/`piCoreIn` が `Ch2.S07.derivedInG`/`opiCoreInG` と重複 (issue 登録済) → proof フェーズで統一。
- **次フェーズ = proof 充填** (本線 §4 Lem 4.13 → §16 → Pf §8/§9)。

---

## このセッションでやったこと (全 push 済 origin/main = fd99137)

**方針**: 教科書の定理を **faithful な Lean statement + `sorry`** で scaffold (true-stub 不可)、定義は埋める、
**foundation-first** (固定 G / ℳ / 𝒰 等の共有定義を先に作り、dependency 順に statement 化)。
各 section は `lake build OddOrder` green + 単位 commit。

### 完成済 (build-green, faithful, axiom 増無し)
- **foundation 7 module** (`OddOrder/GroupTheory/`):
  - `MaximalSubgroup` = ℳ `maximalSubgroups` / ℳ(H) `maximalSubgroupsContaining` / 𝒰 `IsUniquelyMaximal`
  - `AInvariantPiSubgroups` = ℋ_H(A;π) `hInvariant` / ℋ* `hInvariantStar`
  - `ConjClassSet` = 𝒞_G(T) `conjClassSet`; `ElementaryAbelianFamily` = ℰ_p^n `elemAbelianOfRank`
  - `ZGroup` = `IsZGroup` (全 Sylow cyclic)
  - `OddOrder.BG.IsMinimalSimpleOdd G` (`BG/Ch2_Uniqueness/Setup.lean`): 固定最小単純奇数反例 G の structure
  - `BG/Ch1_Preliminary/PLength.lean` = `hasPLengthOne`
- **BG §5** (`S05_NarrowPGroups`): 7/7 faithful (5.1(a) `scn3_nonempty_of_three_le_pRank` のみ proved・axiom-clean)
- **BG Ch2 §7/§8/§9** 完成 (15 statement): §7 Hypothesis71 + Transitivity 6, §8 Fitting 2, §9 Uniqueness 6+系
- **BG Ch3 §10** (`S10_MalphaMsigma`): **13/14** (定義層 idealPrime/σ/α/β/M_σ/M_α/M_β/F_σ + 10.1–10.12,10.14; 10.13 のみ TODO)
- **BG Ch3 §11** (`S11_ExceptionalMaximal`): **7/7** (Hypothesis111 + 11.1–11.7)
- **BG Ch3 §12** (`S12_E`): **9/19** (定義層 τ₁/τ₂/τ₃ + SubgroupESetup + 12.1/12.2(a)/12.3/12.4(a)/12.13/12.14/12.16(a)/12.17/12.19)

## BG 継続タスク (foundation-first 確立済、rhythm に乗せるだけ)
1. **§12 残り 10** (`S12_E.lean` に追記): 12.5(Thm a-f)/12.6(Cor a-f)/12.7(Thm a-e, F(M)=M_σ×A₀)/12.8(Lem a-f)/
   12.9(Cor)/12.10(Cor a-e)/12.11(Lem)/12.12(Thm, Frobenius)/12.15(Prop a-d)/12.18(Lem a-b)。多部分・intricate
   → clean core を faithful に + fragile sub-clause は docstring で defer。
2. **§13** (`Ch3_MaximalSubgroups/S13_PrimeAction.lean`, 13 結果): `ActsPrimeOn`/`ActsRegularlyOn` 2 def (今書ける)
   + 13.1–13.13。**13.10/13.11 は Nougat が conclusion 欠落** → PDF p.116 から再構成要。
3. **Ch4** (`Ch4_FamilyOfMaximal/`): §14 type-𝒫/counting (13) → §15 M_F (9) → §16 apex Thm A–E/I/II + Prop16.1 (8)。
   §16 の **Type I–V** は Peterfalvi §10–§16 と共有モジュール化を検討 (下記)。
4. **App** C (= Peterfalvi §9 への docstring cross-ref) / D (skip) / E (E.1/E.2 のみ)。

## Peterfalvi scaffold (次セッションの新規対象)
- **§1–§9 は Lean 化済** (`OddOrder/Peterfalvi/S01–S09`; §1–§7 sorry-free, §8/§9 = 既知 2 sorry)。**§10–§16 は Lean ファイル無し = scaffold 対象**。
- §10–§16 = 最小単純群 G の構造 (§10) + 極大部分群 type II/III/IV/V (§11–§14) + 部分群 S,T (§15) + G の非存在 (§16)。
  **BG Thm A–E を入力**とし、固定 G は **`OddOrder.BG.IsMinimalSimpleOdd` と同一** (= 共有/再利用)。BG §7–§16 と完全に並行する scaffold タスク。
- **詳細計画 = `notes/peterfalvi/scaffold_feasibility_2026_06_01.md`** (workflow `peterfalvi-scaffold-survey` で生成済、per-section 定義/結果/Tier A-C/BG 依存)。要点:
  - **~60 results 中 ~47 が Tier C** (apex 指標算術 + type 分類 + 最終矛盾)。**foundation-first 必須**。
  - **4 つの global gate**: (1) **§10 Type 分類塔** (`IsTypeF/I/P/II/III/IV/V` + Ms + A₁/A/A₀) = 唯一の「今すぐ高価値」ファイル、§11–§16 の全 hypothesis が参照; (2) **`M_F`** (極大 nilpotent normal Hall) = **BG §15 と同一対象** → 共有 module 化 (`fittingInG` は別物!); (3) **指標 index 族 `ω/η/μ/ν`** (S03/S04 に未材料化) → §13/§15/§16 の norm-cascade をブロック; (4) **BG Thm A–E + App.C が未 scaffold** → §10 構造定理 (8.8/8.11–8.13) と §16 最終矛盾の proof をブロック。
  - **今すぐ Tier A で書ける standalone 数論補題**: (11.1) `p^q>4q²+1` / (13.14) cyclotomic / (14.8a) `q^{p+1}>p^{q+1}` / (9.1) Wielandt — proof も可能。
  - **再利用確定**: `OddOrder.BG.IsMinimalSimpleOdd G` (= Pf §10 の固定 G と同一、再定義不可)、`Peterfalvi.S05.TICyclicHypothesis` の設計 (type 𝒫 の V-normalizer 条件)、GroupTheory foundation 一式。
- **共有 module 化**: (a) `M_F` → new `GroupTheory/MaxNilpotentNormalHall.lean` (BG §15 + Pf §10 横断); (b) **Type I–V 述語** → new `GroupTheory/MaximalSubgroupType.lean` (BG §16 と Pf 同一分類)。BG Ch4 §14–16 と Pf §10–16 を**同 wave で設計**。

## 次セッションで workflow を高速 scaffold に使う方針
逐次 build-fix-commit がボトルネックなので、**worktree 分離した並列 scaffold** が有効:
- **Phase 1 (investigate, 並列)**: 既に BG/Peterfalvi の plan note があるので skip 可 (or 残部の精査)。
- **Phase 2 (parallel scaffold)**: section ごとに 1 agent を `isolation: 'worktree'` で起動し、各 agent が
  「plan note の該当 section を読む → faithful statement + sorry の Lean ファイルを書く → `lake build <module>` で green 化 → 返す」。
  worktree 分離で並列ファイル書き込みが衝突しない。
- **Phase 3 (merge, 逐次)**: 各 worktree の section ファイルを main に取り込み → root 配線 → `lake build OddOrder` green → 単位 commit。
- 注意: agent は plan note を spec とし、**確立済の encoding tips (下記) を厳守**。statement のみ (proof は sorry) なので
  各ファイルの build は速い (import + 型チェックのみ)。section 間の依存 (Pf §11 が §10 定義に依存) は wave 分け。

## 確立した encoding tips (BG scaffold で判明、Pf でも同じ)
- 固定 G は `(hG : IsMinimalSimpleOdd G)` を各定理に明示 thread (Peterfalvi Hypothesis 流儀; structure ↔ バラ変換は 1 行 wrapper, lock-in 無し)。
- **`Subgroup.normalizer` は `Set G` を取る** → Sylow 等の二重 coe には `(... : Set G)` 明示が必須 (carrier 推論失敗の頻出原因)。
- 共役 `M^g` = `MulAut.conj g • M` (`open scoped Pointwise`)。部分群の集合上の推移性は `ConjTransitiveOn` 風 (`∃ k∈K, conj k • Q₁ = Q₂`)。
- Hall = `OddOrder.Isaacs.Ch03.IsHallSubgroup`; normal p-complement = `OddOrder.Isaacs.Ch05.HasNormalPComplement`;
  π-subgroup = `Subgroup.IsPiSubgroup` (`GroupTheory.OpResidual`); Z-group = `GroupTheory.IsZGroup`。
- O_π(H) を G 内に = `OddOrder.BG.Ch2.S07.opiCoreInG π H`; F(M) を G 内に = `OddOrder.BG.Ch2.S08.fittingInG M`; M' = `Ch2.S07.derivedInG M`。
- M_σ/σ 等 = `OddOrder.BG.Ch3.S10.{Msigma,Malpha,Mbeta,sigma,alpha,beta,idealPrime}`。
- **商型 (G/N) の rank/nilpotent は Normal instance 不足で脆い** → 該当 sub-clause は docstring で defer。
  正規化子の積分解・「centralizes a Sylow」は **要素形 / ∃ 形**で書く (Set 積 coercion は脆い)。
- 別 namespace の参照: `OddOrder.BG.Ch3.SNN` から `OddOrder.BG.Ch2.S07.foo` は `Ch2.S07.foo` で解決 (sibling chapter は full prefix から)。
- 深い入れ子 (Ω₁(Z(P)), 内部直積 A₀×Z, 推移性) は clean に書けない → `-- TODO (Ref N.N): <blocker>` で documented (true-stub も hoist も不可、memory `scaffold-sorry-free-not-done` 準拠)。
- 各結果は **statement の faithful 性最優先**。多部分定理は clean core を述べ fragile part を defer (partial でも honest)。

## やらないこと / 注意
- push は指示時のみ (本セッション末で fd99137 まで push 済)。
- proof は全部 `sorry` (scaffold 目的)。proof を埋めるのは別フェーズ (BG §4 capstone / §16 / Pf §8-9 sorry が先行依存)。
- `lake build OddOrder` を各 section 配線後に green 確認。AxiomsCheck には proved 結果のみ追加 (sorry 物は不可)。
