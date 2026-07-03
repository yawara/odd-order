---
id: 9004
slug: hypothesis46-big-v-deviation
title: "Hypothesis46 の V=W−W₂ (big V) 逸脱: 原文(3.1)/(8.10)/Coq は small V — §10 instantiation を阻む"
created: 2026-07-02
---

# Hypothesis46 の V=W−W₂ (big V) 逸脱: 原文(3.1)/(8.10)/Coq は small V — §10 instantiation を阻む

**起票**: lane a (Pf 11.8.3 β real piece 4 の上流調査で発見, 2026-07-02)。
**種別**: shared-infra 設計逸脱の flag + 修正 claim (claim-before-build)。lane a は待たずに
hypothesis-threaded で (11.8.3) を続行する (下記「lane a の並行対応」)。

## 発見 (unsound-carrier 系)

`S06_CertainHypothesis46.lean` の `Hypothesis46` (Pf (4.6) の形式化) が、原文・Coq の (4.6) より
**真に強い** 2 フィールドを持つ:

1. `tic_V : tic.V = ↑W \ ↑W₂` — ambient (3.1) の TI 集合を **big V** (W−W₂) と規定。
   しかし **原文 (3.1) は V = W−(W₁∪W₂) (small V)** で、(4.3.a) が big V の TI 性を主張するのは
   **L 内のみ** (ambient G ではない)。
2. `dade0 : S04.Hypothesis G (A ∪ {l·v·l⁻¹ | l∈L, v∈tic.V}) L` — A₀ = A ∪ **V_big**^L 上の
   Dade 仮説。原文 (4.6.d) の A₀ = A ∪ V^L の V は (3.1) の **small V** (下記証拠)。

### 証拠

- **原文 (3.1)** (04.5 p.15): 「V = W−(W₁∪W₂) is a TI-subset of G with normalizer W」。
- **原文 (8.10)** (04.10 p.46): type P で「A₀(M) = A(M) ∪ V^M」、V は (8.4) の V = W−(W₁∪W₂)。
- **原文 (8.15)** (04.10 **p.48 = mmd MISSING page、PDF 直読で回収**): 「If M is of type P and
  M′=[M,M], then Hypothesis (4.6) holds for L=M, K=M′, A=A(M), **A₀=A₀(M)**, H=M_F or M_s」。
  つまり (4.6.d) の A₀ = (8.10) の A₀(M) = A(M) ∪ V_small^M。
- **Coq** `PFsection3.v:69`: `Definition cyclicTIset & W1 \x W2 = W := W :\: (W1 :|: W2)` (small V)。
  `PFsection4.v:707-716`: `prime_Dade_definition` = 「A0 = A :|: class_support V L」 (V = cyclicTIset =
  small V)、`prime_Dade_hypothesis` の cycTI は G 側も同 V。big V は Coq に存在しない。
- **(4.8) 原文証明の整合**: 「z ∈ L−K ⇒ z ~_L x·W₂ の元」で y=1 (つまり z ~ x ∈ W₁^#) のケースは
  「μ_{ij}−μ_{ik} は W₁ 上で消える ((4.3.c))」で殺す → supp ⊆ A ∪ V_small^L で足りる。
  big V は不要。

### なぜ big V 版は充足不能 (見込み) か

TI-subset V with normalizer W ⇒ ∀v∈V, C_G(v) ⊆ W。x ∈ W₁^# ⊆ V_big に適用すると
**C_G(x) ⊆ W** を要求。だが §10 設定では x ∈ W₁^# の C_G(x) は type II support S 側に伸びる
((8.8)/(9.x): S∩M = W, W₁ ⊆ S')。(8.13.b) の D-control は A₀(M) 内の元のみで、W₁^# ∉ A₀(M)
(位数論法: W₁^# の元は V_small の元 (W₁ 部・W₂ 部とも非自明 = 位数が両素因子を含む) の共役に
なれない; A(M)=(M′)^# とも W₁∩M′=1 で交わらない)。ゆえに tic.V_ti (big V TI in G) を §10 から
討ち取る supply が無い。**Hypothesis46 は一度もインスタンス化されていない** (repo 全 grep で
パラメータ出現のみ) ため、この逸脱はこれまで латент。

## 提案する修正 (lane a が claim、hub 異議あれば差し戻し)

1. `Hypothesis46.tic_V` を `tic.V = ↑W \ (↑W₁ ∪ ↑W₂)` (small V) に変更。
   `dade0`/`tau` の A₀ も自動的に A ∪ V_small^L に縮む (set は tic.V 経由で書かれている)。
2. `ticVdiff` (S06_CertainTypeIsometry:58) は shrink が恒等になる (V_ti を tic から直接継承;
   構造は互換のため残してよい)。tic_V の rw 6 箇所 (Isometry:85/314/386, FourCorner:160/406) は
   small→big 変換をしていたので **単純化** (small=small で id 化)。
3. **実質強化が要るのは support 補題のみ**: `certainType_diff_supp_subset_A0`
   (Isometry:276) の L−K 側で y=1 ケースを「μ-diff が W₁ 上で消える ((4.3.c) 対応の在庫
   `certainType_apply_eq_of_mem_W1` :238 近傍)」で除外する 1 ステップ追加。
   同型の support 障害が S06_CertainTypeCoherence の dade0-support 義務
   (columnSum 差 = ∑ 行差、同じ W₁-vanishing で処理) にも出るが同一パターン。
   FourCorner は α が元々 small-V 支持 (W₁ でも W₂ でも消える) なので無傷。
4. S08 の 14 file は `h46 : Hypothesis46 …` パラメータ経由のみ → 型は不変。内部で A₀ 所属を
   証明している箇所があれば同パターンで修正 (要 grep 精査)。
5. 修正後、**§10 instantiation `Hypothesis.toHypothesis46`** ((8.15)/(10.1) の形式化) が可能になる:
   tic := `typePData_toTICyclicHypothesis` (already small-V, `V = Vdiff` rfl)、
   prTI 部 := `toCertainTypeHypothesis`、H := K (=M′, (10.1) の H=M_s=M′ を採用; A_covers が
   A(M)=(M′)^# で自明化 `typePA_eq_sharpSubgroup_derivedInG`)、
   dade0 := `hyp.dadeData.dade` の台集合照合 (typePA0 は conjClassSet=G-共役だが (8.13.a) 系で
   M-trace 一致; 要精査)、tau := `fullDadeIsometryData hyp.hconj`。

## 進捗 (2026-07-02 lane a)

- [x] **修正 1-4 (Hypothesis46 small-V 化) landed** (commit 1056f3a9): 構造体 tic_V 変更、
  ticVdiff 単純化、`certainType_diff_supp_subset_A0` の y=1 除外強化
  (`certainType_apply_eq_of_mem_W1` + `ClassFunction.conj_eq`、Pf (4.8) 証明の
  「μ-diff vanishes on W₁」に忠実)、FourCorner 2 箇所。S06/S08 含め full build green
  (3m41s) + AxiomsCheck OK。S08 は predicted 通りパラメータ絶縁で無傷。

## 完了 (2026-07-03 lane a) — 全完了条件達成、CLOSE

- [x] **追加発見 2 (typePA0 M-共役化) landed** (4623902b): `conjClassSetIn H T` (= Coq
  `class_support`) を GroupTheory/ConjClassSet に新設し `typePA0 = typePA ∪ conjClassSetIn M
  (typePV)` に修正。fallout: `le_normalizer_typePA` 抽出 (toHypothesis71 系の実需要は easy 方向
  のみ)、`normalizer_typePA_eq` は A(M)=(M')# → N(M') = M (極大性+単純性、hG param 追加) で再証明、
  `muGrid_alpha_support` は (2.1) の共役元 c ∈ M を記録するだけで通過 (予測通り)。
- [x] **(4.6.d) dade0 の台集合を conjClassSetIn に統一** (da38b5f7): §10 instantiation が
  definitional になる下準備 (13 statement 箇所 + 構成 4 箇所の機械的変換)。
- [x] **`Hypothesis.toHypothesis46` landed** (52150245): (8.15)/(10.1) の §10 instantiation。
  dade0/tau は **definitionally** `hyp.dadeData.dade` / `fullDadeIsometryData hyp.hconj`、
  tic_V は rfl、H := K = M'、A_covers は A(M)=(M')# で自明。Hypothesis46 の初インスタンス化。
- [x] **(4.8)/(4.10) aligned-grid 化 + h48/h410 discharge** (f5dd2373):
  `tau_muGrid_zeroRow_diff` ((4.8) row 0) + `tau_muGrid_fourCorner` ((4.10) δ-scaled) を
  toHypothesis46 経由で実証明 (σ-bridge: `certainTypeOmegaSigma h46 = alignedOmegaSigmaGrid`、
  ticVdiff h46 ≡ tic は rfl)。(11.8.5) capstone `residualCoeff_eq_zero` の hdeg0/h410/h48
  thread を除去 (+hw2 param、CharacterParameters.w2_prime が供給)。

**残り**: なし (本 issue スコープ)。(11.8.4) h114 thread は別作業 (coherence 依存で同根でない)。
§6 (S08) 側の Hypothesis46 discharge は §6 の endpoint gate と共に別途。

## 追加発見 2 (2026-07-02, §10 instantiation 調査中): typePA0 の G-共役も unsound

`OddOrder/GroupTheory/MaximalSubgroupType.lean:309`:
`typePA0 = typePA ∪ conjClassSet (typePV)` は **G-共役閉包** (`conjClassSet T = {gtg⁻¹ | g ∈ G}`)。
だが:
- **原文 (8.10)**: 「A₀(M) = A(M) ∪ **V^M**」 (M-共役)。Coq `prime_Dade_definition` も
  `class_support V L` (L-共役)。
- `S04.Hypothesis G A L` は `subset_L : A ⊆ L` を**要求** (S04_DadeIsometry:194)。
  `conjClassSet (typePV) ⊆ M` は成立しない: 成立すると V の正規閉包 ⊆ M が G の非自明真正規部分群を
  与え **G の単純性に矛盾**。⟹ sorried `dadeSupportHypotheses_typeP` (S10:566) の第 1 成分
  `Nonempty (DadeSupportHypothesisData M (typePA0 M data))` は **statement が偽** (充足不能)。
  scaffold-sorry の unsound carrier ([[scaffold-sorry-free-not-done]] の実例)。
- **修正案**: `typePA0 := typePA ∪ {m v m⁻¹ | v ∈ typePV, m ∈ M}` (M-共役; もしくは
  `conjClassSetIn M` 的な相対版を GroupTheory 側に新設)。
- **fallout 見積**: S12 `Hypothesis.dadeData` (型は typePA0 経由 — 定義変更で自動追従)、
  `Hypothesis.A0 = supportInSubgroup typePA0 M` (縮む)、`muGrid_alpha_support` 系の
  「support ⊆ A0」証明 (中の共役は (2.1) 由来で M-元による共役 → M-共役版で同証明が通る見込み)、
  `normalizer_typePA_eq` (Core:~400、conjClassSet の G-不変性を使用 → 書き直し。ただし
  dadeSupportHypotheses_typeP 第 2 成分 (A(M) 版 normalizer_eq) から直接取る再編が自然)。
- **判定**: 発見 1 と同根 ((8.15) 形式化の前提衛生)。lane a の claim 範囲に含めて続行。

## 動機 (FT 経路)

(11.8.3) β real piece 4 (betaE) は Pf (4.8) `certainType_diff_dade_eq` / (4.10) `fourCorner_dade_eq`
(S06 に landed 済、Hypothesis46 前提) を §10 の aligned grid で cite する必要がある。現状の big-V
Hypothesis46 は §10 から供給不能なので、この修正が (4.8)/(4.10) 消費の前提。§6 (S08) 側の
Hypothesis46 discharge (§6 endpoint の gate) にも同じ修正が必要になる見込み。

## lane a の並行対応 (この issue に gate されない)

(11.8.3) piece 4/5 (betaE + Rbeta assembly) は (4.8)/(4.10) の aligned-grid 版を
**hypothesis-threaded** (h48/h410 パラメータ) で先に組む (hβr と同じ方式)。本 issue の修正 +
§10 instantiation が landed したら thread を discharge。

## 完了条件

- Hypothesis46 が small V 形に修正され、S06_CertainType* が build green。
- `Hypothesis.toHypothesis46` (§10 instantiation) が sorry-free で landed。
- (4.8)/(4.10) が §10 aligned grid から cite 可能 (piece 4 の h48/h410 thread が discharge)。

## 参照

- 原文: 04.5 p.15 (3.1), 04.10 p.46 (8.10) + **p.48 (8.15, PDF 直読)**, 04.6 pp.21-24 (4.6)/(4.8)/(4.10)。
- Coq: PFsection3.v:69 (cyclicTIset), PFsection4.v:707-716 (prime_Dade_hypothesis)。
- Lean: OddOrder/Peterfalvi/S06_CertainHypothesis46.lean:51 (tic_V), :65 (dade0);
  S06_CertainTypeIsometry.lean:58 (ticVdiff), :276 (supp 補題), :622 ((4.8));
  S06_CertainTypeFourCorner.lean:440 ((4.10))。
- notes/peterfalvi/s13_11_8_orthogonality.md cont.⁶⁶ (本 issue の発見経緯)。
- [[verify-port-state-by-number-not-coq-name]] [[feedback-file-hub-issue-dont-stop]]
