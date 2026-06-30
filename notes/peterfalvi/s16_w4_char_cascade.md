# Pf §16 POLE-2 char cascade — W4 (lane-h, 2026-06-25 relane #9)

> lane-h = **W4 = POLE-2 `field_normalizer_structure` (Pf 14.2) char cascade + §15 setup**
> (正本 `notes/meta/ft_frontier_remap_2026_06_25.md` §2 W4、issue 0083)。Arm B = 最終矛盾の
> 独立アーム。W1 (lane-f) と upstream gate を共有しない。

## 全体構造 (2026-06-25 調査確定)

`field_normalizer_structure` **本体は sorry-free assembly**。§16 の**算術/数値スケルトンは網羅的に
完成済み** (sorry-free): `all_pm_one_and_card_of_odd_sq_sum_le` (14.11.2 parity core) /
`one_le_norm_signed_paired_sum` (14.11.3/3.9 parity core) / cyclotomic facts (13.14) / m-bounds
(13.11) / norm-cascade consumer chain / `norm_error_terms_lt_inv_q` / `norm_cascade_contradiction`。

残 sorry は全て **genuine character theory** で、共通の foundation に interlock している:
**concrete §3/§4 Dade-isometry 構成** (abstract §16 carrier `ω`/`η`/`tau3`/`betaM` を pin する
「残り §3/§4 layer」) + **(7.5) Frobenius/TI norm formula (repo 未実装)**。

### 残 sorry の bottom-out 先

| 種別 | sorries (S16_NonExistenceG 他) | gate |
|---|---|---|
| Dade η-grid 基盤 | `betaM_expansion` (14.11.2), `normCascadeBound_of_charData` (14.11.4), `orthogonality_switch` (14.14), `caseB_character_contradiction_of_gap_inequalities` (14.16), `exists_MHypothesis` (14.10) | §3/§4 Dade 構成 + (7.5) norm |
| §9/§11 char | `c_eq_one` (13.12), `U_cyclic_and_Q_elemAbelian`, `V_cyclic`, `T_side_caseB_facts`, `caseB_order_u` (13.15) | §9/§11 character theory |
| BG §14 σ | `basic_structure_gated` (P_order), `card_Q_eq` | σ-structure (lane-f/W1) |
| BG Thm E / 深 §13 | `card_LF_coprime_pq`, `normalizer_W1` (13.16), `complement_inf_Q_structure` | lane-f/F or 深 §13 (`s13_17_structural_program.md`) |

## アプローチ (ユーザー裁可 Option A、2026-06-25)

「基盤を lane-h で構築」: opaque endpoint を **done 算術コア + faithful Dade producer** による honest
assembly に de-opacify し、不足する Dade 基盤 ((3.9) integrality / (7.5) norm) を reusable lemma /
faithful producer として lane-h で実装。repo の established pattern (lane-c §16 de-opacification)。
**doneness = carrier/仮説の構成可能性で判定** ([[scaffold-sorry-free-not-done]])。

## 進捗

### ✅ betaM_expansion (14.11.2) — S09 §7 bridge de-opacification (lane-h resume, this session)

bare `sorry` を **faithful carrier + 実 Lean 証明 + axiom-clean S09 cite bridge** に分解
(`S16_NonExistenceG.lean`):

- **`BetaMExpansionData hyp Mdata`** (faithful data carrier, `structure`): (7.8.a) decomposition
  `β_M^τ = 1_G − χ + Δ` (`betaM_seven_eight`) + η-grid 同定 `1_G + Δ = Σ_{ij} ε_ij η_ij` (`grid_eq`,
  signs ±1) を ClassFunction レベルで carry。**χ は generic field** (`chi` + `chi_norm:‖χ‖=‖ψ^τ₁‖`)
  ゆえ原文 (14.11.2) の 2 branch (`χ=ψ^τ₁` / `χ=−ψ̄^τ₁`) を両方忠実カバー。data 構造ゆえ
  `noncomputable def` 製 (Prop でないので theorem 不可。`EtaGenericData` は全 Prop fields で Prop ゆえ
  theorem 可だった差分に注意)。
- **`betaM_expansion_data`** (faithful producer, `noncomputable def := sorry`): type-I M が (7.8)
  Dade-coherence 構造を持つ事実。§3/§4 Dade-isometry layer で discharge。`EtaGenericData` と同パターン。
- **`betaMExpansionData_of_hypothesis78`** (✅ **axiom-clean** bridge lemma, AxiomsCheck 登録、3 axioms):
  concrete `S09.Hypothesis78 G A M` + 同定 (`β_M=β`, `ψ^τ₁=ζ^ν`) + η-grid id から `BetaMExpansionData`
  を構成。`betaM_seven_eight` を **S09 `beta_eq_constOne_sub_zetaImage_add_delta` (β=1_G−ζ^ν+Δ) の
  pure `rw`** で導出 ⟹ (7.8.a) rearrangement が S09 §7 の genuine consequence と certify (独立仮説でない)。
  obligation を §3/§4 Dade 構成 + (13.1.d) η-grid 同定に縮約。
- **`betaM_expansion` 本体** = 実 Lean 証明: `e=pq` は field `MHypothesis.complement_card_eq_pq`
  (cite)、η-grid 展開は `betaM_seven_eight` + `grid_eq` の `abel` rearrangement、χ:=carrier の `chi`、
  `‖χ‖=‖ψ^τ₁‖` は `chi_norm`。bare sorry → faithful producer のみに isolate。`generic_character_bound`
  (14.11.3) は本 betaM_expansion をそのまま consume (destructure 形 `⟨_he,ε,hε,χ,hχnorm,hexp⟩` 不変)。

S09 §7 cite 経路: `S09_NonexistenceCertain` は S16 import closure 内 (S11→S10_MinimalSimpleStructure→S09
経由、python closure 検証済 275 modules)。full build 3872 jobs green, 21s。

### ✅ normCascadeBound_of_charData (14.11.4) — two-sided ρ-norm carrier (本セッション)

原文 (14.11.4 p.90) の構造を忠実に分離。導出 = (7.5) family inequality を ψ^τ₁ (norm 1) に適用 →
`‖ψ^{τ₁ρ}‖²` の two-sided bound → rational 不等式:

- **`NormCascadeData hyp Mdata`** (faithful carrier): `rhoNormSq:ℚ` + `lower` ((7.5)+(14.11.3):
  `1−pq/k ≤ ‖ψ^{τ₁ρ}‖²`) + `upper` ((7.5)+(7.8.b): `‖ψ^{τ₁ρ}‖² ≤ 1−1/p−1/q+2/(pq)+1/(uq)+1/(vp)`、
  原文の `(|P|−1)/|P|≤1` 等で loosen 済)。two-sided 構造が textbook の 2 段導出を反映。
- **`normCascadeData`** (faithful producer, `noncomputable def := sorry`): (7.1) ρ-map for (M,A(M)) +
  (7.5) `FamilyHypothesis71` + (7.8.b)/(14.11.3) norm bounds。§7 Dade layer で discharge。
- **`normCascadeBound_of_charData` 本体** = 実 `linarith`: lower+upper の transitivity から
  `1/p+1/q ≤ pq/k+2/(pq)+1/(uq)+1/(vp)` = `normCascadeBound`。bare sorry → faithful producer のみ isolate。

注: betaM (14.11.2) と違い axiom-clean S09 bridge lemma は未付随 ((7.5) の lower bound 導出は
`family_inequality` の real-analysis 出力を `1−pq/k` に同定する要で、FamilyHypothesis71 構成の重い
instance plumbing 要)。modest だが honest な de-opacification (実 linarith + faithful carrier)。

### ✅ caseB_character_contradiction_of_gap_inequalities (14.16) — β_L 展開+直交性 carrier (本セッション)

原文 (14.16 p.92) の case-(b) 最終矛盾を忠実分離。bare sorry (`False`) を **faithful carrier + 実
inner-product assembly** に:

- **`CaseBContradictionData nc`** (faithful carrier, `[Fintype G][Invertible (Nat.card G:ℂ)]`):
  `betaL`/`chiL`/`signs`(±1) + `betaL_expansion` ((14.16): β_L^τ = Σ ε η − χ_L、(14.11.2)/(13.19.c) 由来)
  + `eta_orthogonal_psi` ((η_ij, ψ^τ₁)=0、ψ^τ₁ は (14.11.2) で除去される直交成分) + `chiL_orthogonal_psi`
  ((χ_L, ψ^τ₁)=0、(4.1) L^τ₁⊥M^τ₁) + `pairing_ne_zero` ((β_L^τ,ψ^τ₁)≠0、(14.14.b) case-b)。
  ψ^τ₁ = `nc.Mdata.tau1 nc.Mdata.psi`。
- **`caseB_contradiction_data`** (faithful producer, `noncomputable def := sorry`): case-b+gap から
  expansion+直交性+pairing を assemble。expansion は §3/§4 Dade layer + 既 proven
  `exists_typeI_eta_axes_odd_of_caseB_gap` (axes-odd) に bottom-out。
- **`inner_finset_sum_left`** (sorry-free reusable helper): `inner (Σ f i) ψ = Σ inner (f i) ψ`
  (`inner_add_left` 帰納、hoistable to ClassFunction.lean)。
- **本体** = 実 inner 計算: `(β_L^τ,ψ^τ₁) = (Σ ε η − χ_L, ψ^τ₁) = Σ ε·(η,ψ)−(χ_L,ψ) = Σε·0−0 = 0`
  (`inner_sub_left`+`inner_finset_sum_left`×2+`inner_smul_left`+直交性)、`pairing_ne_zero` と矛盾。
  instance = `Fintype.ofFinite`+`invertibleOfNonzero (Nat.card_pos.ne')`。

bare sorry (`False`) → faithful producer のみに isolate。**§16 char endpoint 3 本 (14.11.2/14.11.4/14.16)
de-opacify 完了** (issue 2024 checklist 3/4)。

**次手** = §3/§4 Dade concrete 構成 (`betaM_expansion_data`/`eta_generic_data`/`normCascadeData`/
`caseB_contradiction_data` 共通の最終 obligation) / `normCascadeData` の (7.5) lower-bound bridge (重い) /
`exists_MHypothesis` (14.10)。

### ✅ generic_character_bound (14.11.3) — honest assembly (commit `483a5716`)

opaque `sorry` を honest assembly に置換。**直接 sorry 不使用**。新規:

- **`finNeg` / `finNeg_val` / `finNeg_involutive` / `finNeg_eq_self_iff`** (sorry-free, reusable):
  `Fin n` (n>0) 上の negation involution `i ↦ (n−i) mod n`。odd n で一意固定点 `0`。(3.9.a) の
  共役 `(i,j) ↦ (−i,−j)` を表す index map。
- **`one_le_norm_eta_grid_signed_sum`** (sorry-free, reusable): (14.11.3) parity core を η-grid
  (`Fin q × Fin p`, product-negation involution) に特化。`one_le_norm_signed_paired_sum` (既存
  done) に product 共役を供給。`generic_character_bound` が消費。
- **`classFunction_sum_apply`** (sorry-free, reusable): ClassFunction 有限和の点別評価
  (hoistable to `ClassFunction.lean`)。
- **`EtaGenericData` / `eta_generic_data`** (faithful producer, `:= sorry`): (3.9.c) `η_ij(g)∈ℤ`
  on G₀ / (3.9.a) conjugation 対称 + `η₀₀(g)=1` / (14.10) `β_M^τ(g)=0` on G₀。**結論の言い換えでない
  genuine 制約**。concrete 構成は §3/§4 Dade-isometry 層。

assembly: `betaM_expansion` (cite) の β_M 展開を点別評価 → `β_M(g)=0` で `χ(g)=Σε_ij η_ij(g)` →
η 整数性で `Σε_ij(n_ij:ℂ)` → `one_le_norm_eta_grid_signed_sum` で `‖·‖≥1` → `‖χ‖=‖ψ^τ₁‖`。
`generic_character_bound` に `hne` (K≠V) 追加 (唯一の消費者 `normCascadeBound_of_charData` は hne 保持)。

## ⚠ 真の foundation = §7 Dade ρ-machinery (7.1)–(7.8)（原文確認 2026-06-25）

`normCascadeBound_of_charData` (14.11.4) と `betaM_expansion` (14.11.2) は、いずれも Pf **§7 の
Dade ρ-machinery** に bottom-out する。原文 (mmd `04.9` pp.38-43) で確認:

- **(7.5)** (`normCascadeBound` の核): Hyp (7.4)（subgroup 族 `L_i`・isometry `τ_i`・supports
  `A_i^{τ_i}` 互いに disjoint・`G₀ = G − ∪A_i^{τ_i}`）の下、`χ∈Irr G` に対し
  `(1/|G|)(Σ_{g∈G₀}|χ(g)|² − |G₀|) + Σ_i(‖χ^{ρ_i}‖² − |A_i|/|L_i|) ≤ 0`。証明は norm 分解 (7.3) +
  (7.2.b)。= **CF(L,A) / ρ map / Hyp 7.1-7.4 の framework が前提**。pure-arithmetic でない。
- **(7.8)** (`betaM_expansion` の抽象版): coherent `S` の下、`β = 1_G − ζ^ν + a·Σ φ(1)/(e‖φ‖²)φ^ν + Γ`
  (`Γ ⊥ S^ν∪{1_G}`)、`e≤(h−1)/2 ⟹ ‖Γ‖²≤e−1` (7.8.b)。`betaM` の η-展開 + `Σa_ij²≤e−1` はこの
  instance。±1 は (7.8) の `a∈ℤ` + Dade 合同。

### ✅✅ 重要訂正 (2026-06-25): §7 ρ-machinery は S09 に既に形式化済み・cite 可能

当初「§7 ρ-machinery を新規形式化要・lane-c §7 重複」と評価したが**誤り**。**`S09_NonexistenceCertain.lean`
に (7.1)-(7.8) がほぼ完全 sorry-free で実在** (全ファイル実 sorry 1 個): `Hypothesis71`/`chiRho` (ρ map,
7.1-7.3) / `FamilyHypothesis71`/**`family_inequality` (7.5, sorry-free)** / `Hypothesis76` (7.6-7.7) /
`Hypothesis78`/**`beta` (7.8, sorry-free)**。S09 は S10→…→S16 で推移 import 済 ⟹ **S16 から cite 可能**。
lane-c の §7 は coherence (S07_*) で**別ファイル = 衝突なし**。

⟹ **W4 の genuine 残作業 = §16 MHypothesis → S09 bridge** (lane-c 協調不要な lane-h §16 work):
`Hypothesis71`/`Hypothesis78` は concrete `S04.Hypothesis`+`S04.DadeMap` を要求 / MHypothesis は abstract
`tau` のみ ⟹ type-I M の Dade extension (14.10) から faithful に bridge carrier を供給 (S04 concrete 構成
=§3/§4 が discharge)。本セッションの貢献 (parity-core 特化 + `generic_character_bound`) はこの上に乗る。
詳細手順 = issue 2024。

## 次手候補 (優先順・未着手) — 全て lane-h §16 work (lane-c 協調不要)

正本手順 = **issue 2024**。共通の鍵 = MHypothesis → S09 bridge carrier (faithful `Hypothesis71`/`Hypothesis78`)。

1. **bridge carrier** (最上流): MHypothesis に `Hypothesis71 G (A M) M` / `FamilyHypothesis71 G 1` /
   `Hypothesis78 G (A M) M` を faithful 供給 (type-I M の Dade extension 14.10 から)。`eta_generic_data`
   と同パターン。これが揃えば 2/3/4 は S09 cite + 算術で de-opacify 可。
2. **`normCascadeBound_of_charData` (14.11.4)**: `family_inequality` (7.5, S09 cite) +
   `generic_character_bound` (本セッション) + (7.7) 内積式 → `normCascadeBound`。(14.11.4) 算術が intricate。
3. **`betaM_expansion` (14.11.2)**: `Hypothesis78.beta`/(7.8.a) (S09 cite) を η-grid 形に identify +
   `all_pm_one_and_card_of_odd_sq_sum_le` (done) で ±1。⚠ full-grid vs non-principal の index split。
4. **(14.16) dual** `caseB_character_contradiction_of_gap_inequalities`: β_L の (7.8) expansion で同様。
   axes parity (`TypeIOrthogonalityData.caseC2_eta0j_odd`) は citeable・既 proven。

## cross-lane (lane-c / §3-owner 宛)

lane-h は §16 (lane-h owned) 内で **§3/§4 Dade obligation を faithful producer として isolate** 中
(`eta_generic_data` = (3.9) integrality/symmetry + (14.10) support vanish)。これらは将来 §3/§4
Dade-isometry concrete 構成 (lane-c §5/§7 coherence 機構と連続) で discharge される。**現状 §3-§7
ファイル未編集ゆえ衝突なし**。(7.5) norm を §7 に置く場合は事前に notes で調整。
[[cross-lane-sync-via-notes]] [[feedback-cite-sorried-lemmas-if-signature-correct]]

## ✅ 2026-06-28 (lane c=γ 新体制初): MHypothesis Dade carrier 化 + `toFamilyHypothesis71` — POLE-2 §7 接続点 sorry-free landing

「次手候補 1 = bridge carrier (最上流)」の**実装核を landing**。POLE-2 全 producer
(`normCascadeData`/`eta_generic_data`/`betaM_expansion_data`/`caseB_contradiction_data`) が共通に
bottom-out する §7 接続点を確立 (`S16_NonExistenceG.lean`, sorry-free, leaf+full build green):

- **MHypothesis に `typeIHyp : OddOrder.Peterfalvi.S14.Hypothesis M` carrier 追加** = type-I maximal
  `M` (over N_G(V)) の genuine Dade setup (`TypeIData` + (8.15) Dade support `dadeData` for
  `A(M)=typeIA M` + 共役不変 `hconj`)。S14 (lane b 所有) の `exists_typeI_hypothesis` (**sorry-free**)
  で将来供給可能 = honest carrier (scaffold でない; [[scaffold-sorry-free-not-done]] の doneness 基準
  「carrier の構成可能性」を満たす)。consumer は exists_MHypothesis (既 sorry) のみ ⟹ 影響限局。
- **`MHypothesis.toFamilyHypothesis71` (sorry-free)** = `S12.Hypothesis.toFamilyHypothesis71` の
  type-I 版移植 (typeIA support ゆえ A_0→A restrict 不要、より直接的)。`S09.FamilyHypothesis71 G 1`
  を構成 → `S09.family_inequality` (7.5, sorry-free) を `M` に直接適用可能に。

**残 (normCascadeData 14.11.4 honest 化、次セッション最優先)** — 道筋確定済、3 課題:
1. **ℚ/ℝ bridge**: `NormCascadeData.rhoNormSq : ℚ` を `(toFamilyHypothesis71).chiRhoNormSq (ψ^τ₁) 0 : ℝ`
   に同定 (norm² は有理数だが型が違う、cast 補題要)。
2. **ψ^τ₁ の norm-one**: `family_inequality` の `hχ : inner χ χ = 1` 入力。MHypothesis の `tau1`/`psi` を
   §13.3 τ₁ Dade isometry + `psi ∈ Mset` (Irr) として characterize する carrier 強化が要 (S12 の
   `inner_tau1_zeta_self_eq_one` に相当)。
3. **upper/lower 導出**: upper = family_inequality + `generic_character_bound` (‖ψ^τ₁‖≥1 on G0、landed) +
   `|A(M)|/|M|` 評価; lower (1−pq/k) = (7.8.b) coherence norm formula (重い)。S12 の
   `chiRhoNormSq_zeta_le_line83` (`S12:6047`) が type-P 版の完全テンプレート。

de-opacify 後は `eta_generic_data`/`betaM_expansion_data` も同 `typeIHyp` carrier から S09 cite で連鎖。
[[scaffold-sorry-free-not-done]] [[feedback-cite-sorried-lemmas-if-signature-correct]] [[feedback-no-avoiding-hard-parts]]

### cont. (lane c=γ /loop): Hypothesis78 carrier 導入 + betaM_expansion_data honest 化 (commit 7c8af266)

MHypothesis に M の §7 coherence (`h78 : S09.Hypothesis78`) + 整合 carrier
(`betaM_eq`/`psi_tau1_eq`/`betaSigns`/`betaSigns_pm`/`betaGrid` = 13.1.d η-grid) を追加。
**betaM_expansion_data (14.11.2) を honest 化**: `h78.beta_eq_constOne_sub_zetaImage_add_delta`
(S09 (7.8.a), sorry-free) cite + carrier から genuine 構成。残 obligation =
exists_MHypothesis の h78 supply (M coherence) + η-grid (13.1.d) に isolate。full build 3886 green、
S16 実 sorry 11→10。instance plumbing は `open scoped S12.FiniteInduce in` (docstring の**前**) で
`finiteG : Finite G` から Fintype/Invertible 供給 (FiniteInduce に finiteGFintype/natCardInvCG 在)。

**⚠ normCascadeData (14.11.4) の追加課題発見 (原文 `04.16` 精読)**: 既知 3 課題 (ℚ/ℝ・norm-one・
upper/lower) に加え、**family_inequality の support が toFamilyHypothesis71 と異なる**。原文は `ρ` を
(M, A(M)) で取るが norm 評価の `G₀ = G − [Ã(M) ∪ (W#)^G ∪ (P#)^G ∪ (Q#)^G]` (thickened + W#/P#/Q# 除外);
一方 `toFamilyHypothesis71.G0 = G − A(M)^τ`。(14.11.3) の `|ψ^τ₁|≥1` はこの狭い G₀ 上ゆえ、
family_inequality 出力の `Σ_{G0}` から W#/P#/Q# 寄与を分離する counting が要る (S12 (10.8) の
`sum_zeta_tau1_normSq_ge_card`+`dadeSupport_restrict_subset` に対応)。**normCascadeData は betaM より深い**。
次は `S12.chiRhoNormSq_zeta_le_line83` (`S12:6047`) を type-I M 版に移植する形で着手するのが定石。

### cont.² (lane c=γ /loop): normCascadeData ℚ/ℝ 土台 commit (25006c10)

本丸着手の準備として **NormCascadeData.rhoNormSq を ℚ→ℝ 化** (S09 `FamilyHypothesis71.chiRhoNormSq : ℝ`
に対応、(7.5)/(7.8.b) 導出を ℝ で行えるように)。`normCascadeBound_of_charData` は ℝ lower/upper から
ℚ `normCascadeBound` へ **`rw [← Rat.cast_le (K := ℝ)]; push_cast; linarith`** で降下 (build-green)。
`normCascadeData` 本体は依然 sorry。**本丸 (次セッション、fresh context 推奨、複数ターン)**:
1. `rhoNormSq := (Mdata.toFamilyHypothesis71).chiRhoNormSq (Mdata.tau1 Mdata.psi) 0`。
2. **ψ^τ₁ norm-one**: `family_inequality` の `hχ : inner (tau1 psi) (tau1 psi) = 1` 入力 = MHypothesis に
   norm-one carrier 追加 (tau1 isometry + psi Irr、betaM の h78 carrier と同パターン)。
3. **lower** (1−pq/k ≤ rhoNormSq): `family_inequality` + (14.11.3) `generic_character_bound`
   (‖ψ^τ₁‖≥1 on G0) で `S12.chiRhoNormSq_zeta_le_line83` を type-I M 移植 (support set counting)。
4. **upper** (rhoNormSq ≤ …): `family_inequality` + (7.8.b) `h78.NormEstimates`。
全 piece は h78 carrier (commit 7c8af266) + toFamilyHypothesis71 (commit 95bcc13e) から接続済。

### cont.³ (2026-06-29 lane c=γ, ユーザー裁定 §16 本丸): line-83 upper-bound step + 2 carrier field 着地

normCascadeData (14.11.4) の **upper bound 第一段を sorry-free 着地** (`S16_NonExistenceG.lean`,
full build 3886 green)。原文 (14.11.4 04.16 lines 107-115) の family inequality 骨格を honest 化:

- **MHypothesis に 2 carrier field 追加** (build-safe: 構成は exists_MHypothesis=sorry のみ、
  field access は不変ゆえ downstream 無影響):
  - **`psi_tau1_norm_one : ClassFunction.inner (tau1 psi) (tau1 psi) = 1`** ((14.10)/(7.5):
    ψ^τ₁ norm-one = family_inequality の `hχ` 入力。S12 `inner_tau1_zeta_self_eq_one` の V-side dual)。
    MHypothesis は `open scoped S12.FiniteInduce in` 下で宣言ゆえ inner の Fintype/Invertible が
    `finiteG : Finite G` から synth (Finite は Prop ゆえ proof-irrelevance で family_inequality 側の
    instance と defeq、desync なし)。
  - **`G0_off_dadeSupport : ∀ g ∈ G0, g ∉ typeIHyp.dadeData.dade.dadeSupport`** ((14.11.3)/(14.11.4):
    G₀ ⊆ famG₀ = `(toFamilyHypothesis71).G0` = G − Ã(M))。toFamilyHypothesis71 は構造体の後方定義ゆえ
    Dade support を `typeIHyp.dadeData.dade.dadeSupport` で直接参照 (toFamilyHypothesis71 の `hyp71 i).hyp`
    と rfl 一致)。
- **`MHypothesis.chiRhoNormSq_psi_le_line83` (sorry-free)** = S12 `chiRhoNormSq_zeta_le_line83` の
  type-I M 移植。family_inequality (7.5) を `toFamilyHypothesis71` に適用 (norm-one =
  `psi_tau1_norm_one`) + generic_character_bound (‖ψ^τ₁‖≥1 on G₀) で `|G₀|≤Σ_{G₀}‖·‖²` (1≤‖·‖⟹1≤‖·‖²
  の `nlinarith`) + `G0_off_dadeSupport` で G₀⊆famG₀ → `Finset.sum_le_sum_of_subset_of_nonneg` で drop →
  `mul_sub`+`linarith`。結論 `‖ψ^τ₁ρ‖² ≤ |A(M)|/|M| + (1/|G|)(|famG₀|−|G₀|)`。

**残 (normCascadeData 完了まで、次セッション)**:
1. **upper**: line-83 の `|A(M)|/|M|` + `(1/|G|)(|famG₀|−|G₀|)` を **§8 TI-counting** で displayed
   `1−1/p−1/q+2/(pq)+1/(uq)+1/(vp)` に評価 (原文 line 109-115: `|K#|/|M|`, `|(W#)^G|`/`|(P#)^G|`/
   `|(Q#)^G|` の |G| 比を引いて raw upper、(|P|−1)/|P|≤1 等で loosen)。**deep §8 counting**。
2. **lower**: `1−pq/k ≤ ‖ψ^τ₁ρ‖²` = **(7.8.b) coherence norm formula** (S09 BetaDecomp の `‖Γ‖²≤e−1`
   producer 要、重い)。
upper の family-inequality + G₀-drop 骨格は本セッションで honest 化済 ⟹ 次は 1 (§8 counting) または
2 ((7.8.b))。[[scaffold-sorry-free-not-done]] [[feedback-no-avoiding-hard-parts]]

### cont.⁴ (2026-06-29 lane c=γ /loop): upper-bound loosening step `normCascade_upper_loosen` 着地

normCascadeData (14.11.4) upper の **最終段 (loosening) を sorry-free 着地** (`S16_NonExistenceG.lean`,
full build 3886 green/33s):

- **`normCascade_upper_loosen` (sorry-free, 純 ℝ 算術)** = 原文 (14.11.4 04.16 line 115) の raw (7.8.b)
  upper estimate `1−1/p−1/q+1/(pq)+(|P|−1)/(|P|uq)+(|Q|−1)/(|Q|vp)+(k−1)/(kpq)` を
  NormCascadeData.upper の displayed bound `1−1/p−1/q+2/(pq)+1/(uq)+1/(vp)` に `(|P|−1)/|P|≤1`・
  `(|Q|−1)/|Q|≤1`・`(k−1)/k≤1` で loosen (各 `div_le_div_iff₀`+`nlinarith`、合流は `linarith`+
  `2/(pq)=1/(pq)+1/(pq)`)。**RHS は NormCascadeData.upper と一致ゆえ producer が直接 cite 可**。

**⟹ normCascadeData upper の算術両端が honest 化完了**: line-83 (第一段, cont.³) + loosen (最終段,
本)。**残る upper gate は §8 TI-counting** (raw bound 生成: `|K#|/|M|`, `|(W#)^G|`/`|(P#)^G|`/`|(Q#)^G|`
の |G| 比) **のみに crisp に絞られた**。lower gate は依然 (7.8.b)。次 /loop は上流優先で (7.8.b) lower
((7.8.b) coherence norm formula、§7) を正面から、または §8 counting。

注: `div_le_div_iff` は本 mathlib で **`div_le_div_iff₀`** (末尾 ₀) に改名 ([[verify-port-state-by-number-not-coq-name]] 系の API drift)。

### cont.⁵ (2026-06-29 lane c=γ): normCascadeData (14.11.4) **lower bound = (7.8.b)** sorry-free 着地

normCascadeData (14.11.4) の **lower gate を完全 honest 化** (`S16_NonExistenceG.lean`, full build
3889 green、AxiomsCheck OK 新 3 定理 allowlist 3 axioms、commit `f4d731ec`、main 同期済)。

**原文精読で lower/upper の出所を確定** (04.16 lines 107-115): (7.5) family inequality は単一の
不等式を与え、そこから (14.11.3) で G₀-part を drop ⟹ **upper** `‖ψ^{τ₁ρ}‖² ≤ |K#|/|M| +
(1/|G|)(|(W#)^G|+|(P#)^G|+|(Q#)^G|)` (→§8 counting → raw → loosen)。**lower** `1−pq/k ≤ ‖ψ^{τ₁ρ}‖²`
は **(7.8.b) coherence-norm formula 直接** (`‖ζ^{νρ}‖² ≥ 1−e/h`、e=pq, h=k)。⚠ NormCascadeData
の旧 docstring は lower=(7.5)+(14.11.3) / upper=(7.5)+(7.8.b) と **swap して誤記**していた → 訂正。

**genuine 成果 (全 axiom-clean)**:
- **`chiRhoCF_congr_hyp`** (一般): `S09.Hypothesis71.chiRho` は support hypothesis `H71.hyp`
  (= H(a)-族) のみ依存で **Dade map τ 非依存** (chiRho 定義 S09:133-138 が τ を参照しない)。
  ⟹ 異なる τ でも同じ `.hyp` なら chiRhoCF 一致。
- **`MHypothesis.chiRhoNormSq_eq_zetaNuRhoNormSq`** (bridge、linchpin): family-inequality ρ-norm
  `(toFamilyHypothesis71).chiRhoNormSq (ψ^{τ₁}) 0` = (7.8.b) coherence-norm `h78.zetaNuRhoNormSq`。
  `psi_tau1_eq` (ψ^{τ₁}=ζ^ν) + `h78_hyp_eq` (同 Dade support) + chiRhoCF_congr_hyp。**(7.5) family
  inequality 層と (7.8.b) coherence-norm 層を繋ぐ**。⚠ instance desync (両 inner が同 M の別
  FiniteInduce instance) は `congr 1` で Subsingleton 自動解決 ([[lean-induce-transport-instance-desync]])。
- **`MHypothesis.rhoNormSq_ge_lower`**: lower 組立 = bridge + (7.8.b carrier) + index 算術。
  index: `h78.kernelOrder=Nat.card H=|K|=k` (h78_H_eq+k_eq_card_K)、`h78.complementIndex=|M:K|=pq`
  (h78_H_eq + `kernelOrder_mul_complementIndex_eq_card_L` + Lagrange `Subgroup.card_mul_index` +
  `subgroupOfEquivOfLe` + e_eq_index + complement_card_eq_pq、`Nat.eq_of_mul_eq_mul_left` で cancel)。

**MHypothesis に faithful carrier 3 本追加** (構成は exists_MHypothesis=sorry のみゆえ build-safe):
`h78_hyp_eq` (h78.hyp76.hyp71.hyp = typeIHyp.dadeData.dade、bridge 互換) / `h78_H_eq`
(h78.hyp76.H = K、kernel) / `h78_zetaNuRho_normSq_ge` (`1−ci/ko ≤ zetaNuRhoNormSq` = (7.8.b)
`NormEstimates.zetaNuRho_norm_sq_ge` for M、smallIndex=2pq+1≤k from (14.11.1) k>2pv & v≥q 充足)。
**doneness は carrier 構成可能性** ([[scaffold-sorry-free-not-done]]): 3 carrier は型-I M で全て真
(compatibly-built h78 で rfl/structural)、exists_MHypothesis に isolate。

**producer `normCascadeData` を full-sorry → field-split**: `rhoNormSq`=family norm + `lower`=
rhoNormSq_ge_lower を honest 配線、**残 sorry は `upper` §8 TI-counting のみに isolate** (line-83
`chiRhoNormSq_psi_le_line83`✅ と loosen `normCascade_upper_loosen`✅ の両端は既 honest、gap は
`|K#|/|M|`・`|(W#)^G|`/`|(P#)^G|`/`|(Q#)^G|` の orbit cardinality count)。

**次 /loop**: upper §8 TI-counting (line-83 → raw bound)。= conjugacy-class orbit size
`|(P#)^G|=[G:C_G(P)]·|P#|` 型 + (8.6.a)/(8.11)/(10.7) の C_S(x)/C_T(x) 包含。S12 (10.8) の
TI-counting (`G₁⊆(H#)^G∪V^G`) の type-I M 対応物。[[scaffold-sorry-free-not-done]] [[feedback-no-avoiding-hard-parts]]

### cont.⁶ (2026-06-30 lane c=γ /loop): normCascadeData upper を line-83+§8-gap に wire + §8 plan 確定

`normCascadeData` (14.11.4) の **`upper` field を honest skeleton 化** (commit `a7ff9cb2`、full build
3889 green/15s): `upper := le_trans (chiRhoNormSq_psi_le_line83 [proven]) line83_le_displayed_upper`
⟹ **producer body は sorry-free**、残 §8 obligation を単一 named lemma `line83_le_displayed_upper`
(sorried, precise statement) に isolate。∴ normCascadeData の 3 field = rhoNormSq (具体) + lower
(proven) + upper (line-83 ✅ + §8-gap)。

**§8 TI-counting plan 確定** (`line83_le_displayed_upper` を埋める道筋、原文 04.16 L109-115):
1. **`|A(M)|/|M| = (k−1)/(kpq)`**: type-I Dade support `A(M) = typeIA M = K#` (= `|K|−1`) + `|M| = pqk`。
   ⚠ `typeIA M = centralizerSupport (sharpSubgroup H) M` で**単純な K# でない** → `|typeIA M| = |K#|`
   自体が §8 事実 (要確認/証明)。S12 type-P 側は `typePA_eq_sharpSubgroup_derivedInG` + `Set.ncard_diff`
   で `|typePA|=|M'|−1` を出す (S12:6126、pattern 流用可)。
2. **orbit counting** `(1/|G|)(|famG₀|−|G₀|) ≤ (1/|G|)(|(W−(W₁∪W₂))^G|+|(P#)^G|+|(Q#)^G|)`:
   - set 部 = `famG₀∖G₀ ⊆ (W..)^G∪(P#)^G∪(Q#)^G` (union bound)。⚠ `Mdata.G0` が **abstract carrier**
     (= G−[Ã(M)∪orbits] の orbit 構造を持たない) ゆえ、G0 を concrete 化 or carrier 追加が要。
   - **✅ tool 在庫**: **`S14.ncard_conjClassSet_of_isTISubset`** (S14_TypePCounting:5594、axiom-clean、
     登録済) = `(conjClassSet A).ncard = A.ncard · L.index` (TI-subset A、L=normalizer-bound で A 安定)。
     ⟹ `|(P#)^G| = (|P|−1)·[G:N_G(P)]`。
   - normalizer サイズ `[G:N_G(P)]=|G|/(|P|uq)` 等は **Type-II partner S=(H⋊U)⋊W₂** の構造
     ((8.6.a)/(8.11)/(13.12))。
3. **raw → displayed**: `normCascade_upper_loosen` (proven)。

**∴ 在庫 = orbit-cardinality tool (`ncard_conjClassSet_of_isTISubset`) + loosening。残 deep =
§8 structural input** = Frobenius pieces W/P/Q の (a) TI 性 (`IsTISubset`) + (b) normalizer サイズ +
(c) `Mdata.G0` の orbit-complement concrete 化 (carrier enrich)。= S12 (10.8) `G₁⊆(H#)^G∪V^G` の
type-I 対応 (S12 側も `typeII_coherence_contradiction_estimate` で sorry、共有 deep gate)。
**次 /loop** = (1) で `|typeIA M|=|K#|` を確認/証明 (tractable 候補) or §8 structure carrier 設計。
[[scaffold-sorry-free-not-done]] [[feedback-no-avoiding-hard-parts]]

### cont.⁷ (2026-06-30 lane c=γ /loop): Coq PFsection14 co-read — §8 counting 構造完全判明 + `|A(M)|=k−1` 確認

`line83_le_displayed_upper` (§8 TI-counting) の正確な port path を **Coq `PFsection14.v` の (14.11.4)
証明** (lines 929-991) 併読で確定。**typeIA=K# の不確実性を解消**:

- **Dade support**: `ddMK := FT_DadeF_hyp maxM`、`AM := Dade_support ddMK`、`defAM: AM = 'A~(M)`
  (`FTsupp_Frobenius`)。
- **upper `ub_rho`** (line 980): `'[rho(ψ^τ₁)] ≤ k.-1/#|M| − nG⁻¹·sumG0_diff` を **`Dade_cover_inequality`**
  (MathComp Dade 理論) 1 発で。`sumG0_diff = sumG0 − (#|G0|+#|What^G|+#|P#^G|+#|Q#^G|)`。
  **= 私の `chiRhoNormSq_psi_le_line83` と同型** (family_inequality (7.5) = single-member Dade-cover)。
- **🔑 `k.-1/#|M| = |A(M)|/|M|` ⟹ `#|A(M)| = k−1 = #|K#|` を Coq が確認** (Dade_cover_inequality の
  `#|A|` 項が `k−1`)。∴ **`typeIA M = K#` は TRUE** (型-I M の Frobenius FPF `C_M(x)≤K for x∈K#`
  由来。⚠ Lean TypeFData の `centralizer_le_U1` は弱条件のみ → 完全 FPF は別の §8 定理が要、
  但し結論 typeIA=K# は正しい)。`cardG_D1: #|R^#|=#|R|.-1` で `#|K#|=k−1`。
- **G0** (line 932): `~:(Ã(M) ∪ ccG What ∪ ccG P^# ∪ ccG Q^#)` (`ccG A = class_support A G = A^G`)。
- **P/Q/W の出所** (lines 926,933-934): **S/T type-P partner** (`FTtype2_support_coherence TtypeP
  StypeP` = (14.11.2)、`W2⊆P` [StypeP]、`W1⊆Q` [TtypeP])。P=S の Sylow 的ピース、Q=T 側。
- **(14.11.3) lbG0** (line 936): `1≤|ψ^τ₁(g)|²` on G0 = 私の `generic_character_bound` と同型
  (`coprime_typeP_Galois_core` で order prime-to-pq、`Cint_cycTIiso_coprime` で η-grid 整数、
  signed sum ≡1 mod 2 で |·|≥1)。

**∴ §8 counting port path 確定** (`line83_le_displayed_upper` を埋める):
1. **`|A(M)|/|M| = (k−1)/(kpq)`**: `typeIA M = K#` (Frobenius FPF、§8) + `|M|=kpq`。Coq で TRUE 確認。
2. **orbit counts** `|P#^G|=(|P|−1)·[G:N_G(P)]` 等: `ncard_conjClassSet_of_isTISubset` (在庫) + P/Q/W
   の TI 性 (S/T partner 構造) + normalizer サイズ ([G:N_G(P)]=|G|/(|P|uq))。
3. **drop + loosen**: sumG0≥|G0| (lbG0) で drop、`normCascade_upper_loosen` (proven)。

**残 deep = (a) `typeIA M = K#` の Frobenius-FPF lemma (§8)、(b) P/Q/W 定義 + TI 性 + normalizer
サイズ (S/T type-P partner 構造、§13-14)**。= multi-session port。Coq `Dade_cover_inequality` の Lean
analog は私の line-83 (= family_inequality) で既達ゆえ、残は orbit-size 評価 (TI tool 在庫) + partner
構造。次 = (a) typeIA=K# の FPF lemma (最 tractable、§8 Frobenius) から着手。[[scaffold-sorry-free-not-done]]

### cont.⁸ (2026-06-30 lane c=γ /loop): §8 第1成分 cardinalities 着地 + orbit-count plan 確定

**§8 counting 第1成分の cardinalities 実証** (commit `2f5c17c6`): `card_typeIA_eq` (`|A(M)|=k−1`、
FPF 恒等式を `typeI_frobenius` (12.7) の Frobenius witness に適用) + `card_M_eq` (`|M|=pqk`、
axiom-clean)。⟹ **第1成分 `|A(M)|/|M|=(k−1)/(kpq)` の cardinality 完成**。⚠ card_typeIA_eq は
typeI_frobenius 経由で (12.16)/lane-β に transitively gated (body sorry-free・citable)、AxiomsCheck 非登録。

**§8 残 3 成分 (W/P/Q orbit counts) の deep core 確認** (`line83_le_displayed_upper` を埋める残り):
- **在庫**: `hyp.base` が partner subgroups **P/Q/W2/U/S** を保持 (`hyp.base.P`/`.Q`/`.W2`/`.S`)、
  + 関係補題 (`hyp.base.S ≤ normalizer P`、`IsMulCommutative P`、`P ≤ centralizer P`、
  `Nat.card (P.subgroupOf S) = Nat.card P` @S16:3031)。orbit tool `ncard_conjClassSet_of_isTISubset`。
- **未在庫 (= deep, 要構築)**:
  (a) **P/Q/W の TI 性** (`IsTISubset (sharpSubgroup P) (normalizer P)`) — Frobenius kernel TI
      (`IsFrobeniusGroup.trivialIntersection` 在庫だが P の Frobenius 構造特定が要)。
  (b) **N_G(P)/N_G(Q) サイズ** (`[G:N_G(P)]=|G|/(|P|uq)`) — Type-II partner S=(H⋊U)⋊W₂ 構造から。
  (c) **`Mdata.G0` の orbit-complement concrete 化** — 現状 abstract carrier (`G0_off_dadeSupport`
      で `G0⊆famG₀` のみ)、`famG₀∖G0 ⊆ (W..)^G∪(P#)^G∪(Q#)^G` を出すには G0 を (14.11.3) 集合
      `G−[Ã(M)∪orbits]` に concrete 化 (carrier 追加、build-safe) が要。
- **S12 (10.8) と共有 deep gate**: 同じ TI-counting (`G₁⊆(H#)^G∪V^G`) が S12 でも sorried
  (`typeII_coherence_contradiction_estimate`)。partner orbit 構造は両者の共通核。

**次 /loop**: orbit-count 構築の最 foundational ピース = (c) G0 concrete 化 carrier 追加 →
set-reduction `famG₀∖G0 ⊆ orbits` (union bound) を実証 → 各 orbit を (a)+(b)+tool で評価。
あるいは (a) P TI 性 (Frobenius kernel) から。**deep multi-session structural build**。
[[scaffold-sorry-free-not-done]] [[feedback-no-avoiding-hard-parts]]

### cont.⁹ (2026-06-30 lane c=γ /loop): 🎉 §8 TI-counting 完全組立 — normCascadeData (14.11.4) body-sorry-free

ユーザー裁可「§8 orbit counts 正面構築」を**完遂**。`line83_le_displayed_upper` を body-sorry-free
証明 ⟹ **`normCascadeData` (14.11.4) は body-sorry-free** (upper = `le_trans (line-83) (line83_le_displayed_upper)`、
全 char content [lower (7.8.b) + upper §8] が MHypothesis carrier に isolate)。commits = §8 machinery
群 (`orbit_normSq_term`〜`famG0_sub_filter_card_le_orbit_ncard`) + 構造 carrier 8 + capstone `638f1dcb`。

**§8 機械 (全 axiom-clean reusable、~13 lemma)**:
- **bridge** `orbit_normSq_term` (`|A^G|/|G|=|A|/|N|`、TI-subset)。
- **W-orbit** `isTISubset_sdiff_sup_of_normalizer_eq` (TI、S12 typePData_V_ti 一般化) +
  `conj_smul_sdiff_sup_eq_of_normalizer_eq` (stab) + `orbit_sdiff_sup_normSq_term` (measure) +
  `ncard_sdiff_sup_add_eq` (|W-set|=|W|−|W1|−|W2|+1)。
- **P#/Q#-orbit** `conj_smul_sharpSubgroup_eq_of_mem_normalizer` (stab) +
  `orbit_sharpSubgroup_normSq_term` (measure、`Subgroup.IsTI`=orbit TI 定義的) +
  `ncard_sharpSubgroup_add_one` (|P#|=|P|−1)。
- **set-reduction** `famG0_sub_filter_card_le_orbit_ncard` (`|famG₀|−|G₀|≤Σ|orbit|`、`G0_orbit_cover` carrier)。
- **§8 第1成分** `card_typeIA_eq` (|A(M)|=k−1 via FPF 恒等式 `centralizerSupport_sharpSubgroup_eq_of_frobenius`)
  + `card_M_eq` (|M|=pqk)。

**MHypothesis 構造 carrier (§13-14 structural prerequisite、exists_MHypothesis に isolate)**:
G0_orbit_cover / W_normalizer_V / W_set_nonempty / P_isTI / Q_isTI / card_W_eq (|W|=pq) /
card_W1_add_W2_eq (=p+q) / card_normalizer_P_eq (|N_G(P)|=|P|uq) / card_normalizer_Q_eq (|N_G(Q)|=|Q|vp)
+ (lower 用) h78_zetaNuRho_normSq_ge 等。**counting は機械が genuine 実行、carrier は構造前提のみ** (ユーザー
「結果 carrier 化」拒否を遵守、[[scaffold-sorry-free-not-done]] doneness=carrier 構成可能性)。

最終 assembly: line83-RHS = |A(M)|/|M| + (1/|G|)(|famG₀|−|G₀|) ≤ (k−1)/(kpq) + W-term + P-term +
Q-term = raw bound (`normCascade_upper_loosen` で displayed へ、u,v>0 は normalizer carrier から)。

**残 §16 sorry** (normCascadeData は閉じた): `exists_MHypothesis` (全 carrier 供給、最大)、`eta_generic_data`
(§3 Dade)、`betaM_expansion`、`orthogonality_switch` (14.14、最深)、v formulas、CaseBContradictionData。
次 = exists_MHypothesis の carrier 供給 (deep §13-14) or orthogonality_switch。[[feedback-no-avoiding-hard-parts]]

### cont.¹⁰ (2026-06-30 lane c=γ /loop): main_size_bounds reduction + solo frontier 枯渇の確定

§16 char 義務 solo 続行 (ユーザー裁可) で 1 reduction 着地: `main_size_bounds_structural` (14.11.1)
の quotient bound `(k−1)/e ≥ (v−1)/p` を第1連言 `k>2pv` から純算術で genuine 化 (commit `fd9a55b8`)。
obligation = `k>2pv` のみ (構造 residual)。

**solo tractable frontier 枯渇の確定** (残 §16 sorry を網羅調査):
- `main_size_bounds_structural`: `k>2pv` のみ残 (deep、cyclotomic v-value + M order gated)。
- `T_side_caseB_facts` (136、v-formula `v=(q^p−1)/(q−1)`): S-side dual `caseB_order_u` も sorry、§13
  cyclotomic 構築要。
- `T_typeII` (1564、14.9): char argument (type-III ⟹ `(v−1)/p≤(u−1)/q`、§5/§11/§13 inner-product)
  は **cite 可能 lemma なし** ((14.8) `key_ratio_inequality_of_caseB_data` は在庫だが片側のみ)。
- `eta_generic_data` (2345): §3 Dade η-grid 整数性。
- `U_cyclic_and_Q_elemAbelian` (3438)/`V_cyclic` (3518): §9/§11 char (docstring 明記)。
- `CaseBContradictionData` (4360): §14.16 L-side β decomp + orthogonality。
- `exists_MHypothesis` (4426/4502): 全 carrier 供給 = type-I M 完全構成 (最深)。

⟹ **残 §16 は全て non-citable な deep §13/§14/§9/§11 partner char theory を一から構築要**で、lane a
(§9-13 char core)・lane b (§12 Dade) と深く重複。lane c の group-theory/arithmetic shaped 生産 frontier
(§8 counting + main_size_bounds 等) は枯渇。これ以上の solo は (a) 同 sorry 再調査 (空転) or (b) §13 char
を lane a と重複構築。**hub/ユーザー判断要** (lane a/b char 成熟を待って cite [[feedback-cite-sorried-lemmas-if-signature-correct]]、
lane c 再配分、or §13 char solo 構築の是非)。[[feedback-flag-poor-progress]] [[cross-lane-sync-via-notes]]

### cont.¹¹ (2026-06-30 lane c=γ /loop): T_typeII (14.9) BG-structural reduction landed + bedrock 独立再確認

**1 genuine reduction landed** (commit `89f71cfc`): `T_typeII` (14.9, S16:1581) の bare sorry を
**BG structural 経路**で de-opacify。教科書の type-III orthogonality contradiction (cite 可能 lemma
無し、cont.¹⁰ で確認) を回避し、`typePData_of_isTypeNonI (T_nonI)` (sorry-free) → `TypePData` →
`isTypeII_of_typePData` (**axiom-clean**, `OddOrder.BG.Ch4.S16`, AxiomsCheck 登録) に T-side
structural inputs を供給。残 obligation = 新 `T_typeII_structural_inputs` (S16:1565、5 連言:
nontrivial core / U commutative / N_G(U)⊄T / T' type-F / F(T')=T_F) に isolate。これは cont.¹⁰ が
「cite 可能 lemma なし」とした T_typeII への、唯一見つかった alternative-route reduction。leaf green。

**main sync** (10 commits, conflict 無): lane-b (β) の L-witness Dade infra 着地 —
`hypothesis_of_typeIData` (S14:159, **sorry-free**: explicit TypeIData → S14.Hypothesis)、
`witness_L_hypothesis_frobenius`/`witness_L_coherent`。**lane b が lane-c の MHypothesis pattern を
mirror 中** (s14 note 明記)。但し全て **L (witness 第二極大) 対象**で、私の deepest sorry
`exists_MHypothesis` は **M (type-I over N_G(V)) の完全構成**を要し直接 discharge せず。

**残 9 sorry を独立 fresh 調査で bedrock 再確認** (cont.¹⁰ 結論を refine):
- **U/V cyclic** (3486/3566): citation 候補 `complement_cyclic_order_dvd` (S14:2343, sorried 但し
  citable) は **frob.complement** 対象 → だが U/V は Frobenius **kernel** (`S_deriv_eq_PU: derivedInG S
  = P⊔U`, `T_deriv_eq_QV: Q⊔V`; `BasicStructureData.UW1_frobenius` で U=kernel/W₁=complement)。
  ∴ complement 経路は**適用不可**、kernel cyclicity は deep §9/§11 char。sorry-free
  `isCyclic_and_card_dvd_of_fpf_conj_elemAbelian` (S14:2298) も rank-≤2 elem-abelian FPF 要 / P は
  rank q (>2) ゆえ不適用。
- **v-formula** (136, `v=(q^p−1)/(q−1)`): §13 cyclotomic 同定 (`hyp.tSide_cyclotomic_quotient_*`
  field 経由)、純算術 shortcut 無し。
- main_size_bounds (k>2pv) / EtaGenericData (§3 Dade) / CaseBContradictionData (§14.16) /
  exists_MHypothesis (~30 field full M 構成) も全て deep、既に minimal isolated obligation
  (de-opacify 余地ほぼ無)。
- **∴ T_typeII は one-off opportunity** (既存 BG structural lemma が alternative route を供給した稀有例)。
  他 8 sorry には対応する shallower-bottoming alternative-route lemma が無く、同種 reduction 不可。

**bedrock 確定**: tractable solo lane-c frontier (group-theory/arithmetic) は枯渇。次は**戦略判断**
(wait-and-cite / 再配分 / §13 char solo 構築の是非) = ユーザーに flag。[[feedback-flag-poor-progress]]
[[scaffold-sorry-free-not-done]] [[s09-is-section7-chirho-complete]] (duplication 回避)

### cont.¹² (2026-06-30 lane c=γ /loop): ユーザー裁定「V-side 構成続行」→ Tdata carrier は**設計上の dead-end** と判明、真の gate = T_typeII (14.9) 深 char

ユーザーが AskUserQuestion で「§16 V-side 構成を続行」を選択 (issue 4002 標準ルール路線)。
最大 item `exists_MHypothesis` (V-side Dade 構成) の forward path を正面調査した結果、
**当初仮説 (base Hypothesis に Tdata carrier 追加) は誤りと判明**:

- **🔑 設計上の意図的非対称** (`FeitThompson.lean:276` docstring 明記): 「**T (larger-κ member) need
  not be type-P₂, so no symmetric Tdata**」。S は maximal pair の smaller-κ member で type-P₂ 固定
  (`S_typeP2` 入力 + `Sdata` carrier)、**T の type-P₂ 性は §14 の結論 (`T_typeII` 14.9)** であって入力でない。
  ⟹ Tdata を入力 carrier として追加すると「T type-P₂」(§14 結論) を入力に格上げしてしまい設計違反。**Tdata
  carrier path は dead-end**。issue 4001 の前 entry (「Tdata carrier 欠如が blocker」) を本 entry で訂正。
- **真の V-side gate = `T_typeII` (14.9)**: V-side 構成は T の type-P 構造を要し、それは `T_typeII`
  (本 iteration で BG-structural reduction 済 → `T_typeII_structural_inputs` の 5 連言) 経由でのみ得る。
  そして 5 連言は **`TypeIIData T` の field そのもの** (`MaximalSubgroupType.lean:208-213`:
  common/U_commutative/normalizer_not_le/derived_typeF/derived_fitting_eq) = 「T は type II (P2≠P1)」
  の genuine §14.9 char。tractable sub-conjunct **無し** (各々が P2-vs-P1 distinction の深 char)。
- **§14.9 char の citability**: 教科書 14.9 証明 (type-III orthogonality contradiction) は §5/§11/§13
  inner-product machinery 依存で、cont.¹⁰ 既述「cite 可能 lemma なし」。⟹ V-side は lane b char 成熟か
  cross-lane signature authoring を要し、structural shortcut が存在しない。

**∴ V-side 構成の正確な構造** (次 iteration の出発点):
1. `exists_typeI_maximal_overNormalizer_V` (S-side `exists_typeI_maximal_overNormalizer_U` S15:609 の
   ~350 行 dual) = V-side type-I maximal over N_G(V) 存在。**T type-P data 経由 (T_typeII gated) + 多数の
   V-side helper (not_normalizer_V_le_T / card_LF_coprime dual / typeI_overNormalizer_V_le_fitting 等)**
   の chain を要す。Tdata でなく T_typeII を上流とする。
2. それを consume して `exists_MHypothesis` の ~35 field を assemble (構造 field + §7 h78 coherence +
   §8 counting carrier、後者は deep)。
⟹ **multi-iteration の V-side helper chain build**。Tdata dead-end を除外できたのが本 iteration の成果。
次 = `exists_typeI_maximal_overNormalizer_V` の helper chain から着手 (T_typeII gated、fresh context 推奨)。
[[feedback-no-avoiding-hard-parts]] [[scaffold-sorry-free-not-done]] [[feedback-flag-poor-progress]]

### cont.¹³ (2026-06-30 lane c=γ /loop): 🎯 「fully-gated」結論は過早だった — TypeIIData harvest で §13.2.a 非-gated 化 (`isMulCommutative_U`)

ユーザーが「待つな・lane c を進めろ」と push (×3)。それを受けて §15/§13.2 の gated 構造事実を**正面から**
attack した結果、**「lane c frontier は fully cross-lane gated」という本 session 前半の結論は過早**と判明
([[feedback-no-avoiding-hard-parts]] の warning 通り、試行不足だった)。

**genuine landing** (commit `100e4d73`, full build 3888 green): **`S15.isMulCommutative_U`** (sorry-free) =
型-P₂ member S の complement U が可換 (Pf 13.2.a)。これまで §16-gated な `basic_structure_gated.U_commutative`
経由でしか得られなかった事実を**非-gated に実証明**:
- **鍵 = sorry-free type determination の harvest**: S は type II (`isTypeII_of_isTypeP2`, sorry-free
  from `S_typeP2`) ゆえ `TypeIIData S` witness `tdata` が**只で手に入る**。`tdata.U_commutative` は
  witness の U の可換性。
- carrier U (=Sdata.U) と tdata.typeP.U は M'=[S,S] 内で M_F=P の complement ⟹ Schur–Zassenhaus
  (`IsComplement'.exists_conj_of_coprime`, |P|⊥|U| from `coprime_card_U_card_P_of_disjoint`) で M'-共役
  ⟹ `isMulCommutative_of_mulEquiv` chain で可換性 transfer。
- 消費者 `typeI_overNormalizer_U_le_fitting:646` の gated 参照を本 lemma に置換。

**⟹ 反復可能な lane-c 技法 (次 iteration の方針)**: **sorry-free type determination が与える
`TypeIIData S` (= `hSII.some`) の field を harvest して gated §13.2 構造事実を非-gated 化**する。
- witness 非依存 field (derivedInG S 関連: `derived_typeF` = `IsTypeF (derivedInG S)`,
  `derived_fitting_eq`) は**直接** citable (transfer 不要、derivedInG S は canonical)。
- U-witness 依存 field (`U_commutative` ✅, `normalizer_not_le` = ¬N_G(U)≤S) は**complement 共役
  transfer** (本 `isMulCommutative_U` pattern)。
- 真に deep な残り = σ-structure (`P_order` |P|=p^q, `P_elementaryAbelian`, `u_bound`, `A0S_TI`) =
  BG §10/§14 σ-theory (docstring「no repo theorem yet」)。これは harvest 不可、別 attack。
次 /loop = TypeIIData harvest で次の gated fact を非-gated 化 (例 `normalizer_not_le` 共役 transfer、
or derivedInG S 系の直接 cite)。[[feedback-no-avoiding-hard-parts]] [[scaffold-sorry-free-not-done]]

### cont.¹⁴ (2026-06-30 lane c=γ /loop): 🛑 HUB 裁定で Tdata dead-end 結論を撤回 — Tdata carrier 着地 (V-side step 2)

**hub 裁定 (issue 4001:116-136 + LAUNCH.md)**: cont.¹²/issue 4001 で「Tdata carrier = 設計 dead-end /
architecturally significant cross-lane infra」を理由に戦略 fork を flag した件、hub が**🛑STOP 条件 (a)
違反 (自クラスタ hard body を gated 理由で放置・relane 要求)** として却下。**「難所回避は無意味」「正面突破せよ」**。

**cont.¹² の dead-end 結論は誤りと確定・撤回**: `T_nonI : IsTypeNonI T → IsTypeP T` ゆえ
**`TypePData T` は存在する** (type-P であって、`FeitThompson:276` docstring の懸念した type-**P₂** 特定性は
TypePData に不要)。当初「T type-P₂ は §14 結論ゆえ Tdata 不可」は type-P と type-P₂ を混同していた。
Tdata carrier の追加先 (base `Hypothesis` = S15_SAndT_Setup:80 / S16_NonExistenceGCore:42) は **lane-c
自身の所有ファイル**で cross-lane 依存ゼロ。

**genuine landing (commit `737a15de`, full build 3888 green)**: base `Hypothesis` に
`Tdata : TypePData T` + `Tdata_V_eq : Tdata.U = V` / `Tdata_W2_eq : Tdata.W1 = W2` を Sdata の dual で追加。
cascade = S15.Hypothesis / Section16TypePStructure / Section16Inputs の 3-field + `_of_components` の
Td params + producer の T-side mirror (`typePData_of_kappaHall_hallComplement` for T を S-side そのまま
mirror)。`Section16TypePStructure:276` の「no symmetric Tdata」docstring も訂正。
**唯一の新 sorry = `hTP2 : IsTypeP2 mp.T`** (producer、= (14.9) T type II。producer は Hypothesis 構築前
ゆえ T_typeII を循環なしに cite 不可、§14.9 gate を単一 isolate)。

**次 /loop = V-side step 3**: `typeII_overNormalizer_frobenius` (S15:1070) / `exists_typeI_maximal_overNormalizer_U`
(S15:609 ~350 行) の **V-side dual を S/U-side mirror で構成** (Tdata を消費)。途中 genuine lane-b char に
当たれば sorried signature cite (hub: 再導出・待機・再配置しない)。multi-iteration。
[[feedback-no-avoiding-hard-parts]] [[hub-check-issue-before-asking-on-scope-violation]] [[scaffold-sorry-free-not-done]]

### cont.¹⁵ (2026-06-30 lane c=γ /loop ×3): V-side helper dual 6 本完成 — assembly 手前まで

hub step 3 (V-side dual 構成) を bottom-up で進め、`exists_typeI_maximal_overNormalizer_V` の **V-side
helper を全て landing** (全 sorry-free・初回 build-green・mechanical S→T mirror、commits `f06417a9`
`f6397634` `4f18c229`):
1. `coprime_card_V_card_Q_of_disjoint` (coprime_card_U_card_P dual)
2. `isMulCommutative_V` (isMulCommutative_U dual、V abelian、IsTypeII T は hypothesis)
3. `not_normalizer_V_le_T` (not_normalizer_U_le_S dual)
4. `exists_conj_typeP_V_of_coprime` (exists_conj_typeP_U_of_coprime dual)
5. `typeI_V_le_fitting_of_coprime` (typeI_U_le_fitting_of_coprime dual、VW₂ Frobenius を
   `typeP_uW1_frobenius hyp.Tdata` で inline 構築)
6. `typeI_overNormalizer_V_le_fitting` (typeI_overNormalizer_U_le_fitting dual)

**次 = assembly `exists_typeI_maximal_overNormalizer_V`** (S15:1005 ~356 行 dual)。⚠ **branches swap**:
S-side の L~S 排除 (Hall-conjugacy via `normalizer_le_of_isHall_subgroupOf_of_conj` [generic] + bdata
card 計算) ↔ V-side では L~T 排除 (N_G(V)⊄T = `not_normalizer_V_le_T`); S-side L~T 排除
(`tConjugate_fitting_data` + `card_Q_eq` |Q|=q^p) ↔ V-side L~S 排除 (要 **新 `sConjugate_fitting_data`
dual** + `card_P_eq` |P|=p^q、gated cite)。intricate ゆえ fresh context で。VW₂ Frobenius は
Tdata から取得済パターン流用可。[[feedback-no-avoiding-hard-parts]] [[scaffold-sorry-free-not-done]]

### cont.¹⁶ (2026-06-30 lane c=γ /loop ×5-6): V-side 主存在定理 + Frobenius-decomp dual 完成

hub step 3 を継続。**V-side 構成の中核を landing** (全 build-green、commits `e3f9e0be` `960c58c3`):
- **`exists_typeI_maximal_overNormalizer_V`** (S15、~150 行 dual、初回 green) = type-II T に対し N_G(V)
  上の type-I maximal L が V⊆L_F で存在。branches swap (L~T=Hall-conjugacy / L~S=order-contradiction)。
  VW₂ Frobenius を Tdata から構築・両 branch 共有。新 sorry = `sConjugate_fitting_data` (tConjugate の
  S-side dual、card_P_eq gated、hub 指示で author)。helper 6 本消費。
- **`p_not_dvd_kernel`** (q_not_dvd_kernel dual) + **`exists_typeIFrobeniusData_W2_le`**
  (exists_typeIFrobeniusData_W1_le dual) = clean mirror。

**残 = `typeII_overNormalizer_frobenius` の V-dual** (S15:1604)。要素:
- `complement_card_eq_pq` の V-dual (order pq with W₂)。S-side は sorry-free だが gated lemma
  (`complement_le_QW2` [Huppert]、`Q_W2_structure`、`complement_inf_Q_structure`) に依存
  ⟹ V-dual は **gated dual を author 要**: `complement_le_PW1` (Huppert: W₂◁E→E≤PW₁、normalizer_W2 経由)、
  `P_W1_structure`、`complement_inf_P_structure` (全 sorried、hub 指示 cite)。
- **`TypeIOverNormalizerDataV` struct** (TypeIOverNormalizerData の V-side、normalizer_V_le_L /
  W₁^y conjugate / etc.)。
- `typeI_overNormalizer_complement_V` + `typeII_overNormalizer_frobenius_V` assembly。
これで exists_MHypothesis の structural field (complement_card_eq_pq = e=pq) が供給可能に。
deeper char (h78/§8) は別 (MHypothesis carrier に isolate 済)。[[feedback-no-avoiding-hard-parts]]
[[hub-check-issue-before-asking-on-scope-violation]] [[scaffold-sorry-free-not-done]]

### cont.¹⁷ (2026-06-30 lane c=γ /loop ×6-7): 🎉 V-side group-theory 構造入力 完成

hub step 3 (V-side 構成) の **group-theory 部分を完遂** (commit `84ca5187` 他)。本セッション通算の
V-side landing (全 build-green、~13 lemma/struct + Tdata carrier):
- **carrier**: Tdata (base Hypothesis)。
- **helper dual 6**: coprime_card_V_card_Q / isMulCommutative_V / not_normalizer_V_le_T /
  exists_conj_typeP_V_of_coprime / typeI_V_le_fitting_of_coprime / typeI_overNormalizer_V_le_fitting。
- **主存在**: `exists_typeI_maximal_overNormalizer_V` (N_G(V) 上 type-I maximal、branches swap)。
- **Frobenius decomp**: p_not_dvd_kernel / exists_typeIFrobeniusData_W2_le。
- **complement order**: `complement_card_eq_pq_V` (= pq、exists_MHypothesis の e=pq input)。
- **authored gated dual** (sorried、deep §13 isolate): sConjugate_fitting_data / complement_inf_P_structure
  / complement_le_PW1 / P_W1_structure (全て tConjugate/complement_le_QW2/Q_W2_structure 等 gated S-side の対称)。

**⟹ V-side group-theory は出尽くした**。残 exists_MHypothesis (~35 field) は:
1. **structural field wiring** (M/K/normalizer_V_le_M/typeIHyp/complement_card_eq_pq) = 上記 V-side
   pieces を MHypothesis に配線 (機械的、TypeIData M → S14.Hypothesis M via hypothesis_of_typeIData)。
2. **deep char field** (h78 coherence / §8 counting / Mset/tau/betaM grid 等) = lane a/b char keystone
   gated、MHypothesis carrier に isolate。
次 = (1) の structural wiring で exists_MHypothesis を de-opacify (bare sorry → 構造 field 充足 + char
field isolate)、or TypeIOverNormalizerDataV packaging。[[feedback-no-avoiding-hard-parts]]
[[scaffold-sorry-free-not-done]] [[hub-check-issue-before-asking-on-scope-violation]]

**✅ UPDATE (同 /loop): hub V-side directive 完遂** (commit `06509fc6`)。`TypeIOverNormalizerDataV`
struct + `typeI_overNormalizer_complement_V` (generic `exists_mem_conj_W2_le_of_dvd_card` を (P,W1,E)
再利用) + `typeII_overNormalizer_frobenius_V` assembly を landing。⟹ hub 指示
「typeII_overNormalizer_frobenius / exists_typeI_maximal_overNormalizer_U の V-side dual」**両方完成**。
V-side 構造 producer 完備。残 = exists_MHypothesis (S16:4547、bare sorry) の wiring: typeII_overNormalizer_frobenius_V
で M/complement_card_eq_pq 供給 + typeIHyp (M type-I → hypothesis_of_typeIData) + 残 deep char field
(h78/§8、lane a/b char keystone gated、carrier isolate or sorried cite)。これは 35-field assembly
ゆえ char sorry を多数導入する点に注意 (de-opacify は genuine だが optically sorry 増)。

### cont.¹⁹ (2026-06-30 lane c=γ): ⚠ HUB tick² 修正 — unsound Tdata spine carrier 撤回、reconciled_typePData_T へ

**cont.¹⁴ の「Tdata dead-end 撤回」は誤りで、hub tick² (issue 4001) が再 HOLD・修正要求**。私が `Tdata`
carrier を base Hypothesis + §16 spine constructor `section16TypePStructure_of_isMinimalSimpleOdd`
(従来 sorry-free) に追加し、supply に `have hTP2 : IsTypeP2 mp.T := sorry` を挿入したのが問題:
- **FT spine sorry regression** (merge_monitor HOLD、hub が main マージ abort)。
- **型が逆**: `T_typeII` (14.9) が産むのは `TypeIIData T` (type-II)。`IsTypeP2 T` は strictly 強く**一般に偽**
  ⟹ sorry が埋まらない＝**Tdata dead-end の裏口再導入**。cont.¹² の正しい判断 (type-P/type-P₂ 区別) を自分で覆した。
- d 所有 §16 carrier の非-additive 改変 (`FeitThompson:276` docstring 削除)。

**修正 (commit `8aa7b8b4`, revert 737a15de + helper refactor, full build 3889 green)**:
- Tdata carrier + spine の hTP2 sorry **撤回**、`FeitThompson:276`「no symmetric Tdata」docstring **復元**、
  **spine を sorry-free に戻した**。
- V-side helper の T-side type-P 源を **off-spine の honest obligation `reconciled_typePData_T`**
  (`∃ data : TypePData T, data.U = V ∧ data.W1 = W2`、TRUE な §13 reconciliation、IsTypeP2 と違い偽でない) に変更。
  `Q_inf_V_eq_bot_of_reconciled` で hdisj factor。
- **V-side helper 群 (existence/共役/fitting/complement/typeII_overNormalizer_frobenius_V) は全て残存** (hub 承認、build-green)。

**教訓**: carrier を「構成可能」と確かめる前に上に積むな ([[scaffold-sorry-free-not-done]] doneness=carrier 構成可能性)。
hub 指示が自分の careful 分析 (cont.¹²) と矛盾したら盲従でなく矛盾を flag すべきだった。
**残 = exists_MHypothesis wiring は reconciled_typePData_T (off-spine) + TypeIIData T 経由で**
(hub tick²: 「TypePData T/IsTypeP2 T は使わない、TypeIIData T 経由」)。
[[scaffold-sorry-free-not-done]] [[hub-check-issue-before-asking-on-scope-violation]]

### cont.²⁰ (2026-06-30 lane c=γ /loop): MHypothesis carrier −3 — W=W₁×W₂ cardinalities を base から honest 化

cont.¹⁹ の方向 (spine 改変でなく carrier 構成可能性を上げる) に沿い、**spine を一切触らず** carrier の
deep-looking field を 3 本 honest に de-gate (commit `b82d7c9e`, full build 3889 green):

- `MHypothesis` (S16:1593) の `card_W_eq` (|W|=pq) / `card_W1_add_W2_eq` (|W₁|+|W₂|=p+q) /
  `W_set_nonempty` (W∖(W₁∪W₂)≠∅) の 3 field を**撤去**。これらは「§13-14 σ-prerequisite」として
  exists_MHypothesis に isolate されていたが、実は base `Hypothesis` の elementary consequence と判明。
- 新規 sorry-free 補題 (S15_SAndT.lean、base `Hypothesis` 上):
  - `S15.card_W_eq_pq`: W=W₁⊔W₂ の内部直積 (`W1_commutes_W2`+`W1_inf_W2_eq_bot` →
    `card_sup_eq_mul_of_le_normalizer_of_disjoint`、commute から W₁≤N(W₂) を `mem_normalizer_iff` で構築)。
  - `S15.card_W1_add_W2`: prime data から自明。
  - `S15.W_sdiff_nonempty`: `Set.ncard_le_ncard`+`ncard_union_le`、(p−1)(q−1)>0 を omega。
- §16 第8 TI-counting の 3 消費点 (orbit measure 2949 / W-set ncard 2961 / hWcardR 2974) を
  `Mdata.*` field から `S15.*` lemma (`hyp.base` 適用) に rewire。**lemma 文 = 旧 field 文と同一**ゆえ
  drop-in (omega/ring 文脈不変)。

**意義**: exists_MHypothesis の obligation −3 (bare sorry 数は不変、3 field が proven 化 = carrier 構成
可能性 ↑、CLAUDE.md doneness 判定の本筋)。sorry regression 0 (sound REMOVAL、cont.¹⁹ の unsound
ADDITION と逆)。**残 σ-carrier (8→5)**: P_isTI/Q_isTI (§8 TI)、card_normalizer_P/Q (|N(P)|=|P|uq 等
§13-14)、W_normalizer_V (exceptional-set normalizer=W §13) — これらは base から自明でなく要 char/σ。
次候補 = (a) 同様に base/Sdata から derivable な残 carrier field の探索 (P_isTI が Frobenius kernel TI
として Sdata/typeP から出るか調査) or (b) exists_MHypothesis の structural field skeleton
(M/K/typeIHyp/e=pq、T_typeII sorried cite + V-side producer)。[[scaffold-sorry-free-not-done]]
[[feedback-no-avoiding-hard-parts]]

### cont.²¹ (2026-06-30 lane c=γ /loop): σ-carrier 残 field の gate を**定性的に確定** — clean structural win は枯渇、残は deep §13 char/(13.10)・§7 coherence・BG FittingIsTI

cont.²⁰ の次候補 (a)(b) を正面調査し、**残 MHypothesis σ-carrier field の gate を 1 つずつ確定**
(これで future iteration の re-investigation を防ぐ — anti-spin)。結論: **W-cardinality cluster
(cont.²⁰) が唯一の clean sorry-free structural win で、残 σ-field は全て deep に gated**:

- **`card_normalizer_P_eq`** (|N(P)|=|P|uq): 構造核 `N_G(P)=S` は `maximalSubgroup_eq_normalizer_maxNilpotentNormalHall`
  (S14:2813) で sorry-free。order `|S|=|W₁||U||P|` も recipe 在 (S15:1171)。**但し |U|=u に `c_eq_one`
  (13.12) を要し、`c_eq_one` は S15_SAndT_Setup:1046 で sorried** ⟹ clean でない (carrier field を
  cite すると normCascadeData body-sorry-free が regress)。
- **`card_normalizer_Q_eq`**: Q-dual。`reconciled_typePData_T` (sorried §13) + `d_eq_one`(dual) gated。
- **`P_isTI`/`Q_isTI`**: BG `FittingIsTI` 経由 (`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`
  S16_MainResults:1855) = lane d §15-16。TypePData に P⋊U Frobenius 構造は無 (derived_complement のみ)。
- **`W_normalizer_V`**: TypePData.normalizer_V 在だが Sdata.W2=W2 / Sdata.W=W reconciliation gated。
- **`h78`** (§7 M-coherence): citable producer 無 (S09 に Hypothesis78 struct のみ)。lane a/b §5-9 coherence。

**🔑 c_eq_one (13.12) の正確な bottom-out** (textbook 04.15:206 + Coq PFsection13:307-322 co-read):
- **(13.11) m-bounds は formalized sorry-free**: `numeric_bounds` (S15_SAndT_Setup:1029) =
  m>8/10 (q≥7) / m>7/10 (q≥5) / m>49/100 (q=3)。`m_eq` 経由の genuine 算術。
- **gate = (13.10) analytic inequality** `u/c > (p²−1)/6` (= `numeric_bounds` q=3 branch の sorry@1040、
  norm cascade (13.5)-(13.10) の終端) + **W₁-FPF-on-C → c odd ≥ 2q+1**。
- textbook 証明: c≠1 仮定 → c≥2q+1 → (13.10) で m< uq/(cp^{q-1}) bound → p=3 で q=5 (13.11.a)、
  p≥5 で q=3 + c∈{7,≥13} → 全て (13.11) m-bound と矛盾。Coq の reducible case (13.3.b) は
  Frobenius PU の `cent_semiregular` で C=1 (別 case)。

**⟹ 次 iteration の genuine target (fresh context)**: **c_eq_one を de-opacify** — bare sorry を
(i) (13.10) を named sorried lemma 化 (cite) + (ii) W₁-FPF-on-C 確立 + (iii) numeric_bounds + 算術
case analysis で wire し、真の gate (13.10) に isolate。これで c_eq_one が honest 化 →
card_normalizer_P_eq が (13.10)-conditional に。**(13.10) 自体の formalization (norm cascade
(13.5)-(13.10)) はさらに deep = lane a §13 char と重複** ⟹ (13.10) は cite に留め body は埋めない
([[feedback-cite-sorried-lemmas-if-signature-correct]])。[[scaffold-sorry-free-not-done]]
[[feedback-no-avoiding-hard-parts]] [[feedback-flag-poor-progress]]

### cont.²² (2026-06-30 lane c=γ /loop): c_eq_one は cont.²¹ 想定より深い (要 13.3.b char case split) — 方針を hub directive (exists_MHypothesis skeleton) に切替、index bridge を landing

cont.²¹ の c_eq_one de-opacify plan を着手したが、**c_eq_one は cont.²¹ 想定より深いと判明** (Coq
PFsection13 再読): textbook 04.15:208「By (13.3.b), we may assume the hypothesis of (13.10) holds」
= c_eq_one は **char-theoretic case split** を要す:
- **reducible core case** (`~~ has irrIndH calS`): C=1 via Frobenius PU `cent_semiregular` (Coq
  `FTtypeP_no_Ind_Fitting_facts` = 13.3.b)。
- **irreducible case**: (13.10) analytic + (13.11) numerical。
case split 自体 (`has irrIndH calS` = 型-P char family の irreducible induction 有無) が deep §13
char ⟹ c_eq_one は lane-c-solo wireable でない (lane a §10-13 char と重複)。FPF→c bound piece も
IsFrobeniusGroup を ↥(C⊔W₁) ambient + subgroupOf で組む friction 大。

**⟹ 方針切替: hub cont.¹⁹ directive (exists_MHypothesis structural skeleton) に従う**
([[feedback-gated-endpoint-skeleton-pattern]] = gated endpoint を structural skeleton で前倒し)。
**landed (commit 次): `typeIFrobenius_kernel_index_eq_complement`** (S15_SAndT、sorry-free) =
任意 `TypeIFrobeniusData M` で `|M : M_F| = |complement|` (`IsComplement'.symm.index_eq_card` +
`typeF.H_eq`)。V-side `complement_card_eq_pq` (=pq) と合わせ exists_MHypothesis の `e=|M:K|=pq`
(`e_eq_index`+`complement_card_eq_pq` field) を供給する skeleton 第1 piece。

**残 σ-frontier 確定** (cont.²⁰-²² 総括): clean independent structural win = W-cardinality のみ。
残は全て (a) deep char (c_eq_one=13.3.b+13.10、h78=§7 coherence、lane a/b 共有) / (b) gated-endpoint
scaffold (exists_MHypothesis skeleton、index bridge が初手) / (c) BG FittingIsTI (P/Q_isTI、lane d)。
**次 = exists_MHypothesis skeleton の structural field を順次供給** (M/K/typeIHyp via
exists_typeI_hypothesis + V-side producer、e=pq via 本 index bridge、T_typeII sorried cite)、char
field は named obligation に isolate。[[scaffold-sorry-free-not-done]] [[feedback-no-avoiding-hard-parts]]

### cont.²³ (2026-06-30 lane c=γ /loop): exists_MHypothesis の structural 半 = `exists_M_structural` 完成 (sorry-free)

**landed (commit `723b897c`)**: `exists_M_structural` (S15_SAndT、sorry-free) = `IsTypeII hyp.T →
∃ M (typeIHyp : S14.Hypothesis M), M ∈ maximalSubgroups ∧ N_G(V) ≤ M ∧ |M : M_F| = p q`。
`typeII_overNormalizer_frobenius_V` + `S14.exists_typeI_hypothesis` + index bridge
(`typeIFrobenius_kernel_index_eq_complement`) を組立。**exists_MHypothesis の structural 半
(M/K=M_F/typeIHyp/e_eq_index/complement_card_eq_pq) を 1 lemma に集約済**。

**⟹ exists_MHypothesis 残 = char carrier ~25 field** (h78/Mset/tau/tau1/psi/betaM/betaSigns/betaGrid/
psi_tau1_*/h78_*/P_isTI/Q_isTI/card_normalizer_P,Q/W_normalizer_V/G0*)。これらは deep §7 coherence
(h78、producer 無)・§8 σ・§13 char で **lane c solo では body 埋まらず**。

**次 iteration の wiring 設計 (fresh context、mechanical だが voluminous)**: spine sorry regression
回避のため inline-sorry でなく **`MCharData` bundle 方式**:
1. `structure MCharData (hyp) (M K : Subgroup G) (typeIHyp : S14.Hypothesis M) (e k : ℕ)` =
   MHypothesis の char field ~25 を parameterized copy (self-ref M/typeIHyp/e/k を param 化、
   field 型は MHypothesis L1606-1719 から literal copy)。
2. `exists_MCharData : ∀ …, Nonempty (MCharData …) := sorry` (1 named obligation = deep char 全体)。
3. `exists_MHypothesis := exists_M_structural で structural obtain + exists_MCharData で char obtain →
   32-field assembly`。⟹ spine bare-sorry 1→1 (exists_MHypothesis sorry → exists_MCharData sorry)、
   structural 半は proven 化 = de-opacify。[[feedback-gated-endpoint-skeleton-pattern]]
   [[scaffold-sorry-free-not-done]] [[feedback-no-avoiding-hard-parts]]

### cont.²⁴ (2026-06-30 lane c=γ /loop): 🎯 戦略 REFRAME — lane-c の真の remaining work は §13 char (lane-c OWNED, §5-9 上、blocked でない)

h78 構成可能性を正面調査し、戦略を reframe (複数 iteration の「char は lane-a 共有/gated」思考を修正):

- **h78 (Hypothesis78 for M) は lane-B coherence gated と確定**: `Hypothesis78` (S09:1433) は coherent
  ν-isometry + `Hypothesis76` ((7.6) coherent family) + (7.8.c.i) certificate を要す。`S14.toHypothesis71`
  は Hypothesis71 を構成するが Hypothesis78 producer は無 ⟹ §5-8 coherence (`frobenius_typeI_coherent`
  → `sibleyTarget_frobI` S14:1289 sorry + (6.8) lane-B) gated。**lane-c solo 構成不可**。
- **MCharData bundle は数学価値低 (sorry 再編成)**: structural 進捗は `exists_M_structural` が既に捕捉
  (carrier 構成可能性=doneness 判定済)。bundle は spine sorry を relocate するだけ ⟹ 優先しない
  ([[feedback-no-spine-sorry-verify-carrier]] hub cont.¹⁹ directive と私の技術分析が齟齬、本 entry で flag)。
- **🎯 REFRAME: lane-c の真の deep work = §13 char (13.5-13.15)**。これは **lane-c OWNED**
  (`S15_SAndT_Setup.lean` = 教科書§13「The Subgroups S and T」、lane-a の S10-S13 は §8-§11 で別)、
  **§1-9 machinery 完了済の上に積める** (lane-a blocked でない)。§13 norm cascade infra は既に大量実装
  (`innerSum_self_eq_sum_normSq`/`sum_normSq_eq_card_mul_inner`/`induce_one_apply`/Frobenius perm-char
  vanishing 等、S15_SAndT_Setup:442+)。(13.11) numeric_bounds も済。**残 gate = (13.10) analytic
  inequality (norm cascade 終端) → c_eq_one (13.12) → card_normalizer_P/Q + §16 数値矛盾**。

**⟹ 次 iteration = §13 char を正面から engage** (fresh context): (13.5)-(13.10) norm cascade を
既存 infra + §5-9 Dade-norm 上に構築し (13.10) analytic inequality (u/c > (p²-1)/6) に到達 →
c_eq_one。heavy・multi-iteration だが lane-c の genuine 本丸。「ask/wait/re-org」でなく hard part を
正面突破。[[feedback-no-avoiding-hard-parts]] [[scaffold-sorry-free-not-done]] [[feedback-flag-poor-progress]]

### cont.²⁵ (2026-07-01 lane c=γ): §13 norm cascade を engage — **算術層 (13.6/13.7/13.8/13.10/13.11) 完備**、残 = (13.5) chiRho engine

ユーザー裁定「quick win は基準でない、目的にかなう deep work を難しくても正面から」(規約 = CLAUDE.md
「進捗の測り方」+ [[feedback-quick-win-not-a-criterion]]) を受け §13 norm cascade を engage。
**cascade 構造を完全 map**: (13.5) engine → (13.6-13.9) norm bounds → (13.10) analytic ineq →
numeric_bounds (13.11) → c_eq_one (13.12)。

**算術層は完備** (全 sorry-free、S15_SAndT_Setup):
- (13.5.c) `sum_normSq_erase_one_ge_of_const_on_subgroup` ✅ (既存)
- (13.6) `caseB_lambda_norm_core` ✅ **landed** (commit `0abe3a3b`、caseB_quadratic_nonneg で交差項 q²(...)≥0)
- (13.7) `caseB_eta_norm_core` ✅ (既存、Parseval 形)
- (13.8) `caseB_eta01_norm_core` ✅ **landed** (本セッション、δ=±1、b=δα(1) で caseB_quadratic_nonneg)
- (13.10) `analytic_inequality_arith` ✅ (既存)、(13.11) `m_value_*`/`numeric_bounds` ✅ (q=3 branch のみ (13.10) gated)

**⟹ 残る §13 数学 = (13.5) chiRho engine のみ** (character theory、deep・multi-iteration):
- **(13.5.a)** point formula `χ(x) = (a/‖ζ₁‖²)ζ₁(x) + α(x)` on H# — (7.7.a) `chiRho_explicit_formula`
  (S09:1109、lane b 済) を (S, H#) に適用。
- **(13.5.b)** norm expansion — ζ₁ が S−H で消える + Res ζ₁ ⊥ α (P-kernel) の 2 char 事実 + 代数展開。
- **engine の foundation build plan** (次の deep work): `S04.Hypothesis G (H#) S` ((2.2) Dade hyp、
  S04:192) を構築 → `Hypothesis71 (S, H#)` → coherence は `S_coherent` (S15:397、citable、
  sibleyTarget_S/(6.8) gated) → `Hypothesis76` bridge → chiRho。⚠ S04.Hypothesis (S,H#) は H# TI +
  centralizer 半直積構造 (centralizer_eq_sup/disjoint/coprime) を要し major build。§8 TI 入力
  `H_sharp_ti : IsTISubset (sharpImage H) L` は `S08_CoherenceCorePart1:3279` に在 (bridge 要)。
- **(13.9)/(13.10.3)** = 構造 counting (H# TI で disjoint union G = {1}⊔G₀⊔(H#)^G⊔(Q#)^G、§8)。

次 = (13.5) engine の foundation (S04.Hypothesis for (S,H#)) を構築開始。算術層が完備ゆえ engine が
landing すれば (13.6-13.8) → (13.10) → c_eq_one が連鎖。[[feedback-no-avoiding-hard-parts]]
[[feedback-cite-sorried-lemmas-if-signature-correct]] [[scaffold-sorry-free-not-done]]

### cont.²⁶ (2026-07-01 lane c=γ /loop ×多数): 🎉 (13.5) chiRho engine を**完全結線** (foundation→H71→H76→χ=χ^ρ→base decomp)

ユーザー裁定 (quick win 不問・hard work 正面) を受け §13 (13.5) chiRho engine を一から構築完遂。
**全 sorry-free** (§8 TI obligation modulo)、各 commit で landing、S15_SAndT_Setup:

1. **算術層** (13.6/13.8 core): `caseB_lambda_norm_core`/`caseB_eta01_norm_core` (caseB_quadratic_nonneg)。
2. **(13.5.b) 分解部品**: `sum_normSq_real_smul_add` (Parseval 代数核) + `sum_normSq_sharp_eq_total_sub_one`
   (fact1 ζ₁-norm) + `sum_mul_conj_sharp_eq_neg_of_inner_zero` (fact2 cross-term)。
3. **Dade foundation**: `H_sharp_dadeHypothesis` = S04.Hypothesis for (S,H#) via `S04.Hypothesis.of_isTISubset`
   (§8 TI 入力 = `H_sharp_isTISubset`(8.5.a)/`S_normalizes_H_sharp` を named obligation 化、構造入力
   H#⊆G#・H=PC≤S は proven)。
4. **Hypothesis71**: `H_sharp_hypothesis71` (Dade map = `fullDadeIsometryData`、hconj = of_forall_H_eq_bot)。
5. **Hypothesis76**: `H_sharp_hypothesis76` via `S09.Cert.hypothesis76OfDade` (issue-1013 = (7.7.a) 証明書込で
   (7.1) data のみから構築)。import S09_CertificateDischarge。instance は FiniteInduce scope+[Inv|G|] param。
6. **χ=χ^ρ bridge**: `chiRho_eq_self_of_H_eq_bot` (TI 局所 H(a)=⊥ で ρ-map 恒等)。
7. **(13.5.a) base decomp**: `H_sharp_chiRho_eq_explicit` = χ(x) = ∑_{i≥1}(c̄_i/‖ζ_i‖²)ζ_i(x) on H#
   (bridge .symm.trans chiRho_explicit_formula、H76.hyp71=H71 defeq)。

**残 (13.5.a)**: base decomp から **ζ₁ 抽出 + P-kernel tail を α に grouping** (textbook の orthogonality
仮説 χ⊥(ζ_i-ζ_0)^τ で S₁ 中間項 c_i=0、P⊆ker tail = α、α(1) ≡0 mod q)。これが intricate な reorganization。
完成すれば `tiSubset_character_orthogonality` (13.5 producer) → (13.6-13.8) [arith 済] → (13.9)/(13.10) →
numeric_bounds [済] → c_eq_one。[[feedback-no-avoiding-hard-parts]] [[scaffold-sorry-free-not-done]]

### cont.²⁷ (2026-07-01 lane c=γ /loop): (13.5.a) reorganization の sub-plan 確定 (base decomp は landing 済)

base decomp (`H_sharp_chiRho_eq_explicit`: χ(x) = ∑_{i∈Ioi 0}(c̄_i/‖ζ_i‖²)ζ_i(x) on H#) から
(13.5.a) full form `χ = (a/‖ζ₁‖²)ζ₁ + α` (P off ker α) への reorganization の precise sub-plan:

**🔑 kernel insight**: H76 family ζ_i = Ind_H^S θ_i (θ_i∈Irr H, distinct, exists_distinct_induced_family)。
P◁H (H=PC≤S≤N(P)、P=S_F)。**P⊆ker(Ind_H^S θ) ⟺ P⊆ker θ** ゆえ family は 2 群に分割:
S₁ middle = {Ind θ : P⊄ker θ} (P⊄ker)、tail = {Ind θ : P⊆ker θ}。

**sub-steps**:
1. (13.5) hypothesis χ⊥(ζ_i-ζ_0)^τ for S₁ middle (2≤i≤n) ⟹ c_i = cCoeff χ i = 0 ⟹ middle 項 drop
   (Finset.sum_subset / filter で zero 項除去)。
2. i=1 (distinguished ζ₁) を Finset.add_sum_erase 等で抽出 → (c̄_1/‖ζ_1‖²)ζ_1。
3. **α := ∑_{tail}(c̄_i/‖ζ_i‖²)·Res_H ζ_i** (ClassFunction ↥H、tail を H に制限)。各 Res_H(Ind_H^S θ) (tail) は
   P⊆ker (θ が P⊆ker ゆえ) ⟹ α の P⊆ker (= `alpha_kernel_contains_P`)。textbook: 「(1/‖ζ_i‖²)Res_H ζ_i is a
   character of H having P in its kernel」(13.5.a 証明)。
4. point_formula: χ(x) = (a/‖ζ_1‖²)ζ_1(x) + α(x) on H# (steps 1-3 合成、a = c̄_1)。
5. norm_formula (13.5.b): `sum_normSq_real_smul_add` (Parseval核) + fact1/fact2。
   alpha_norm_bound (13.5.c): `sum_normSq_erase_one_ge_of_const_on_subgroup` (α const on P から、step 3 で取得)。

**⟹ 全部品は landing 済**: base decomp + facts1/2 + Parseval核 + alpha bound 補題。残=上記 1-4 の組立
(kernel partition の Lean 化が核心: P⊆ker(Ind θ)⟺P⊆ker θ + tail の Res_H が P⊆ker)。multi-step だが
全 prerequisite 在庫。fresh context で producer 組立を engage。[[feedback-no-avoiding-hard-parts]]
[[scaffold-sorry-free-not-done]]

**🔑 kernel lemma 確認 (cont.²⁷ 追記)**: `subsetCharacterKernel_induce_of_subgroupOf`
(S03_PreliminaryCharacter:618、Pf (1.6.a) **forward**: A⊴G, A≤H, A⊆ker θ ⟹ A⊆ker(Ind_H^G θ)) が
**在庫** = step 3-4 の核心。これで α=∑_tail Res_H(Ind θ_i) (P⊆ker θ_i) の **P-const** (α(p)=α(1) on P,
alpha bound `sum_normSq_erase_one_ge_of_const_on_subgroup` の入力) が得られる: P⊆ker(Ind θ)
[forward lemma] ⟹ Ind θ が P 上 const ⟹ Res_H も。converse (1.6.a 逆) は未形式化だが**不要**
(tail の forward だけで足りる)。**⚠ 注意**: H76 family は θ_i : ClassFunction ↥(H.subgroupOf S) で
induction は ↥S 内 (Ind_K^L, K=H.subgroupOf S, L=S) ⟹ partition/orthogonality/α 構成は
subgroup-of-S setup での careful work。次 iteration = producer 組立 (step 1-4) を engage。

### cont.²⁸ (2026-07-01 lane c=γ /loop): (13.5.a) point-formula 算術核 LANDED (sorry-free)

`H_sharp_point_formula` (S15_SAndT_Setup, commit 7cea5ee8) = (13.5.a) の**代数核を証明**。
H^# 上で `χ(a:G) = (c̄_{i₁}/‖ζ_{i₁}‖²)ζ_{i₁}(a) + ∑_{i∈filter(P⊆ker ζ_i)(Ioi 0)}(c̄_i/‖ζ_i‖²)ζ_i(a)`。
証明 = base decomp `H_sharp_chiRho_eq_explicit` → `Finset.add_sum_erase` で i₁ 抽出 →
`Finset.sum_filter_add_sum_filter_not` で P⊆ker / P⊄ker 分割 → middle (P⊄ker, ≠i₁) を
直交仮説 `hmiddle` (cCoeff χ i=0) で `Finset.sum_eq_zero` drop → `filter_erase`+`erase_eq_self`。
**パラメータ**: distinguished index `i₁` (`hi1`: 0<i₁, `hi1_ker`: P⊄ker ζ_{i₁}), 直交 `hmiddle`
(∀ i, 0<i → i≠i₁ → P⊄ker ζ_i → cCoeff χ i=0)。α = RHS の tail Σ (P⊆ker, pointwise 値)。

**残 (13.5)**: (b) norm formula = ‖χ‖²_{H#} を point formula + facts1/2 (`sum_normSq_sharp...` /
`sum_mul_conj_sharp...`) + Parseval 核 (`sum_normSq_real_smul_add`) で展開 (κ²‖ζ₁‖²+2κRe(...)+‖α‖²)。
(c) alpha_norm_bound = α P-const (各 tail ζ_i が P⊆ker ⟹ pointwise const) + `sum_normSq_erase_one_ge...`。
全 prerequisite landing 済 = 次 increment は (13.5.b) 組立。[[scaffold-sorry-free-not-done]]
