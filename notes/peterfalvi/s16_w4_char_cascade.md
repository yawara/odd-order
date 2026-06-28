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
