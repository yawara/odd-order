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
