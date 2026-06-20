# Pf §10–§13 character bridge — Lane B 再開 roadmap (gate #3 proper)

> 2026-06-20 Lane B 再開時の現地調査結果 (正本)。ユーザーが「§11-13 spine 着手」を選択
> ((6.8) capstone 締結後)。本 note = §11-13 character theory を honest に閉じるための設計・API 在庫・攻略順。
> 上位文脈 = 記憶 [[ft-endgame-two-poles]] [[peterfalvi-s10-13-gated-on-bg-spine]]、
> Lane H 視点の正本 = [`s10_13_maximal_structure.md`](s10_13_maximal_structure.md)。

## 0. 現在地 (2026-06-20)

- **(6.8) `sibleySetup_is_coherent` DONE** (§8 唯一 sorry 消滅、実 sorry 138)。
- §10-13 の lane 分担: **§10 (S10) = Lane H** (BG §16 cite/wiring) / **§11-13 (S11/S12/S13) = Lane B 領域**。
- §11-13 (~25 sorry) は **G2 = Pf §3-8 char API** に gate。その 2 半分:
  - ① (6.8) coherence producer = ✅ DONE。
  - ② **gate #3 = ω/η/μ/ν/σ index 族 + σ/τ₁ の §5/§6 materialization**。
    S05 ω-grid (`omegaGrid`/`omegaSigmaGrid`/`sigmaIntegral`) は ✅ 全 sorry-free。
    **欠けているのは「§10 carrier (`Hypothesis M`) を §5/§6 の ω/μ machinery に接続するブリッジ」** = gate #3 proper。
- ⚠ **「S11-13 の sorry 除去 ≠ 進捗」** ([[scaffold-sorry-free-not-done]])。carrier の opaque Prop を vacuous に
  埋めるのは scaffold。doneness = carrier 材料化 (real 恒等式 + 実構成)。

## 1. §10 の数学 (Pf §12 = pp.58-63、原文 `references/peterfalvi/04.12_*.mmd`)

`M` = type III/IV/V maximal、`M' = [M,M]`、`W = W₁ × W₂` cyclic、`τ` = Dade isometry rel `(A₀(M),M,G)`。

| Pf | 内容 | S12 行 |
|---|---|---|
| (10.1) | Hypothesis (setup) | 86 (`Hypothesis M`, ✅materialized) |
| (10.2) | ∃ ζ ∈ S∩Irr M, ζ(1)=w₁ | 286 (sorry) |
| (10.3) | w₂ prime; d=μ_ij(1) 独立, δ=δ_j 独立, d>1, n=(d-δ)/w₁∈ℕ | 295 (sorry) |
| (10.4) | Hypothesis (a): ζ,d,δ,n + τ₁ 拡張 | 271 (`CoherentHypothesis`) |
| (10.5) | α_ij=μ_ij-δμ_i0-nζ, Supp(α_ij)⊆A₀(M), α_ij^τ formula | 307 (sorry) |
| (10.6) | τ₁ images, ζ^τ₁ norm bound | 318 (sorry) |
| (10.7) | type II ⟹ [S,S] Frobenius kernel S_F | 339 (sorry) |
| (10.8)★ | **S not coherent** (keystone) | 348 (sorry) |
| (10.9) | w₁<w₂ ⟹ (μ₀-ζ)^τ=Σω_i0^σ-χ, χ⊥(IrrW)^σ, ‖χ‖²=1 | 358 (sorry) |
| (10.10) | no type V maximal (via (10.8): type V ⟹ S coherent、(6.8)/(6.4)/(6.5) 使用) | 368/378 (✅body sorry-free, 依存 sorry) |
| (10.11) | case(b) ⟹ \|W₁\|,\|W₂\| prime; type II ⟹ H elem ab p^q | 425 (✅body sorry-free, 依存 sorry) |

**依存連鎖** (lane-f POLE-1 への接続): `theorem88_caseB_prime_orders` (✅body) → `no_typeV_maximal` (✅body)
→ (10.8) `S_not_coherent` + (10.10.x) `typeV_forces_coherence` (両 sorry) → ⟹ **(10.8)/(10.10.x) を閉じれば
lane-f の POLE-1 `section16TypePStructure` の primes 残 sorry も honest 化**。

## 2. carrier de-opaque plan (`CharacterParameters`, S12:241)

現状 = **scaffold**: real field (`zeta`/`d`/`delta`/`n`/`w2_prime`/grid `mu`/`omegaSigma`/`alpha`) と
**11 opaque Prop** (`zeta_irreducible`/`degree_independent`/`delta_independent`/`n_formula`/`alpha_formula`/
`alpha_tau_formula`/`mu_tau1_formula`/`zeta_tau1_norm_bound`/`orthogonality_w1_lt_w2`/
`typeV_parameter_formula`/`typeV_coherence_formula`) が混在。**producer 未存在** (全定理 `∃ params, sorry`)。

**模範 = `S15.Hypothesis`** (S15_SAndT:73-170、commit c724456 で de-opaque 済): real grid
`omega`/`eta`/`mu`/`nu` + honest 恒等式 field `eta_eq_tau_omega`/`mu_definition`/`nu_definition`。
→ `CharacterParameters` も同様に opaque Prop を実恒等式に置換: 例
`alpha_formula : Prop` → `alpha_def : ∀ i j, alpha i j = mu i j - delta • mu i 0 - n • zeta`、
`zeta_irreducible : Prop` → 実 `IsIrreducibleCharacter zeta` 等。

## 3. gate #3 ブリッジ: §10 `Hypothesis M` → §5 `TICyclicHypothesis G`

§10 の μ/ω 解析は §5/§6 の ω-grid を要する。§6 の ω/μ API は全て **`Hypothesis46 A L`/`TICyclicHypothesis`**
ベース ⟹ ブリッジが gate #3 proper の核心。

### 3a. `TICyclicHypothesis G` のフィールド (S05_TICyclic:41) と TypePData (MaximalSubgroupType:126) からの導出

| field | 導出 | 状態 |
|---|---|---|
| W/W1/W2, W1≤W, W2≤W, nontrivial, W1⊔W2=W, W_cyclic | TypePData 直対応 (`W_eq`/`W_cyclic`/`W*_nontrivial`) | 易 |
| `W_disjoint` | `M_complement` (W1∩M'=⊥) + W2≤H≤M' | ✅ **DONE** = `typePData_disjoint_W1_W2` (S12) |
| `W_card_coprime` | disjoint + cyclic ⟹ coprime | ✅ **DONE** = `typePData_coprime_card_W1_W2` (S12) |
| `W_card_odd` | `Odd |G| ⟹ |W| ∣ |G| ⟹ Odd |W|` | ✅ **DONE** = `typePData_W_card_odd` |
| `V := typePV M = W\(W1∪W2)` | TICyclicHypothesis.V と一致 | ✅ |
| `V_subset_sharp` | 1∈W1 ⟹ 1∉V ⟹ V⊆univ\{1} | ✅ |
| `V_subset_W` | set diff ⊆ W | ✅ |
| `W_normalizes_V` | W abelian (cyclic) ⟹ w∈W で wvw⁻¹=v∈V | ✅ (`commute_of_mem_of_isCyclic`) |
| `V_ti : IsTISubset V W` | **genuine gap** (§3b) → param `hVti` | ⏸ **issue 1005** (4.6.b ambient TI) |

**⟹ ブリッジ `typePData_toTICyclicHypothesis` (S12) 完成・axiom-clean (2026-06-20)。** 残 = `hVti`
([issue 1005](../../issues/1005-typep-ambient-v-ti.md))。

### 3b. V_ti gap (要設計判断)

`normalizer_V` (TypePData field: ∀ nonempty X⊆V, N_G(X)=W) からの直接導出は **非自明**:
- 単集合 {a} で `N_G({a}) = C_G(a) = W` (a∈V) は出る。
- a∈V, b=gag⁻¹∈V ⟹ C_G(b)=gC_G(a)g⁻¹ ⟹ gWg⁻¹=W ⟹ **g∈N_G(W)** までで、`g∈W` は出ない
  (N_G(W)=W が別途要)。
- ∴ IsTISubset V W は normalizer_V より strict に強い。§6 でも `hti` として**入力**
  (`toTICyclicHypothesisOfV` の引数、`Hypothesis46.tic.V_ti`)。
- **ツール**: `normalizer_eq_sup_of_isTISubset_of_isCyclic` (S16_MainResults:639) は
  **IsTISubset → normalizer_V の方向** (逆ではない)。
- **次の調査**: (i) §10 `Hypothesis.dadeData : DadeSupportHypothesisData M (typePA0 M)` が V の TI を内包するか
  (Dade isometry 構築で V_ti を使ったはず — 遡って expose 可能か)。(ii) `exists_hypothesis_of_typeIIIorIVorV`
  /`dadeSupportHypotheses_typeP` (S10:270) の構築過程で IsTISubset V W が available か。
  (iii) 最悪 case = ブリッジを `(hVti : IsTISubset (typePV M typeP) typeP.W)` パラメータ化 (§6 precedent) し、
  V_ti を別 obligation として後で discharge (honest factoring; scaffold ではない — V_ti は具体的 TI 事実)。

### 3c. coprime ✅ DONE

`typePData_coprime_card_W1_W2` (S12, axiom-clean)。Klein-four 反例ゆえ **cyclic が本質** (disjoint 単独では
不可)。S15 `coprime_card_U_card_P_of_disjoint` (S15_SAndT:888) は Hall 経由で別機構ゆえ非流用。
**実装** = 乗法写像 `(Subgroup.inclusion hW1le).coprod (Subgroup.inclusion hW2le) : ↥W₁ × ↥W₂ →* ↥W`
が disjoint から injective → `isCyclic_of_injective` (cyclic への埋め込みは cyclic) →
`coprime_card_of_isCyclic_prod` (mathlib `SpecificGroups/Cyclic`: 有限 cyclic product ⟹ 因子 coprime)。

### 3d. μ-level (ブリッジの次)

TICyclicHypothesis は **W-level ω/σ** のみ (ω on W, ω^σ on G)。μ_ij (on M, = Ind_{M'}^M …) は別途
**§6 `Hypothesis46`/`CertainTypeHypothesis` for M'** が要 (certain-type μ family + Dade)。これが de-opaque の
`mu`/`alpha` grid の供給源。§10 `Hypothesis M` から M' の certain-type 構造を構築 = 重い (full 4.6 apparatus)。

## 4. API 在庫 (sorry-free、消費可)

- **S05 ω-grid**: `TICyclicHypothesis.omegaGrid` (S05_OmegaGrid:65, `Fin|W1|→Fin|W2|→CF ↥W ℂ`),
  `omegaSigmaGrid` (S05_OmegaSigmaGrid:50, `→CF G ℂ`, = σ(ω)), `sigmaIntegral` (S05_IntegralSigma:48,
  `IntegralCharacterMap ↥W G`), `sigmaIntegral_apply_of_mem_V` (V 上恒等), β family + Gram (S05_SigmaIsometry:155).
- **§6 certain-type**: `Hypothesis46` (S06_CertainHypothesis46:39, extends `CertainTypeHypothesis`),
  `toTICyclicHypothesis` (S06_DadeIsometryCertain:414), μ/ω column API (`induce_omegaColumnDiff_*`,
  `columnFamily_mu_*`, `induce_isIrreducible_of_forall_chiRestrict_ne` Clifford, S06_CertainTypeCharacters/Clifford)。
- **TypePData** (MaximalSubgroupType:126): H/U/W1/W2/W + `M_complement`/`derived_complement`/`centralizer_W1`/
  `normalizer_V` + `card_W1_eq_derived_index`/`derivedInG_eq_fitting_sup_U`。`typePV`/`typePA0` (290/294)。
- **coherence**: `sibleySetup_is_coherent` (S08_CoherenceTheorems, ✅(6.8)), `IsCoherent` (S07:1557),
  `IntegralCharacterMap` (S07:301), `CharacterDifferenceImage` (S07:395)。
- **§4 Dade**: `S04_DadeIsometry` (main, sorry-free)。

## 5. 攻略順 (推奨)

1. ✅ `typePData_disjoint_W1_W2` (DONE, S12)。
2. ✅ `typePData_coprime_card_W1_W2` (DONE, S12)。
3. ✅ `typePData_W_card_odd` (DONE, S12; `Odd |G| → |W| ∣ |G| → Odd |W|`)。
4. ✅✅ **ブリッジ `typePData_toTICyclicHypothesis` 完成** (DONE 2026-06-20, S12, axiom-clean)。
   17 フィールド中 16 を `TypePData` から実証明で供給、`V_ti` のみ ambient TI = Peterfalvi (4.6.b) を
   **明示パラメータ `hVti`** で取る (§5 `mapOfInjective` / §6 `toTICyclicHypothesisOfV` と同設計;
   §3b の調査 (i)/(ii) で Dade data も normalizer_V も V_ti を供給しないと確定 → (iii) パラメータ化)。
   ⟹ ω-grid (`omegaGrid`/`omegaSigmaGrid`/`sigmaIntegral`) が §10 で利用可能に。
   **残 obligation = `hVti` の discharge = [issue 1005](../../issues/1005-typep-ambient-v-ti.md)**
   (4.6.b ambient-TI; 上流 BG σ-理論に gate されるか要判定)。
5. ▶ **次**: `CharacterParameters` de-opaque (§2、S15 模範) — opaque Prop を実恒等式に。
6. μ-level: M' の certain-type 構造 (§3d) ⟹ `mu`/`alpha` grid 供給。
7. (10.2)/(10.3) producer 構成 → (10.5)/(10.6) Dade calc → (10.8) keystone → (10.9)/(10.10.x)。
8. ⟹ §11/S13 (9.x/11.x riders) も同 machinery で。

**STOP 規律**: 1 leaf が ~4-5 実質試行で進まなければ STOP + 本 note に障害記録。難所回避禁止 ([[feedback-no-avoiding-hard-parts]])。

## 6. (10.2)–(10.5) 原文照合 + (10.2) 攻略 diagnosis (2026-06-20 bridge 後の調査)

原文 = `references/peterfalvi/04.12_pp_58_63_Maximal_Subgroups_of_Types_III_IV_and_V.mmd` L1-42 を verbatim 照合。
**確定した式 (de-opaque で baking する正値)**:

- **(10.1)**: `S = {Ind_{M'}^M θ | θ∈Irr M', θ≠1}`。「By (8.15), Hyp (4.6) と (5.2) が L=M, H=K=M' で成立。
  w₁,w₂,σ,ω_ij,μ_ij,μ_j,δ_j は **Hyp (4.6) with L=M** と同義」⟹ **μ/ω/δ は §6 (4.6)-with-L=M 由来**
  (∴ μ-level の真の供給源 = §10 Hyp → §6 `Hypothesis46 M M'` bridge、§3d)。
- **(10.3)**: `0≤i<w₁, 0<j<w₂` で `d=μ_ij(1)` は i,j 独立、`δ=δ_j` は j 独立、`d>1`、`n=(d-δ)/w₁∈ℕ`。
  (w₂ prime は **Thm (8.8)** 経由 type-II maximal S with |S:[S,S]|=w₂。)
- **(10.5)**: `α_ij = μ_ij − δ·μ_i0 − n·ζ` (`0≤i<w₁, 0<j<w₂`)、`Supp(α_ij)⊆A₀(M)`、
  `α_ij^τ = δ(ω_ij^σ − ω_i0^σ) − n·ζ^τ₁`。

### CharacterParameters de-opaque field specs (S15.Hypothesis 模範 = data+real恒等式, opaque Prop 廃止)

| 現 opaque Prop | 実恒等式 (self-contained = tau/tau₁ 不要) | 備考 |
|---|---|---|
| `zeta_irreducible` | `IsIrreducibleCharacter zeta` | producer 結論も書換要 (∧ の項) |
| `n_formula` | `(n:ℤ)*(hyp.w1:ℤ) = (d:ℤ) - delta` | clean |
| `alpha_formula` | `∀ i j, alpha i j = mu i j - (delta:ℂ)•mu i 0 - (n:ℂ)•zeta` | clean |
| `degree_independent` | `∀ i (j:Fin w2), j≠0 → (mu i j) 1 = (d:ℂ)` | index 0<j 要 |
| `delta_independent` | δ_j family field 追加要 (現状 `delta:ℤ` は共通値のみ) | 要新 field |
| `alpha_tau_formula`/`mu_tau1_formula`/`zeta_tau1_norm_bound`/`orthogonality_w1_lt_w2`/`typeV_*` | **tau (hyp.tau) / tau₁ (CoherentHypothesis) 要** | CoherentHypothesis 文脈で de-opaque |

⚠ S15.Hypothesis は `omega`/`eta`/`tau3` を **data field** + 恒等式 `eta_eq_tau_omega : eta i j = tau3 (omega i j)`
(S15_SAndT:131-147) で carry。CharacterParameters.omegaSigma も同様に bridge の `omegaSigmaGrid` に pin できる
(`omegaSigmaGrid` docstring が「`S12.CharacterParameters.omegaSigma` がこれに pin される」と明記)。

### ★ (10.2)/(10.3)/μ-grid 攻略 = §10→§6 (4.2)+Dade bridge (apparatus は §6 に既在!)

⚠⚠ **重要訂正** (2026-06-20 深掘り): 当初「(10.2) は quotient-Frobenius + Brauer を一から build」と
診断したが **誤り**。(10.1) 原文「Hyp (4.6) が L=M, H=K=M' で成立」が正路を指す: **§6 certain-type
apparatus が (10.2)/(10.3)/μ-grid をすべて供給**、新規 apparatus build は不要。Brauer/inertia は §6 に既在:
- `S06_CertainTypeClifford.lean:538` `card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm`
  (**Brauer permutation lemma**)、`:756` inertia `I_L(χ)=K`「W₁# で不動な char 無し」(= FPF-on-chars)。
- `IsFrobeniusGroup.of_centralizer_kernel_le` (`Ch06_FrobeniusActions/FrobeniusGroup.lean:324`) =
  `centralizer_W1` 条件から Frobenius 構成。
- `isIrreducibleCharacter_induce_of_inertia_eq` (`InducedIrreducible.lean:424`)。

**∴ 真の次ステップ = §10→§6 bridge = `Hypothesis M → S06.CertainTypeHypothesis (typePA0 M typeP) M`**
(`CertainTypeHypothesis A L extends S06.Hypothesis ↥L` + `dade : S04.Hypothesis G A L`):
- **Dade 部 `dade` は §10 Hyp に既在**: `Hypothesis.dadeData.dade : S04.Hypothesis G (typePA0 M typeP) M`。
- **構造部 `S06.Hypothesis ↥M`** (S06_DadeIsometryCertain:67, **11 field**) を `TypePData M` から構成
  (L=↥M, K=M'.subgroupOf M, W1/W2.subgroupOf M)。field 対応:

  | S06.Hypothesis ↥M field | TypePData M source | 備考 |
  |---|---|---|
  | `K = M'.subgroupOf M` / `K_normal` | derivedInG M 正規 (commutator) | 易 (subtype transport) |
  | `isComplement : IsComplement' K W1` | `M_complement` | **直対応** |
  | `W1_nontrivial`/`W1_cyclic` | `W1_nontrivial`/`W1_cyclic` | subgroupOf transport |
  | `W2_nontrivial`/`W2_cyclic`/`W2_le_K` | `W2_*`/(W2≤H≤M') | subgroupOf transport |
  | `centralizer_W2 : ∀x∈W1#, C_K(x)=W2` | `centralizer_W1` (C_{M'}(x)=W2) | G↔↥M transport (fiddly) |
  | `card_coprime : Coprime |K| |W1|` | **param `hHall`** (W₁ Hall, 非導出) | ⏸ **issue 1006** |
  | `W_odd` | `typePData_W_card_odd` 系 | ✅ 易 |

  **`card_coprime` (W₁ が M の Hall complement = gcd(|M'|,|W₁|)=1) は param `hHall` 化**: complement だけ
  では従わない (確認済: C₂×C₂ 反例)、κ-Hall 経由でのみ導出可ゆえ obligation = [issue 1006](../../issues/1006-typep-w1-hall.md)。
  他 10 field は subtype (subgroupOf) transport の機械作業で discharge (centralizer は `S03h.centralizer_subgroupOf`)。

**✅✅ bridge DONE (2026-06-20)**: `typePData_toS06Hypothesis` (構造部, 11 field) +
`Hypothesis.toCertainTypeHypothesis` (CertainTypeHypothesis 組立, dade=既在) 完成・axiom-clean
(`39f1ead4` 系の続き)。⟹ §6 の `toTICyclicHypothesis`・μ/ω column API・Clifford inertia が L=M で発火可。

### ▶ 次の着手順 (real 進捗順)

1. ✅ **§10→§6 bridge DONE**。残 = `hHall` discharge ([issue 1006](../../issues/1006-typep-w1-hall.md), κ-Hall 経由)。
2. **▶ (10.2)/(10.3) を §6 機構で形式化**: bridge の `CertainTypeHypothesis` から §6 の μ/ω/ζ family・
   Brauer/inertia を引き、(10.2) ζ (degree w₁ irreducible∈S)、(10.3) μ_ij/δ_j independence + w₂ prime を
   producer (`exists_zeta_degree_w1` 等) として構成。これで `CharacterParameters` の zeta/mu/omegaSigma が
   §6 由来の実データに。⚠ §6 が L=M で何を即供給するか (どの定理が `CertainTypeHypothesis`/`Hypothesis46`
   入力か) を先に RECON。
3. CharacterParameters de-opaque (self-contained field: zeta_irreducible/n_formula/alpha_formula) を
   producer signature 書換と一括で。
4. issue 1005 (hVti) / 1006 (hHall) discharge。
