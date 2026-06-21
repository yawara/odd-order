---
id: 7007
slug: prop161-five-deep-theorems
title: "Prop 16.1 axiom-clean: 5 deep §15/§16 structural theorems"
created: 2026-06-19
---

# Prop 16.1 axiom-clean: 5 deep §15/§16 structural theorems

## 背景

POLE-1 の構造側 producer 2 本（`section16MaximalPair` / `section16TypePStructure`）は
2026-06-19 に assembly-complete 化（issue 7005/7006 closed、sorry 140→139）。両 producer の残
`sorryAx` は全て上流 gate に由来し、最も近い lane-f 所有の gate が **BG Proposition 16.1**
(`proposition_type_classification`, `S16_MainResults.lean:894`, 現 `sorry`)。

Prop 16.1 の **組み立て層は完成済み**: engine `proposition_type_classification_of_inputs`
(`S16:817`) は 11 個の named obligation から 6 連言を sorry-free で組む。assembler 群
(`typePData_of_inputs` `S16:695` / `isType{II,III/IV,V}_of_typePData` `S16:763/750/776` /
`typeFData_of_kappa_eq_bot` `S16:555`) と bridge (`typePData_of_isTypeNonI` 等) も clean。

**∴ Prop 16.1 axiom-clean 化の残コスト = 丸ごと「5 本の深い §15/§16 構造定理の本体」**
（Workflow `wpn72i4yc` 2026-06-19 の精査で確定）。§14 long pole (Thm 14.7 `typeP_duality`,
`S14:7982`) は **clean** になったので frontier は §14 を抜け §15/§16 に上がった。

## 5 本の深い定理（= 真の残務）

| Lean 名 | 場所 | BG | leverage |
|---|---|---|---|
| `theoremC_paired_structure` | `S16:274` sorry | Thm C | **最高（11 obligation 中 5本: hP_derived/hP2II/hP1neIIIIV/hIF/hIIP2）** |
| `theoremA_maximal_structure` | `S16:144` sorry | Thm A | 高（hFI/hF_not_derived + M' の TypeFData） |
| `typeP_auxiliary_structure_gated` | `S15:704` sorry | Lemma 15.1 | **最上流 hard math**（Thm A・C・TypePData の土台） |
| `mf_ne_msigma_typeP1_structure` | `S15:1144` sorry | Thm 15.2(a) | h152a + Fitting 分解 |
| `fitting_not_ti_cases` | `S15:3896` sorry | Thm 15.7 | hP1eqV + hVP1 |

## BG schematic proof（原典 recipe、mmd 4420-4444）

```
Theorem A:
  Thm 10.2(b) → (1) M_σ unique σ-Hall + σ(G)-Hall         [✅ Msigma_isHall, ungated 済]
  Lemma 15.1(a) → (2) K cyclic Hall κ
  Prop 14.2(a)(b)(c) → (3)(4)(5)  M=KUM_σ, U◁UK, C_U(k)=1, K*=C_Mσ(K)≠1, C_M(k)=K×K*
  Thm 15.2(a), Cor 15.5, Thm 15.7(a)(b) → (6)(7)(8)
    (6) 1⊂M_F⊆M_σ⊆M'⊊M, M'/M_F nilpotent  [(6 partial) MF≤Msigma, Msigma≤M' ungated 済]
    (7) M''⊆F(M)=C_M(M_F)M_F, K≠1→F(M)⊆M'
    (8) M_F≠M_σ → U=1, F(M) TI, K prime

Theorem C (K≠1):
  Cor 14.12, Cor 15.6, Lemma 15.1(b) → (1)(2)(3)  U abelian+N(U)⊄M; K* cyclic 1⊂K*⊆M_F, M_F 非cyclic; M'=UM_σ, K*⊆M''
  Thm 10.1(b), Thm 14.7(a)(b)(c), Prop 14.2(c) → (4)(5)  ∃!Mstar; M(C(X))={M}/{Mstar}
  Thm 14.7(d)(f)(g)(e) → (6)(7)(11)(8)  M∩Mstar=Z=K×K* cyclic; M or Mstar P2 + 共役; U=1→K* prime; Ẑ TI N(Ẑ)=Z
  Prop 14.2(d), Thm A(3)(5) → (9)  C_M(Ẑ)=A0(M)-A(M) TI
  Prop 14.2(g), Thm 15.7(a) → (10) U≠1→K prime + F(M) TI ⊇M_σ

Theorem D (assembly): Cor 15.3(b)→(1); Lem 12.17→(2); Thm 14.4(b)+A(8)+Cor 15.9→(3)(4)
  [engine theoremD_..._of_inputs は既存; lane-f/H で配線]
```

**Thm C は ∃!Mstar=(4)=`typeP_duality`(clean) を含み、(6)(7)(8)も Thm 14.7 経由 ⟹ §14 clean 化の恩恵大。**

## 依存補正した buildable 順序（重要）

ユーザー選択は「Thm A→C→Lem15.1→15.2→15.7」だが、**実際の依存は Thm A/C が §15 lemma に
bottom-out** するので、clean 化には §15 foundation が先。真の順序:

1. **Lemma 15.1 (`typeP_auxiliary_structure_gated` S15:704)** — 最上流土台。deps = Prop 14.2(a)
   ✅ / Thm 14.7 ✅clean / Thm 12.12。4 conjunct: ①K≠⊥→M'=U⊔M_σ ∧ U abelian ②C_G(X) funnel
   (X cyclic+τ2) ③⟨U∩M̂_σ⟩ abelian ④U≠⊥→Frobenius U0M_σ。
2. **Thm 15.2(a) / Thm 15.7 / Cor 15.5** — Thm A の (6)(7)(8) が要する §15 残り。
3. **Thm A (`theoremA_maximal_structure` S16:144)** — Lemma 15.1 + Prop 14.2 + §15 で組む。
4. **Thm C (`theoremC_paired_structure` S16:274)** — Thm A + Thm 14.7 + Lemma 15.1(b) で組む。
5. **Prop 16.1 配線** — 11 obligation を構築し `exact proposition_type_classification_of_inputs …`、
   AxiomsCheck 登録。

### ⚠ stale docstring 注意（2026-06-19 発見）

`typeP_auxiliary_structure` の docstring (S15:745-758, Lane G 記載) は「conjunct 2/5 は **sorried**
§14 typeP_duality (Thm 14.7) を cite」とするが、**Thm 14.7 は今 clean**。docstring は stale で、
これら conjunct は既に unblock されている可能性が高い。着手時にまず Thm 14.7 経由の citation が
通るか確認すること（早期の勝ち筋）。

## 関連 forward lemmas（既存・活用可）

- `derivedInG_eq_Msigma_sup_derivedInG_complement` (S14:7741, clean): `M' = M_σ ⊔ E'`。
  Lemma 15.1①の `M'=U⊔M_σ` には E の Frobenius 構造 `E=K⋉U`（U=E₂E₃=E'）経由で `E'↔U` を繋ぐ要。
- `typeP_derivedInG_isComplement_kappaHall` (S14:7806, clean): `M'` complements `K`（piece 2 で使用）。
- `typeP_structure` = Prop 14.2 (S14:1665, proven): ActsPrimeOn / Kstar≠⊥ / N(X)⊓M=K⊔Kstar / TI 等。
- `theoremA_ungated_conjuncts` (S16:181, clean): Thm A の (1)(5 partial)(6 partial) 既証。
- `theoremB_U_sylow_abelian_rank_le_two` (S16:242, clean): Thm B(1)。

## 進捗ログ

**2026-06-21 (cont.) ✅✅ BG Thm 15.7(a) `fittingIsTI_of_isTypeP2` 完成 → Thm C conjunct 11 close (10/12) + 15.7 を (c) 残のみに** (`dc2fe378` + `7eeb933b`, full build 3881 green, sorry 136→135):
- **`fittingIsTI_of_isTypeP2` (S15, BG Thm 15.7 conjunct (a), mmd L4244)**: type-P2 maximal ⟹ FittingIsTI。
  証明 = landed §15 piece のみ: `¬FittingIsTI ⟹ MF=Mσ` (`mf_eq_msigma_of_not_fittingIsTI`) + `π(MF)∩β=∅`
  (`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`)、type-P2 は σ=β (Prop 14.2(g))、Mσ≠⊥ で q∈π(Mσ)=π(MF)⊆σ=β、
  disjoint と矛盾。sorry-free declaration (既存 `fitting_decomposition` sorryAx を transitively 保持、新規導入なし)。
- **Thm C conjunct 11 完全 close**: `U≠⊥→IsTypeP2` (`isTypeP2_of_hall_subgroupOf_ne_bot`) + |K| prime (Prop 14.2)
  + FittingIsTI (本補題)。⟹ **Thm C は 10/12 conjunct 実証明**、残 = conjunct 2 (N(U)⊄M=Cor 14.12)/10 (A0-A TI=Thm A(3)(5)) のみ。
- **`fitting_not_ti_cases` (フル 15.7) も (a)+(b) wire 済** (`7eeb933b`): (a)=本補題の対偶+F/P1/P2 三分律、(b)=`mf_eq_msigma_of_not_fittingIsTI`。
  残 sorry = (c)-(e) のみ (cyclic X=X₁∈Mσ / M'=F(M) / O_p(M) 非可換・Lem 10.13(b) / 三 local case = deep §15)。
- 15.7(a) は Prop 16.1 の hP1eqV/hVP1 にも再利用可 (型分類 reverse 方向)。**次 = Thm C conjunct 2/10、または 15.7(c)、または Cor 14.12**。

**2026-06-21 (lane F resume) ✅ Thm C `theoremC_paired_structure` 9/12 conjunct discharge + faithfulness 修正 2 件** (`8f636b54` + `ec711630`, full build 3881 green):
- TypePData de-contradiction (issue 7008, `0530f90c`) で lane unblock → Thm C 着手。Thm C は full sorry の scaffold だったが **9/12 conjunct を landed §14/§15 補題から実証明**:
  - conjunct 1,7 (U abelian, M'=U⊔M_σ) ← `typeP_hall_derived_eq_and_abelian` (Lem 15.1(b))
  - conjunct 3,4,5,6,8 (K*≠⊥/cyclic/≤M_F/≤M''/¬cyclic M_F) ← `typeP_kstar_in_mf` (Cor 15.6)
  - conjunct 9 (∃! M*) ← `typeP_duality` (Thm 14.7)
  - conjunct 12 (U=⊥→|K*| prime) ← `kstar_card_prime_of_inputs` (要 `kappa_eq_sigmaComplementPrimes_of_hall_subgroupOf_eq_bot` を Thm C 前へ hoist)
- **faithfulness 修正 2 件** (lane-internal、caller=`theoremII_tame_embedding{,_of_inputs}` のみ、3 定理に伝播):
  1. **署名に `hKM : K ≤ M`, `hUM : U ≤ M` 追加** — `subgroupOf M` Hall 条件は K,U⊆M を含意せず、conjunct 7 (M'=U⊔M_σ) は U⊄M で偽。BG は K,U が M の Hall factor (M=KUM_σ)。
  2. **`∃! M*` を `typeP_duality` の強い述語に強化** — 旧 scaffold の弱い述語 (maximal∧typeP∧¬conj∧(P2 M∨P2 M*)) は partner M* の全 G-共役が満たす (N_G(M*)=M*⊊G) ゆえ **∃! が literally false**。強い述語は dual Hall datum (K*≤M*, K=M*_σ⊓C(K*)) で M* を pin。caller は TI conjunct のみ projection ゆえ安全。
- **残 residual = genuinely-deep 3 conjunct のみ**: conjunct 2 (N(U)⊄M = Cor 14.12)、conjunct 10 (A0(M)-A(M) TI = Thm A(3)(5)+Prop 14.2(d))、conjunct 11 (U≠⊥→|K|prime∧F(M) TI = Thm C(10)=Prop 14.2(g)+Thm 15.7(a))。これらは standalone 補題未 landed。
- sorry 134→136 (1 opaque sorry を 9 conjunct 実証明 + 3 named residual に itemize、+ 2 bug fix)。進捗は sorry 数でなく実証明で測る ([[scaffold-sorry-free-not-done]])。
- **次**: Thm C residual (conjunct 2/10/11) は §16 Theorems A-E と連動の deep construction。または Thm A faithful (`theoremA_maximal_structure_faithful` 既 sorry-free) を活用した hard input 方向、Prop 16.1 wire。

**2026-06-19 (cont.³) ✅✅ BG Lemma 15.1 完全完成 — conjunct 4 + gated lemma wire DONE**:
- `3d240069`: **conjunct 4 (15.1(e)) COMPLETE** — τ₂ **nonabelian** sub-case 着地で `typeP_hall_frobenius_factor`
  全 sorry-free (K=⊥ / K≠⊥ τ₁∪τ₃ / τ₂ abelian / τ₂ nonabelian すべて)。nonabelian: Lemma 10.13
  (`nonabelian_pSubgroup_rankTwo_elemAbelian_structure`) で `C_{S'}(A)=A₀⊔Z` (Z cyclic) を取得、
  S'⊇Sylow_p(U) で C_{S'}(A)=Sylow_p(U)、Z regular は clause (c)、exp Z=exp SUG は not-cyclic 論法。
  新規 infra: `open scoped IsMulCommutative` (CommGroup 導出)。
- `7337cdf2`: **`typeP_auxiliary_structure_gated` wire DONE** — 4 conjunct standalone lemma の直接 4-tuple、
  sorry-free。BG Lemma 15.1 の §14-gated 構造内容が全 proven。
- sorry count 136→134 (merge 後)。**Lemma 15.1 は Thm A/C/TypePData の土台 — 完成で §16 endpoint へ前進**。
- **次 = Thm 15.2(a) `mf_ne_msigma_typeP1_structure` (S15) / Thm 15.7 `fitting_not_ti_cases` / Thm A / Thm C / Prop 16.1 wire**。


**2026-06-19 conjunct 4 (BG 15.1(e)) — K=⊥ DONE + K≠⊥ engine/packaging DONE, kernel isolated**:
- `06278a11`: K=⊥ branch (type F) of `typeP_hall_frobenius_factor` (Thm 12.12(b))。sorry-free。
- `49e1a380`: K≠⊥ の **assembly 層を全て sorry-free 化** + kernel を最小 per-prime 補題へ隔離:
  - `isFrobeniusGroup_of_regular_le_maximal` (sorry-free): `isFrobeniusGroup_of_regular` の E-setup-free
    一般化 (`U0≤M` + `M_σ⊓U0=⊥` + regularity を直接取る)。
  - `frobenius_factor_of_regular_components` (sorry-free): U abelian + per-prime regular component
    `Z_p` から `U0=⊔Z_p` (exp U0=exp U, U0M_σ Frobenius) を組む engine。
  - `typeP_hall_regular_component_at_prime` (**唯一の残 sorry**): p∣|U| → regular p-component Z_p≤Sylow_p(U)
    of full p-exponent。`typeP_hall_frobenius_factor` 自体は sorry-free (engine+helper に委譲)。
  - K≠⊥ branch = `M_σ⊓U=⊥` (coprimality) + engine 適用。**sorry count 不変** (K≠⊥ の sorry が
    最小 per-prime helper へ relocate)。full build 3862 green。
- `2f34b0a0`: **linchpin 確立 + τ1∪τ3 case DONE**。`exists_subgroupESetup_with_le hG hM hUM hUpi`
  (S12_Proposition1215:283) で **U≤E の E-setup** を取得 (U は σ'-subgroup ゆえ)。τ1∪τ3 (p∉τ2 ⟹
  r_p=1, `hsetup.pRank_M_le_two` の rank≤2 から): Z=Sylow_p(U) を G へ push、`factorization_exponent_le_of_sylow`
  + Lemma 14.1 (K=⊥ と同じ discharge)。**残 = τ2 case のみ** (helper の唯一 sorry)。
- **τ2 route 確定 (次の一手、~1 session)**: U-localization の conjugacy 罠は
  **S:=Sylow_p(U) を full G-Sylow として使う**ことで回避 (`exists_cyclic_Enormal_regular_of_abelianSylow`
  は `Z ≤ (S:Subgroup G)` を返す ⟹ S=Sylow_p(U) なら Z≤Sylow_p(U)≤U 直接)。要:
  - **hreg** (τ1∪τ3 regularity on E、K=⊥ パターン再利用、~30行)。
  - **full-Sylow-in-G fact (abelian)**: A=Ω₁(Sylow_p(U))∈ℰ_p²、S':Sylow p G⊇A、S' abelian ⟹
    S'≤C_G(A)≤E≤M (`centralizer_le_E_of_tau2`)、|S'|≤(card M).fact p=(card U).fact p=|Sylow_p(U)| ⟹
    |Sylow_p(U)|=(card G).fact p (full G-Sylow)。`Sylow.ofCard SU` で S:Sylow p G 化、適用。
  - **nonabelian sub-case**: Sylow_p(U)=C_S(A)=A₀×Z (Thm 12.7, mmd 3237)、Z=regular cyclic factor。
    既存 Lean `frobFact_of_nonabelianSylow` は FrobFactConclusion を返すゆえ per-prime Z 抽出は別途要 (harder)。

**2026-06-19 (cont.²) τ₂ abelian DONE — 残 sorry = nonabelian τ₂ のみ (1 本)**:
- `49e1a380`→`54b01ba0` で engine+packaging+τ1∪τ3+linchpin+**τ2 abelian** すべて proven。新 infra:
  `isFrobeniusGroup_of_regular_le_maximal` / `frobenius_factor_of_regular_components` (S15 sorry-free)
  + `exists_regular_cyclic_in_abelianSylow_tau2` (S12_Theorem1212b, hreg/hCES-free CES_eq variant —
  E=KU では hreg 偽 [κ⊆τ1∪τ3] かつ C_E(S)≠E ゆえ両 hyp 落とした) + de-private rank-2 constructor。
- **nonabelian τ₂ precise plan (next, ~60-100 行)**: `exists_canonical_line_of_nonabelianSylow`
  (S12_Theorem127:325) が A₀ (order p, centralizes M_σ) + **clause (c)** (non-A₀ line X∈ℰ_p¹(E) は
  M_σ⊓C(X)=⊥) 供給。要 = cyclic Z≤Sylow_p(U) of full exponent with Ω₁(Z)≠A₀ (⟹ (c) で regular)。
  abelian 構造: Sylow_p(U)=A₀×Z (A₀ direct factor ⟺ A₀⊄℧¹(Sylow_p(U)))、max-order cyclic の
  Ω₁=L_char≠A₀ (a>b) / 任意 non-A₀ line (a=b)。cyclic Z' は既存 lemma 未露出
  (`exists_complement_of_canonical_line` S12_Theorem127d:163 は E 内 complement E₀、cyclic Z' でない)
  ⟹ Sylow_p(U) 上で A₀×Z 分解 or agemo-with-(c)-line を再構成要。

- **kernel の shared linchpin (確定)**: τ1∪τ3 (partition coverage `pRank_M_le_two` で r_p=1) も
  τ2 (regular cyclic machinery) も **両方とも type-P M の E-setup with U≤E を要求**。`pRank_M_le_two`
  (S12_ECore:267) と `mem_tau_union_of_mem_primeFactors` (S12_ECore:295) は E-setup メソッド、τ2 機械
  (`exists_cyclic_Enormal_regular_of_CES_eq` 等) も E-setup 取る。⟹ **次の一手 = type-P M の E-setup
  (E=KU σ-complement, U≤E) を構成** (`subgroupESetup_of_complement` S12_Proposition1215:194 は private、
  M=KUM_σ から M_σ⊓KU=⊥ ∧ M_σ⊔KU=M を示し E=KU で適用、または de-private wrapper)。これが linchpin。

**2026-06-19 conjunct 1 (BG Lemma 15.1(b)) DONE** (`cab5603a`): standalone clean lemma
`typeP_hall_derived_eq_and_abelian` (S15_MF.lean, `typeP_auxiliary_structure_gated` 直前) =
`K≠⊥ → M'=U⊔M_σ ∧ IsMulCommutative U`。sorry-free + axiom-clean、full build 3862 green。
+ helper `card_mul_card_mul_card_eq_of_three_hall` (|M|=|K||U||M_σ| 三 Hall 分割)。
証明: `typeP_duality`(clean) で M' complements K + coprime → M_σ≤M' / U≤M'(|U| coprime [M:M']=|K|)
→ 三 Hall card で |U⊔M_σ|=|M'| → M'=U⊔M_σ。U abelian = `[U,U]≤[M',M']≤M_σ`(`derivedDerived_le_Msigma`)
∧ `[U,U]≤U` → `[U,U]≤U⊓M_σ=⊥`。**sorry count 不変 (139)** — gated 定理に wire するのは conjunct 2-4 着地後。

**conjunct 2-4 の依存状況 (2026-06-19 精査確定)**:
- conjunct 2 (BG 15.1(c) C_G(X) funnel + X cyclic τ2): **全ピース available** ⟹ reachable。
  - Thm 12.5(d) (rank-2 A の `Mσ⊓C(A)=⊥`) = **`Msigma_nilpotent_of_tau2`** (S14:~1275 で使用、`.2.2.2.1`)
  - Lemma 14.1 (rank-1, p∉σ∪κ の `Mσ⊓C(A)=⊥`) = **`msigma_structure_of_notMem_sigma_kappa`** (S14:1183)
  - Cor 14.3 funnel (τ2-element → 𝓜(C_G(x))={M}) = **`maximalContaining_centralizer_eq_singleton_of_tau2_element`** (S14:2199)
  - Cor 12.10(b) (E' abelian) = **`nilpotent_sigmaComplement_abelian hG h`** の `.2.1.2` (`IsMulCommutative (derivedInG E)`)
  → conjunct 2 を background subagent に委譲 (2026-06-19, S14 に standalone lemma `typeP_hall_small_subgroup_cyclic_tau2`)。
- **✅ 訂正 (2026-06-19): Thm 12.12 は形式化済み — conjunct 3,4 も reachable**:
  前の「Thm 12.12 未形式化」は **誤ディレクトリ grep の false alarm** (`Ch3_Uniqueness/` を見ていたが §12 は
  **`OddOrder/BG/Ch3_MaximalSubgroups/`** に在る)。Thm 12.12 = `S12_Theorem1212{,b,c}.lean`、**全 sorry-free**。
  結論述語 `FrobFactConclusion M E` (S12_Theorem1212:35) = (a)∃ abelian normal A₀≤E, E≤N(A₀), ∀x∈Mσ#,
  E⊓C(x)≤A₀; (b)∃ E₀≤E, exp E₀=exp E, Mσ⊔E₀ Frobenius kernel Mσ。producer: `frobFact_of_regular_all`
  (S12_Theorem1212:182, hyp=∀e∈E# Mσ⊓C(e)=⊥) / `frobFact_of_nonabelianSylow`(:414) / `frobFact_of_abelianSylow`
  (S12_Theorem1212c:394)。**まだ §14/§15 から consume されていない** (要 wire)。
  - conjunct 3 (BG 15.1(d) `IsMulCommutative (centralizerGeneratedBySigma M U)`): **K≠⊥ = conjunct 1** (U abelian
    ⟹ `centralizerGeneratedBySigma ≤ U` abelian)。**K=⊥ = Thm 12.12(a)**: κ=∅ ⟹ E=U、A₀ abelian で
    `centralizerGeneratedBySigma = sSup{U⊓C(x)} ≤ A₀` ⟹ abelian。
  - conjunct 4 (BG 15.1(e) `U≠⊥ → ∃U0…Frobenius U0Mσ`): **K=⊥ = Thm 12.12(b)** (E=U, U0=E₀)。
    **K≠⊥ (type P2) = 別議論** (BG 4178「easy C_E(S)=E case」; type-P で U が Mσ に FPF 作用 →
    `isFrobeniusGroup_of_regular` で U0=U。`Msigma_centralizer_E23_eq_bot_of_caseTau1` 系の FPF 補題要確認)。
  - ⟹ **Lemma 15.1 の 4 conjunct 全て reachable**。Thm 12.12 を wire すれば gated 定理が組め count 139→138。
    onion の底は Thm 12.12 で、それは既に床が張られていた。

## やること

- [x] Lemma 15.1 conjunct 1 (BG 15.1(b)) = `typeP_hall_derived_eq_and_abelian` ✅ `cab5603a`
- [x] conjunct 2 (BG 15.1(c)) = `typeP_hall_small_subgroup_cyclic_tau2` ✅ `e11e3028`
- [x] BG Thm 12.12 形式化確認 — ✅ 既存 sorry-free (`frobenius_factorization_of_regular` S12_Theorem1212c:520)
- [x] conjunct 3 (BG 15.1(d)) = `typeP_centralizerGeneratedBySigma_isMulCommutative` ✅ `80aa03cf`
- [~] **conjunct 4 (BG 15.1(e))** `typeP_hall_frobenius_factor` (S15_MF:1007) `U≠⊥ → ∃U0≤U, exp U0=exp U, Mσ⊔U0 Frobenius kernel Mσ`:
  - **✅ K=⊥ branch (type F) DONE + committed** (`06278a11`, 2026-06-19): E=U setup
    (`subgroupESetup_of_isHall_kappa_eq_bot`) + `frobenius_factorization_of_regular` part (b) (U0=E₀)。
    hreg discharge は conjunct 3 と同型 (Lemma 14.1 `msigma_structure_of_notMem_sigma_kappa`)。sorry-free。
  - **⬜ K≠⊥ branch (type P2) = 残 kernel** (2026-06-19 **完全再スコープ**, BG 原文 + §12 machinery 精読):
    - **訂正 1 — assembly は CLEAN (U abelian)**: U0=⊔_{p∈π(U)} Z_p。U abelian ⟹ `card_finsetSup_eq_prod`/
      `mem_Z_of_orderOf_prime_mem` (S12_Theorem1212c:102/138, H=U) の normalizer 条件 `U≤N(Z_p)` が**自動**。
      exp は `exponent_eq_of_forall_factorization_le` (S12_Theorem1212:90, E-setup 不要)。regularity は
      `inf_centralizer_eq_bot_of_forall_prime_order` で素数位数還元 → 各 prime-order 元は `mem_Z_of_orderOf_prime_mem`
      で Z_r 内 → Z_r の regularity。Frobenius packaging は `isFrobeniusGroup_of_regular` (S12_Theorem1212:119)
      の **E-setup-free 一般化** (proof は h を mem_maximal/E_le/E_compl_inf でしか使わず U0≤M + Mσ⊓U0=⊥ で代替可)。
    - **訂正 2 — BG「easy C_E(S)=E」の意味**: BG 4178「(e) is obvious from the easy C_E(S)=E argument」=
      U abelian ⟹ C_U(Sylow_p(U))=U 自動 ⟹ Thm 12.12 の C_E(S)=E 易枝に常に居る。`exists_cyclic_Enormal_regular_of_CES_eq`
      (S12_Theorem1212b:1044) がこの枝。**但し S:Sylow p G with S≤M を要求** = full-Sylow-in-G fact。
    - **訂正 3 — nonabelian は full-Sylow-in-G が FAILS だが Z_p は依然存在**: Thm 12.7 proof (mmd 3227)
      `P=C_S(A)=Sylow_p(M) ⊊ S=Sylow_p(G)` ⟹ M は full G-Sylow を含まない。だが `P=A₀×Z` (mmd 3237,
      A₀ order p centralizes Mσ=非regular, Z cyclic regular) ⟹ **Z_p=Z** が regular cyclic of full exponent
      (A₀ は exp p で exp を上げない)。Thm 12.7(d) `frobFact_of_nonabelianSylow` (S12_Theorem1212:414) が供給源。
    - **正スコープ (確定)**: ① sorry-free engine `frobenius_factor_of_regular_components` (assembly + 一般化
      Frobenius packaging, 上記訂正 1 の通り、~100 行) + ② per-prime witness の discharge: τ1∪τ3 (Z_p=Sylow_p(U)
      cyclic, Lemma 14.1 で regular, inline 易) / **τ2 = 唯一の hard kernel** (abelian: full-Sylow-in-G fact
      `S=Sylow_p(U)≤M` 確立 → CES_eq; nonabelian: Thm 12.7 から Z 抽出)。**τ2 kernel = ~1 session の深い §12 work**。
    - **prior 530-line 失敗の死因 = abelian only に簡略化し circular** (訂正 3 が示す通り nonabelian は別構造で回避要)。
      σ-template = `exists_sylow_le_of_mem_sigma` (S10:536)、`centralizer_le_E_of_tau2` (full-Sylow abelian 枝)。
- [ ] conjunct 1-4 を `typeP_auxiliary_structure_gated` に wire (sorry 139→138)
- [ ] Thm 15.2(a) `mf_ne_msigma_typeP1_structure` (S15:1144)
- [~] Thm 15.7 `fitting_not_ti_cases` — **residual = type-F の `M'=F(M)` 一点まで還元** (`dc2fe378`/`7eeb933b`/`1d5e6ff0`/`4fc9125a`, 2026-06-21)。(a)=`fittingIsTI_of_isTypeP2`+三分律 / (b)=`mf_eq_msigma_of_not_fittingIsTI` / ∃X=巡回非自明 X≤MF は Mσ order-q 元 (Lean 文 X 非 pin=弱化) + prime p∈σ-β は disjointness + disjunct (a)。**`M'=F(M)` の type-P1 case は実証明** (`4fc9125a`: U=⊥ inline [κ=σ'] → M'=Mσ via Lem15.1b、K≠⊥ via `card_kappaHall_ne_one`、Mσ=MF nilpotent → Mσ≤F(M)、clause d F(M)≤M')。**残 = type-F の M'=F(M) のみ**: clause d (¬type-F→F(M)≤M') が type-F で適用外、M'=F(M)⟺M' nilpotent⟺U(Frobenius 補元)abelian で、U abelian は type-F で未 landed = BG の E₃=1 argument (Cor 12.6(d)+Lem 12.19+Cor 15.5+Lem 12.1) 要。`subgroupESetup_of_isHall_kappa_eq_bot` (type-F E-setup, E=U) 在
- [ ] Thm A `theoremA_maximal_structure` (S16:144) — Lemma 15.1 + Prop 14.2 + §15 で全 conjunct
- [~] Thm C `theoremC_paired_structure` — **10/12 conjunct discharge + faithfulness 修正 2 件 DONE** (`8f636b54`/`ec711630`/`378e91cf`/`dc2fe378`, 2026-06-21)。残 = conjunct 2 (N(U)⊄M=Cor 14.12)/10 (A0-A TI=Thm A(3)(5)) のみ (conjunct 11 は 15.7(a) で close)
- [ ] Prop 16.1 配線 `proposition_type_classification` (S16:894) + AxiomsCheck 登録

## 完了条件

`proposition_type_classification` (S16:894) が sorry-free + axiom-clean（#print axioms で標準3公理のみ）
で、5 本の深い定理も同様。これにより mp/tp producer の sorryAx 源（Prop 16.1 分）が解消。

## 参照

- 先行: issue 7005/7006 (closed, POLE-1 構造側 assembly-complete)、commit `8c231082`
- Workflow 精査: `wpn72i4yc` (2026-06-19, frontier map)
- BG 原典: `references/bg/local-analysis.mmd` §16 (4328-4449), Lemma 15.1 (4116 付近), Prop 16.1 (4478)
- memory: [[s16-typep-producer-unfillable]] [[bg-s16-gated-on-typedata-construction]]
- 残り obligation 詳細（reverse lemmas hIF/hIIP2/hIIIIVP1/hVP1 は新規・gated）: Workflow plan 参照
