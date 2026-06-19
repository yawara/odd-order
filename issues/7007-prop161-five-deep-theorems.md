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
- [ ] **conjunct 4 (BG 15.1(e))** `U≠⊥ → ∃U0≤U, exp U0=exp U, Mσ⊔U0 Frobenius kernel Mσ`:
  - **K=⊥ branch**: reachable — E=U setup (`subgroupESetup_of_isHall_kappa_eq_bot`) +
    `frobenius_factorization_of_regular` part (b) (U0=E₀)。hreg discharge は conjunct 3 と同型。
  - **⛔ K≠⊥ branch (type-P2) = 唯一の残 hard piece** (2026-06-19 委譲で深掘り ~530行→未完→**revert で消失**):
    - ✅ **設計検証済**: U 上で直接構成 (U は κ' ゆえ (τ1∪τ3)∖κ 元は Lemma 14.1 で自動 regular)。
      U0=⊔_p Z_p ((τ1∪τ3): Z_p=Sylow_p(U) cyclic / τ2: regular cyclic) → `isFrobeniusGroup_of_regular`。
    - ✅ **設計確定だが要再構築** `exists_regular_cyclic_fullExponent_tau2` (~130行) = `exists_cyclic_Enormal_regular_of_abelianSylow`
      の **C_E(S)=E 分岐を global hreg なしで抽出**。regularity は τ2-intrinsic (`Msigma_nilpotent_of_tau2`/`omega1_eq_of_tau2`);
      hreg は τ2'-元 + X-存在分岐でしか使われないと grep 確認済 (CES_eq 分岐は clean に transplant 可)。
    - ⛔ **真の blocker = `(|G|).factorization p = (|M|).factorization p` for p∈τ2(M)** (= M が G の full Sylow-p を含む)。
      τ2 機械は `S:Sylow p G` with `S≤M` を要求。**Sylow_p(G) の abelian/nonabelian 場合分け要**:
      abelian なら A∈ℰ_p²(U)⊆ℰ_p²(E)、S⊇A abelian ⟹ `S≤C_G(A)≤E≤M` (`centralizer_le_E_of_tau2`) ⟹ S=Sylow_p(M)=Sylow_p(U)、fact 成立;
      nonabelian は **Thm 12.7** (`frobFact_of_nonabelianSylow`) 経由。エージェントは abelian case のみで簡略化し circular に陥った。
    - **正スコープ = `frobenius_factorization_of_regular` の abelian/nonabelian Sylow 場合分けを U 上で再現** (各 case で
      full-Sylow-in-G fact 確立) + hreg-free τ2 helper 再構築。**~1+ session の深い §12 work、単発委譲/loop 不適**。
      σ-template = `exists_sylow_le_of_mem_sigma` (S10_HallStructureCore:536)、fact 技法 = `exists_mem_sigma_of_prime_dvd_card` (S14:3573)。
- [ ] conjunct 1-4 を `typeP_auxiliary_structure_gated` に wire (sorry 139→138)
- [ ] Thm 15.2(a) `mf_ne_msigma_typeP1_structure` (S15:1144)
- [ ] Thm 15.7 `fitting_not_ti_cases` (S15:3896) + Cor 15.5
- [ ] Thm A `theoremA_maximal_structure` (S16:144) — Lemma 15.1 + Prop 14.2 + §15 で全 conjunct
- [ ] Thm C `theoremC_paired_structure` (S16:274) — Thm A + Thm 14.7 + Lemma 15.1(b)
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
