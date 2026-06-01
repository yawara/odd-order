# Peterfalvi (6.8) Sibley coherence — assembly plan + [Is] Thm 6.34 progress

**作成**: 2026-06-01 (worktree `lucid-kapitsa-c87a31`)。2 並列 explore (Plan agent) の統合 + 本線 proof 進捗。
正本 handoff は `issues/0046-...md`; 本ノートは (6.8) capstone を `sibleySetup_is_coherent`
(S08:188 sorry) まで運ぶ **具体的 task DAG** + 監査訂正をまとめる。

## A. [Is] Thm 6.34 (induced irreducibility) — 本線 frontier、新 file `InducedIrreducible.lean`

`H ⊴ G`(Peterfalvi の `H ⊴ L`)、`θ ∈ Irr H`、`θ ≠ 1`、**W₁=G/H が Irr(H)∖{1} に自由作用**
⟹ `Ind_H^G θ ∈ Irr G`, degree `[G:H]·θ(1)=|W₁|·θ(1)`。(6.8) の `Y=S(H')` (degree |W₁|) と
case-A の `X⊂Irr L` を供給する最高レバレッジ brick。

### landed (sorry-free, axiom-clean, AxiomsCheck 登録、commits 8e1b74e / 9c505fc)
- **brick (i) Mackey 制限** `card_smul_restrict_induce` :
  `(Nat.card H:k) • restrict H (induce H θ) = ∑ x:G, conjBy x⁻¹ θ` (任意 CommRing k, H⊴G)。
  **設計上の鍵 = 非正規化形** (transversal/`Quotient.out`/fiber-card を全回避; |H| 倍が
  `induce` の |H|⁻¹ を相殺、各左剰余類は `conjBy_eq_self_of_mem` で |H| 個の等項)。
  helper `ClassFunction.finset_sum_apply` も同 file。
- **brick (ii-pre)** `card_mul_inner_self_induce` (任意 θ:CF, over ℂ):
  `(Nat.card H:ℂ) * ⟨Ind θ, Ind θ⟩ = ∑ x:G, ⟨θ, θ^{x⁻¹}⟩`。Frobenius `inner_induce_eq_inner_restrict`
  ∘ brick(i) ∘ inner の右共役線形 (`inner_smul_right`+`star_natCast`)。
- **brick (ii)** `card_mul_inner_self_induce_eq_card_inertia` (θ:IrreducibleCharacter H):
  `(Nat.card H:ℂ) * ‖Ind θ‖² = |I_G(θ)|` (= `[I_G(θ):H]`)。Mackey 各項を
  `irreducibleCharacter_inner_eq_ite` + `coe_conjBy` + `mem_inertia` で inertia 指示関数に潰し
  `Finset.sum_boole`/`Fintype.card_subtype` で count。

### ✅✅ 6.34 COMPLETE (2026-06-01, commit 2f7d545; 全 sorry-free, axiom-clean, AxiomsCheck 登録)
- **brick (iii) 既約性 + capstone** `isIrreducibleCharacter_induce_of_inertia_eq` :
  `H⊴G, θ:Irr H, ClassFunction.inertia (θ:CF)=H ⟹ IsIrreducibleCharacter (induce H (θ:CF))`。
  (a) `induce_mem_ZIrr H θ.property.mem_ZIrr` (∈ZIrr G); (b) brick(ii)+`inertia=H` で `‖Ind θ‖²=1`
  (`mul_left_cancel₀`); (c) degree `[G:H]·θ(1)>0` (`induce_apply_one`+`H.index_mul_card` で index>0);
  (d) reusable 判定 `isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos`
  (`φ∈ZIrr,‖φ‖²=1,φ(1)=正nat ⟹ Irr`) = `exists_irr_sub_irr_of_inner_self_two` の ‖·‖²=1 版,
  helper `exists_single_of_sum_sq_eq_one` (∑cᵢ²=1⟹単一±1) + 符号は degree>0 で確定。
- **brick (iv) degree** = `induce_apply_one` (pre-existing)。
- **自由作用仮説**: statement は `inertia (θ:CF)=H` を直接取る (honest)。実適用では Peterfalvi の
  W₁=G/H が Irr(H)∖{1} に自由作用 (Frobenius complement; `brauer_permutation_lemma'` が classes∖{1}
  自由を供給) ⟹ θ≠1 で stabilizer=H を別途供給する wiring が (6.8) Y/X 構成時に必要 (T6/T7)。

**⟹ §A 完了。本線の次 = T1 (SibleySetup 再構築) で engine の goal shape を整え、T6 (Y coherent,
6.34 で η_j(1)=|W₁|) から assembly 開始。**

## B. T1 (最重要・隠れた構造 blocker): `SibleySetup` を faithful に作り直す

**核心**: `CoherenceTarget` = `IsCoherent hyp.coherence.tau S A` だが現 `coherence.tau` は
**opaque + 大域等距** (`tau_isometry`, FT に非存在)。一方 S07 engine は **具体 base map**
`dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)` 専用に `IsCoherent` を産む。
mmd 04.8 L150 "τ coincides with the Dade isometry relative to (A,L,G)" が load-bearing link。
**現 SibleySetup はこれを記録せず ⟹ scaffolding 無しでは discharge 不能**。

### 監査訂正 (explore が code 照合で確定)
1. **(6.8.a) は `H` NILPOTENT** (mmd L138), `IsPGroup` ではない。p-群還元は (6.5) で proof 内部。
   `IsPGroup p H` を field にすると scaffolding ⟹ field は `Group.IsNilpotent ↥H` + `H≠⊥`。
2. **現 `SibleySetup.H_sharp_ti` は ambient が誤り** (S08:142, `IsTISubset ((H:Set L)\{1}) (normalizer (H:Set L))`)。
   正: **G 内 TI** で normalizer = **L** (`IsTISubset ((map L.subtype H:Set G)\{1}) L`)。
3. **型 param 不整合**: 現 `SibleySetup` は抽象 `{L G:Type*}`、engine は `L:Subgroup G`+源 `↥L`。
   ⟹ `SibleySetup` を `(G:Type*)[Group G]`, `L:Subgroup G` に **再 param 必須** (S04.Hypothesis/
   S06.CertainTypeHypothesis と同流儀)。「field τ を足すだけ」patch は型不一致で不可。

### 新 SibleySetup (field 骨子; 詳細は explore 出力/transcript)
`structure SibleySetup (L:Subgroup G) [Invertible (Nat.card G:ℂ)] [Invertible (Nat.card ↥L:ℂ)]`:
`H W1 : Subgroup ↥L`, `H_ne_bot`, `W1_nontrivial`, `H_normal`, `split:IsComplement' H W1` (L=H⋊W₁),
`H_nilpotent:Group.IsNilpotent ↥H`, `card_L_odd:Odd (Nat.card ↥L)`,
`H_sharp_ti` (G内TI, normalizer=L), `dade:S04.Hypothesis G (sharpImage H L) L`, `hconj:dade.HConjInvariant`,
`S/S_eq` (`S={Ind_H^L θ|θ:Irr H, θ≠1}`), `cases:SibleyCase L H W1` (c1=`IsFrobeniusGroup ↥L H W1` /
c2=`S06.CertainTypeHypothesis` + `K=H` + `w₂`素 + `W₂⊆[H,H]` + `certain.dade=hyp.dade`)。
+ **`noncomputable abbrev tau := dadeIntegralCharacterMap dade (dade.fullDadeIsometryData hconj)`**
(= S07.IntegralCharacterMap ↥L G, **opaque 排除**) → `CoherenceTarget := IsCoherent tau S (supportInSubgroup ...)`。

### downstream 影響 (全て S08 内、shared/frozen file 変更ゼロ)
- `IndChainDecomposition`/`.ofIsCoherent` (S08:204-266) は τ を直接取る ⟹ **無変更**。
- `coherence_tau_inner_eq` (S08:158) は大域等距依存 ⟹ **削除** (Dade map で数学的に偽)。
- `coherence_inner_eq_on_supported` (S08:164) は lattice-relative ⟹ 型調整して保持。
- `DescentHypothesis`/`OddOrderSpecialization` 継承は consumer 0 ⟹ 切断 (削除推奨)。
- S09 は SibleySetup 不参照; AxiomsCheck は S08 result 未登録 ⟹ いずれも無変更。
- build-order: helper def → SibleyCase → 新 struct (別名 `'`) → tau/CoherenceTarget → consumer port →
  sorry 版 thm → 旧削除+rename → full build。`IsCoherent` lattice-relative 弱化は durably authorized。

## C. (6.8) 本体 assembly task DAG (T0–T11; 6.34=A, SibleySetup=B/T1 を前提)

| # | task | LOC | blocked-on | 6.34非依存 |
|---|------|-----|-----------|:---:|
| T0 | [Is]Cor 2.30 producer `θ(1)²≤[H:Z]` (Z≤Z(H)) | ~50 | — | ✅ |
| T1 | **SibleySetup 再構築** (§B) | ~120 | — | ✅ |
| T2 | (5.2.a/b) discharge → `S07.Hypothesis` の tau=τ_D | ~120 | T1 | 一部 |
| **T3** | **(6.7) 上位定理** `peterfalvi_67` (ψ(z)≡ψ(1) mod|P|) — **atoms は ClassSumAlgebra/AlgInt に既存(~90%)**、残=top wiring+(iii)-collapse(`ω(C_s)=α`)+rationality | ~150-250 | — | ✅ **今すぐ可** |
| **T4** | **(1.9)Galois作用+(5.9.a)coherence不変** (cyclotomic field-of-values) — case B 専用、分離可、repo 皆無 | ~200-350 | — | ✅ **今すぐ可** |
| T5 | [Is]Lem 2.27 `Res_Z θ=θ(1)·φ` (Z≤Z(H)) | ~40 | — | ✅ (case B) |
| T6 | `Y` coherent: 等次数族 η:Fin m→Irr L (η_j(1)=|W₁| ← 6.34) で `coherentEqualDegree_fromDade` | ~120 | T1,T2,**6.34** | — |
| T7 | `X` 特徴付け `X={χ∈Irr L\|Z⊄ker χ}` (c1=6.34 / c2=(4.5)) | ~140 | T1,**6.34**,(4.5)? | — |
| T8 | `X` coherent の `DadeChainStep` data (degree-sort + gap + Cor2.30 + 共役対) — 最重 | ~300-450 | T0,T7 | — |
| T9 | (6.8.1) case-A gluing: (6.7)合同で b≡c≡0(mod a) → `coherentUnion_of_glued` | ~250 | T3,T6,T7,T8 | — |
| T10 | (6.8.2) case-B gluing: (6.8.2.1)←T4 / (6.8.2.2)←T3 / (6.8.2.3)←T5 | ~350 | T3,T4,T5,T6,T7,T8 | — |
| T11 | (6.8.3) `X∪Y=S` (else (5.6)+Cor2.30+odd-order矛盾; `sumNonInflatedDegreeSq_eq_index_mul` 既landed) + τ_D→coherence.tau bridge → `sibleySetup_is_coherent` 完了 | ~200 | T9,T10 | — |

**critical path**: T1→T2→{T6,T7}→T8→{T9(+T3),T10(+T3,T4,T5)}→T11。新規 ≈2200-3000 LOC、残は §7 engine 再利用。
**今すぐ並行可能 (6.34非依存)**: T0, T1, T3, T4, T5。中でも **T3(6.7) は handoff の「~300行未実装」が stale** —
atoms (`peterfalvi_673`@ClassSumAlgebra:1651, `AlgInt.Cong.*`, `centralCharacterOfRep_*`) 既存で残 wiring のみ。

### engine 主部品 (S07; 入力 shape)
`coherentUnion_of_glued`(S07:3468, 2族 glue, `himg_ortho` が hard content)、`coherentEqualDegree_fromDade`(4713)、
`peterfalvi_66_coherence_of_X_from_dade`(5120)、`DadeChainStep`(4936)+`.advance`、`dadeIntegralCharacterMap`(4127)。
S04: `Hypothesis`(192), `HConjInvariant`(492), `supportInSubgroup`(137), `fullDadeIsometryData`(4315)。
S06: `CertainTypeHypothesis`(38), `W2`。
