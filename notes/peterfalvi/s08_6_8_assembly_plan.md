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

### T1 進捗 (2026-06-01, worktree `lucid-kapitsa`)
- **✅ step 1 (commit 3f83e90, build-green, sorry 増なし)**: `sharpImage (H:Subgroup ↥L):Set G` +
  **`SibleyDadeHypothesis (G)[Group G][Fintype G][Invertible(Nat.card G:ℂ)] (L:Subgroup G)[Fintype ↥L][Invertible(Nat.card L:ℂ)]`**
  (fields: H W1:Subgroup ↥L / H_ne_bot / H_normal / W1_nontrivial / card_L_odd / `H_sharp_ti:IsTISubset (sharpImage H) L` (ambient 修正済) / `dade:S04.Hypothesis G (sharpImage H) L` / hconj / S) +
  **`tau := dadeIntegralCharacterMap dade (dade.fullDadeIsometryData hconj)`** + **`CoherenceTarget := IsCoherent (L:=↥L) tau S (supportInSubgroup (sharpImage H) L)`**。
  legacy `SibleySetup` と並存 (未 swap)。**= T1 の crux (real-tau CoherenceTarget が engine 産出 shape と一致) を検証済**。
- **⚠️ 発見した設計上の wrinkle (次セッション必読)**: faithful field **`S_eq : S = {Ind_H^L θ | θ≠1}`** は
  `induce H (θ:CF)` を要し, それは **`[Invertible (Nat.card ↥H : ℂ)]`** を要求するが H は field ゆえ
  field 型 elaboration 時にこの instance が scope に無い (typeclass 解決失敗)。対策案: (a) `cardH_inv :
  Invertible (Nat.card ↥H:ℂ)` を field 化し S_eq で `@induce ... cardH_inv` 明示 (ugly), (b) `Fintype ↥H`
  (from `[Fintype ↥L]`) + `Nat.card ↥H>0` から導出する local/global instance を用意 (ℂ char-0; `invertibleOfNonzero`
  は instance でない点に注意), (c) S を「induce の像」として別の表現に。**(b) が最有力** (一度
  `instance : [Fintype ↥L] → Invertible (Nat.card ↥H:ℂ)` 的補題を立てれば S_eq も case-B の Ind_Z 等でも再利用)。
- **残 T1 step (次)**: S_eq + 残 (6.8.a) field (`split:IsComplement' H W1` / `H_nilpotent:Group.IsNilpotent ↥H`,
  要 `Mathlib.GroupTheory.{Complement,Nilpotent}` import) + `cases:SibleyCase` (c1=`IsFrobeniusGroup ↥L H W1`
  要 Isaacs import / c2=`S06.CertainTypeHypothesis` + `certain.dade=dade` 制約) を追加し faithful 化 →
  **その後初めて** `sibleySetup_is_coherent` を `SibleyDadeHypothesis` に restate (faithful 化前に restate
  すると S 自由ゆえ over-general=anti-scaffold) → legacy `SibleySetup`/`OddOrderSpecialization`/`DescentHypothesis`/
  `coherence_tau_inner_eq` 削除 + `coherence_inner_eq_on_supported` retype → full build。consumer `IndChainDecomposition.ofIsCoherent` は τ 直接取りゆえ無変更。

#### step 2a/2b 完了 (2026-06-01, commits a01dafc / ebf2c60, build-green)
- **2a (a01dafc)**: H を **structure param** に昇格 (`[Invertible (Nat.card ↥H:ℂ)]` 同伴) し induce-instance
  wrinkle 解消。faithful field **`S_eq : S = {φ | ∃ θ:Irr ↥H, θ≠1 ∧ φ=ClassFunction.induce H (θ:CF)}`** 追加。
  (`induce` は `ClassFunction.induce` で qualify 要; S08 は `open OddOrder.RepresentationTheory` のみで ClassFunction 未 open。)
- **2b (ebf2c60)**: `H_nilpotent:Group.IsNilpotent ↥H` + `split:Subgroup.IsComplement' H W1` 追加
  (imports `Mathlib.GroupTheory.{Nilpotent,Complement}`)。**⟹ (6.8)(a)+(b) faithful 完成**。

#### (6.8) 正確な仮説 (mmd 04.8 L137-145 原文) — (c)/swap の正本
- (a) `L=H⋊W₁`, `|L|` odd, `H` non-identity nilpotent ≤ L, `H^#` TI-subset of G with normalizer L。✅ 全 field 化済。
- (b) `S={Ind_H^L θ | θ∈Irr H, θ≠1_H}`, **`τ = Z[S,L^#] への Ind_L^G の restriction`**。✅ S_eq 済。
  - **⚠️ tau の subtlety (未解決)**: 原文 (b) の τ は **Ind_L^G の制限**であって Dade 写像ではない。proof 冒頭が
    (5.2.b)+[Is]Lem 7.7 で「τ = Dade isometry relative to (A,L,G)」を**導出**する。現 `SibleyDadeHypothesis.tau
    := dadeIntegralCharacterMap` は**導出後の operative τ** を採用 (engine 直結ゆえ実用上正しいが (b) literal ではない)。
    完全 faithful には (i) τ := (Ind_L^G restrict) field + Dade 一致補題、または (ii) 現状維持 + docstring で
    「(5.2.b) による同一視後の τ」と明記 (現状)。**推奨 (ii)** (engine が Dade 写像専用ゆえ; 一致は repo に
    `dadeIntegralCharacterMap_apply_of_support` 既存)。次セッションで判断。
- (c) **次のcase のいずれか (= 真の hypothesis disjunction、field 化必要)**:
  - (c1) `L` is Frobenius group with kernel `H` ⟹ `IsFrobeniusGroup ↥L H W1` (要 Isaacs Ch06 FrobeniusGroup import;
    namespace/arg 順を build で確認)。
  - (c2) Hyp (4.6) [=`S06.CertainTypeHypothesis (sharpImage H) L`] が `K=H`, `A=H^#`(=sharpImage H, 構成上自動),
    **w₂ prime** (`(Nat.card cert.W2).Prime`), **W₂⊂[H,H]** (`cert.W2 ≤ ⁅H,H⁆`) で成立。
  - **⚠️ (c2) の判断要 (faithful 性の核)**: cert は自前の `dade`/`W1` field を持つ。原文は明示しないが proof は
    τ=cert の Dade isometry の一致に依存 ⟹ **`cert.dade = dade` (同一 Dade 데이터) と `cert.W1 = W1` を制約に
    入れるべきか**を Peterfalvi 精読で確定する (入れないと under-constrained=unprovable、誤って入れると
    over-constrained)。`SibleyCase G L H W1` inductive (c1=frobenius / c2=certain+3-4制約) を S08 に。
- **swap (step 2c, 残)**: 上記 (c) field 追加で **faithful 完成** → `sibleySetup_is_coherent` を
  `SibleyDadeHypothesis` に restate (sorry) → legacy `SibleySetup`/`OddOrderSpecialization`/`DescentHypothesis`/
  `coherence_tau_inner_eq` 削除・`coherence_inner_eq_on_supported` retype → full build + AxiomsCheck。
  **(c) を faithful に決めるまで swap しない** (over/under-constrained statement は anti-scaffold)。

#### ✅✅ T1 COMPLETE (2026-06-01, commits 48af3d5 / 53bbbf9, full build + AxiomsCheck green, sorry 不変=2)
- **2c-i (48af3d5)**: `cases` field 追加 = (6.8)(c) disjunction `IsFrobeniusGroup ↥L H W1 ∨ (∃ cert :
  S06.CertainTypeHypothesis (sharpImage H) L, cert.dade=dade ∧ cert.K=H ∧ (Nat.card cert.W2).Prime ∧
  cert.W2 ≤ ⁅H,H⁆)`。`SibleyDadeHypothesis` が (6.8)(a)(b)(c) 全 faithful に。Frobenius import 追加。
- **2c (53bbbf9) = swap**: `sibleySetup_is_coherent` を `SibleyDadeHypothesis` に retarget
  (goal = `IsCoherent (dadeIntegralCharacterMap …) S H^#` = engine 産出形)。legacy `SibleySetup`/
  `CoherenceTarget`/`coherence_tau_inner_eq`(FT で偽)/`coherence_inner_eq_on_supported` 削除。
  `IndChainDecomposition.ofIsCoherent` (τ 直接取り) 無変更。net sorry 不変 (S08 6.8 + S09 7.10)。
- **(4.6)↔(6.8) 解明 (記録)**: (4.2) `L=K⋊W₁`; (4.6)(c) `W₂⊂H⊂K`; (6.8.c2) "H=K" ⟹ **(4.6)の K = (6.8)の H**
  ⟹ `cert.K = H` が正に faithful。`cert.W1 = W1` は **入れない** (S06 の `W1⊔W2=⊤` と W₂⊆[H,H]⊆H が
  衝突し c2 vacuous 化の恐れ)。
- **残 (T1 後の本線)**: (i) ~~S06.CertainTypeHypothesis の (4.6)-faithfulness 監査~~ **✅ 完了 (commit
  e6090a0)**: `W1⊔W2=⊤` は**実バグ確定** ((4.2)(c) `W=W₁×W₂` は L の真部分群、`W₂⊊K` ゆえ; L=W₁×W₂ は
  L=K⋊W₁ と矛盾)。load-bearing 0 (誰も construct せず、`.dade/.K/.W2` のみ参照) ⟹ 安全に修正。`W_sup`
  削除し真の (4.2): `isComplement K W1`/`W1,W2 cyclic`/`W2≤K`/`centralizer_W2 (C_K(x)=W₂)`/`W_odd` 追加。
  + (6.8.c2) を `cert.W1 = W1` (共有 complement) で強化。**full (4.6)** ((3.1)-for-W, (4.6.c) H with
  W₂⊂H⊂K, Dade A-bounds) は §6 拡充時の課題だが (6.8.c2) は "Hyp(4.6) with H=K" ((4.6)H が K に collapse)
  ゆえ (4.2) core で足りる。(ii) tau=Ind-vs-Dade は operative Dade 採用で確定 (docstring 明記済)。
  (iii) (6.8) proof 本体 = T6–T11 (Y coherent via 6.34 → X coherent → glue)。

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

## D. (6.8) proof 着手 (T6, 2026-06-01)

- **✅ engine unblock (commit 17 本目)**: `coherentEqualDegree_fromDade` (S07:4713) の support 仮説を
  **個別 `(χ j).support ⊆ A` → 差分 `(χ j − χ 0).support ⊆ A` (`hsuppdiff`)** に弱化。動機 = 誘導既約
  `Ind θ` は `Ind θ(1)=|W₁|≠0` で個別には A=H^# 上に supported でない (1 で非零) が、**等次数差分は 1 で消える**
  (`(η_j−η_0)(1)=|W₁|−|W₁|=0`) ので差分 support なら満たす。下層 `coherentEqualDegree` (S07:2940) は元々
  差分 support のみ要求、唯一 個別を使う helper `dadeIntegralCharacterMap_inner_eq_on_supported_span` も
  「与えた元の support を導く」だけ ⟹ `S := {差分}` で適用可。caller 0 ゆえ in-place 弱化が安全・厳密に一般化。
  build+AxiomsCheck green。
- **残 T6 (Y coherent の family 構成側)**: `coherentEqualDegree_fromDade hyp.dade hyp.hconj hn η hηinj hηdeg
  hηsuppdiff h1notA : IsCoherent hyp.tau (range η) H^#` を呼ぶには:
  (1) **Y family** `η : Fin m → IrreducibleCharacter ↥L` を `Irr(H/H')∖{1}` (= H' を核に含む θ、degree 1) の
      `Ind_H^L θ` として構成 (`m = |Irr(H/H')|−1 = |H/H'|−1`)。
  (2) **各 η_j 既約** = 6.34 `isIrreducibleCharacter_induce_of_inertia_eq` (要 `inertia(θ)=H`)。
  (3) **`inertia(θ)=H` (自由作用) = T6 の律速・深い blocker (未着手)**: (c1) Frobenius / (c2) から θ≠1 の
      stabilizer 自明を導く。**精査結果 (2026-06-01)**: repo `brauer_permutation_lemma'`
      (BrauerPermutationUnconditional:196) は **inversion 専用** (`#RealIrr=#RealClass`)、一般 action 不可。
      一般版 `brauer_permutation_lemma` (BrauerPermutation.lean:264) は任意 permutation+compat を取るので、
      **W₁(⟨g⟩)-共役 permutation を character table 上に構成して instantiate** すれば良いが substantial (新 infra)。
      群レベルの自由作用は Frobenius で既存 (`IsFrobeniusGroup` → `FrobeniusActionTI.stabilizer_eq_bot` /
      `fixedPointFree_toMulAut`)。⟹ 残 = 「群レベル自由 ⟹ Irr レベル自由 (inertia=H)」の **general Brauer
      for conjugation の instantiation** (別 multi-session 課題; これが (6.8)/§9-§16 の Frobenius-induced
      irreducibility 全体の鍵)。
  (4) ✅ **等次数 infra done** (commit dde1dcd): `SibleyDadeHypothesis.index_H_eq_card_W1` (`[L:H]=|W₁|`
      via `Subgroup.IsComplement.card_right` on `hyp.split`)。6.34 degree `[L:H]·θ(1)` + θ degree 1 と
      合わせ `η_j(1)=|W₁|`。
      2026-06-02 追記: `IndChainDecomposition.inner_chi_eq_ite` で (6.8) consumer の output
      orthonormality を 1 lemma に集約済み。
  (5) **差分 support** `(η_i−η_0).support ⊆ H^#`: 等次数で 1 消失 + 誘導 support が H 上 (H⊴L で共役不変) ∖{1}。tractable。
  → **T6 の律速 = (3) general Brauer for conjugation** (新 infra)。これが立てば 6.34 + (4)/(5) + engine
    (difference-support 版) で T6 完成。T7 (X 特徴付け, 同じく 6.34/free-action 依存) / T8 (DadeChainStep) /
    T9-T11 (glue) は後続。
