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
| T0 | [Is]Cor 2.30 producer `θ(1)²≤[H:Z]` (Z≤Z(H)) — **✅ 既存と判明 (2026-06-02 監査)**: `SchurCenterBound.lean` の `finrank_sq_le_index` + character 形 `IsIrreducibleCharacter.exists_degree_sq_le_index` | — | — | ✅ **完了** |
| T1 | **SibleySetup 再構築** (§B) | ~120 | — | ✅ |
| T2 | (5.2.a/b) discharge → `S07.Hypothesis` の tau=τ_D | ~120 | T1 | 一部 |
| **T3** | **(6.7) 上位定理** `ψ(z)≡ψ(1) mod \|P\|` — **✅ 完了 (2026-06-02 R1, 67164c6)**: `peterfalvi_67_of_odd`@新 `SylowTICongruence.lean`。`peterfalvi_67`@ClassSumAlgebra の残仮説 2 つを放電: hreal=⟦z⁻¹⟧≠⟦z⟧ (\|L\| odd, `not_isConj_inv_of_isTISubset`) + hone=a₁₁≡1+a₁₂ (**自明指標特殊化** `nonidentityZClassCoeffSum_cong_of_isTISubset`: 自明表現で ω(C)=\|C\|, 同じ collapse 機構 + \|C₁\| cancel)。結論は [ALGMOD \|P\|] 形; **ℤ-合同への昇格は consumer 側** ((6.8.2.2) は Res_Z ψ=aρ_Z+b1_Z から b∈ℤ 既知 → `isIntegral_rat_imp_int`)。書籍の「ψ(z)∈ℤ」前半は未形式化 (consumer 不要; 要るなら Res∈ZIrr(Z)+`mem_ZIrr_inner_int` 経由 ~80行) | — | — | ✅ **完了** |
| **T4** | **(1.9)Galois作用+(5.9.a)coherence不変** — **✅✅ 完了 (2026-06-02 R1)**。(1.9) = `CyclotomicGaloisAction.lean` (`exists_complexRingEquiv_mapRingEquiv_eq_pow` 一様σ値公式 + (1.9.a) CRT 形 + ℂ延長定理 + 有限位数 trace 公式)。(5.9.a) = `S07_CoherenceGalois.lean` **`IsCoherent.extension_mapRingEquiv_comm`**: Dade 基底 coherence 拡張 τ₁ は S 上で σ と可換 ((τ₁χ)^σ = τ₁(χ^σ))。入力 = `dadeIntegralCharacterMap_mapRingEquiv_comm` (Dade 点評価 ⟹ σ-可換) + `dadeIntegralCharacterMap_apply_one` (1 で消滅 ⟹ 一様符号) + `exists_zsmul_irreducibleCharacter_of_inner_self_one` (norm-1 ⟹ ±Irr)。**star-可換仮定不要** (内積を σ 輸送しない) ので wild σ に直接適用可 — `IsCoherent.galoisTransport` の hσ 弱化は (5.9.a) には不要と判明 (galoisTransport 自体は σ∈{id,conj} 専用のまま; 必要になれば値レベル弱化可)。consumer = (6.8.2.1): (1.9.b)+(5.9.a)+「(η^u−η)^τ が Z 上で消える」(Dade 点評価から導出可) | — | (1.9)✅ (5.9.a)✅ | ✅ **完了** |
| T5 | [Is]Lem 2.27 `Res_Z θ=θ(1)·φ` (Z≤Z(H)) — **✅ 完了 (2026-06-02 R1, 376f4e6)**: `IsIrreducibleCharacter.exists_central_linear_restriction`@SchurCenterBound (φ linear ∧ φ(1)=1 ∧ Res=χ(1)•φ ∧ pointwise 形; φ≠1 は pointwise+χ(1)≠0 から)。+ `dadeIntegralCharacterMap_apply_mem` (τ の A 上値復元, (6.8.2.1) の評価 step)@S07_CoherenceGalois (fe8895d) | — | — | ✅ **完了** |
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

## D'. (6.8.2.1) 一般形 完了 (2026-06-03, R1 lane, 069348a)

S08 非依存の一般形 2 本が `S07_CoherenceGalois.lean` に landed (axiom-clean):
- **`IsCoherent.extension_apply_coe_pow_eq`** (core): (5.9.a) 状況 + η が x で degree 値 + σ が ord(x)-乗根上 `(·^k)` ⟹ `(τ₁η)(x^k) = (τ₁η)(x)`。chain = (1.9.b) 値公式 (τ₁η∈ℤ[Irr G], hlat) → (5.9.a) 可換 → δ=η^σ−η の Dade A-値復元 (`dadeIntegralCharacterMap_apply_mem`) で δ(x)=0。
- **`IsCoherent.extension_constant_on_sharp_of_prime`** (=(6.8.2.1)): Z 素数位数 w₂, Z^#⊆A, η は Z 上 degree 値 (応用: Z⊆H'⊆Ker η) ⟹ **τ₁η は Z^# 上定数**。σ は `Nat.exists_eq_pow_mul_and_not_dvd` + `exists_complexRingEquiv_pow_and_fixed` で内部生成; x が素数位数 Z を生成し y=x^k。
- **case-B 接続に必要な残り**: S := range(Y-family) に対する hSu (∀σ 閉性; Ind∘mapRingEquiv 可換 + galoisMap で ~40行) / hlat (τ₁(Y)⊆ℤ[Irr G]; coherence 構成から) / hker (Z=cert.W2≤H'≤Ker η; 誘導指標の値) / hZA (W₂^#⊆H^#-image)。T6 の Y-family 構成と同時に配線。

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
      `Ind_H^L θ` として構成。⚠️ **濃度訂正 (2026-06-03, §E 参照)**: `m = |H/H'|−1` は**誤り**。
      `Ind_H^L(θ^g)=Ind_H^L θ` (`induce_conjBy_eq`) ゆえ Ind は W₁-軌道上で定数、inertia(θ)=H で軌道サイズ=|W₁|
      ⟹ 真の濃度は **`m = (|H/H'|−1)/|W₁|`**、η は**軌道代表 1 つずつ**で単射。
  (2) **各 η_j 既約** = 6.34 `isIrreducibleCharacter_induce_of_inertia_eq` (要 `inertia(θ)=H`)。
  (3) **`inertia(θ)=H` (自由作用) = T6 の律速・深い blocker (未着手)**: (c1) Frobenius / (c2) から θ≠1 の
      stabilizer 自明を導く。**精査結果 (2026-06-01)**: repo `brauer_permutation_lemma'`
      (BrauerPermutationUnconditional:196) は **inversion 専用** (`#RealIrr=#RealClass`)、一般 action 不可。
      一般版 `brauer_permutation_lemma` (BrauerPermutation.lean:264) は任意 permutation+compat を取るので、
      **W₁(⟨g⟩)-共役 permutation を character table 上に構成して instantiate** すれば良いが substantial (新 infra)。
      群レベルの自由作用は Frobenius で既存 (`IsFrobeniusGroup` → `FrobeniusActionTI.stabilizer_eq_bot` /
      `fixedPointFree_toMulAut`)。2026-06-02 追記: general Brauer Layer B は
      `ConjugationBrauer.lean` として landed (`IrreducibleCharacter.conjByPerm`, `ConjClasses.conjByPerm`,
      `card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm`)。Layer C のうち、
      fixed conjugacy classes count = 1 から nontrivial Irr 非固定を出す bridge も landed
      (`not_mem_inertia_of_ne_trivial_of_card_fixedClasses_eq_one`)。2026-06-02 追記: Frobenius case
      (c1) は `IsFrobeniusGroup.centralizer_kernel_le` から `inertia_eq_of_frobeniusGroup` を経由し、
      6.34 まで合成した `isIrreducibleCharacter_induce_of_frobeniusGroup` が landed。
      ⟹ 残 = Y=S(Hprime) family construction / engine call wiring、および case c2 側の inertia discharge。
  (4) ✅ **等次数 infra done** (commit dde1dcd): `SibleyDadeHypothesis.index_H_eq_card_W1` (`[L:H]=|W₁|`
      via `Subgroup.IsComplement.card_right` on `hyp.split`)。6.34 degree `[L:H]·θ(1)` + θ degree 1 と
      合わせ `η_j(1)=|W₁|`。
      2026-06-02 追記: `IndChainDecomposition.inner_chi_eq_ite` で (6.8) consumer の output
      orthonormality を 1 lemma に集約済み。
      2026-06-02 追記: SibleyDadeHypothesis.induce_apply_one_eq_card_W1_of_degree_one を追加し、
      degree-one source θ から η_j(1)=|W₁| を直接放電できる形にした。
  (5) ✅ **差分 support**: support_sub_induce_subset_sharpImage_of_degree_one を S08 に追加。
      normal H で Ind_H^L θ は H 上に supported、degree-one source の等次数で 1 が消えるため、
      (Ind θ_i - Ind θ_0).support ⊆ H^# を直接放電できる。
  → **T6 の現律速** = Y=S(Hprime) family construction / engine call wiring + case c2 inertia。
    c1 Frobenius path は inertia=H → 6.34 → degree-one source の η_j(1)=|W₁| まで landed。
    c2 には同等の inertia discharge がまだ必要。
    T7 (X 特徴付け, 同じく 6.34/free-action 依存) / T8 (DadeChainStep) /
    T9-T11 (glue) は後続。

## E. ✅ T6 設計完全確定 (2026-06-03, 3 並列 Plan agent + mmd 照合、数学的不確実性ゼロ)

引っ越し後の再開セッション。2 つの設計問題 (Y-family 構成 / inertia=H discharge) を Plan agent で詰め、
c2 bridge を mmd (4.2)(4.5) で逐語検証した。**残りは機械的 Lean 記述のみ** (新数学なし)。

### 訂正 2 件 (旧 §C/§D の framing バグ — 両 agent 独立に発見)
1. **orbit 濃度**: 上記 (1) 訂正参照。`m = (|H/H'|−1)/|W₁|`、η=Ind∘θ は軌道代表で単射。
   `hηinj` は source 単射でなく **cross-Mackey 内積=0 (非共役) vs =1 (norm)** から。
2. **`hn : 2 ≤ n` は局所構成不能**: 「H nilpotent≠⊥ + |L| odd」からは `|H/H'|≥3` (⟹ Y 非空) 止まり。
   `m ≥ 2` は (6.8.3) の (6.5) chief-factor 背理法由来 ⟹ **caller 供給仮説** (局所捏造=scaffolding)。

### c1 (Frobenius): 新規 infra ~0、即 build-green
`isIrreducibleCharacter_induce_of_frobeniusGroup` (InducedIrreducible:291, 任意非自明 θ に一般) が直接適用。

### c2 (CertainTypeHypothesis): Route 1 確定、Ḡ=↥L⧸H' 実現
- **mmd 検証**: (4.2.a)「W₁ cyclic **Hall**」⟹ `(|K|,w₁)=1` は教科書帰結 (faithful, scaffolding でない)。
  c2 論証は (4.5.b) 逐語 = [Is]6.32(landed Brauer) + (1.5.b)(landed 6.34)。Y-family は `W₂⊆[H,H]`
  (`cases` c2 既存) で **H/H' 上 FPF** (fixed=1) と clean に出る。
- **核心の気付き**: 抽象 MulAut 用 Brauer は不要。`Ḡ:=↥L⧸H'`, `H̄:=H.map(mk' H')⊴Ḡ` (abelian) と置くと、
  Ḡ 内の元 `q̄=mk' H' g` による共役が**既存 `ClassFunction.conjBy` engine そのもの** ⟹ Brauer 新規コード 0。
- **新規 lemma (ConjugationBrauer.lean 末尾、`inertia_eq_of_freeAction`@:229 を mirror)**:
  - `quotientSubgroupHom hNH : ↥H →* ↥(H.map(mk' N))` 余制限 + 全射 (~15 LOC)
  - **Lemma A** `conjBy_compHom_quotientSubgroup` (inflation–共役 equivariance; `compHom_apply`/`conjBy_apply`
    が rfl ゆえ機械的, ~20 LOC) — **repo に equivariance 補題は無い (grep 確認済)**、これが核
  - **Lemma A′** `mem_inertia_iff_mem_inertia_quotient` (`compHom_injective_of_surjective` 経由, ~12 LOC)
  - **Lemma B** `inertia_eq_of_freeAction_on_abelianization` (le_antisymm, ~30 LOC)
  - **Lemma C** `inertia_eq_H_of_c2` @S08 (cert.centralizer_W2 + Hall + B1′ を Lemma B に供給, ~35 LOC)
- **隠れコスト 2 件 (先の楽観的見積りを上方修正)**:
  - **B1′ は wrapper call でなく新規 ~45 LOC**: landed `quotient_centralizer_inf_kernel_eq_bot_of_fixedPoint_lift`
    (S03:307) の前提は `centralizer⊓K=⊥` (=H 上 FPF) で **c2 では偽** (C_H(g)=W₂≠1)。c2 の内容は H/H' 上 FPF。
    ⟹ `coprime_fixedPoints_quotient` (Isaacs 3.28, ForwardFromCh03:808) を直接呼び、fixed point を ⊥ でなく
    `W₂⊆H'` に着地させる新コード (S03:202-251 を mirror)。材料は全 landed。
  - **inflation 全射性の一般化 ~15 LOC**: `exists_inflate_eq_of_subset_characterKernel` (InflationCharacter:255)
    は whole-group `mk' N` 用、subgroup 余制限 `q:↥H→H̄` 用に任意全射へ一般化 (proof は全射性のみ使うので素直)。
- **Hall 仮説の追加**: `SibleyDadeHypothesis` に `H_W1_coprime : Nat.Coprime (Nat.card ↥H) (Nat.card W1)`
  field (または c2 `cases` 存在子に thread)。(4.2.a) 由来で dischargeable、(6.8) 構成時 ((7.10)/§9) に放電。

### 確定 LOC + 実装順
| # | 内容 | file | LOC |
|---|------|------|-----|
| 1 | `linearIrreducibleCharacter` infra (1-dim rep, hθ_one 自動, 単射) | 新 `LinearCharacter.lean` | ~110 |
| 2 | `card_linearCharacters = card(Abelianization H)` (mathlib duality) | 同上 | ~40 |
| 3 | cross-Mackey `card_mul_inner_induce` + `inner_induce_eq_zero_of_not_conj` (hηinj 用) | InducedIrreducible | ~55 |
| 4 | unification `isIrreducibleCharacter_induce_of_degree_one` (c1/c2 case split→6.34) | S08 | ~30 |
| 5 | c2 bridge (quotientSubgroupHom/Lemma A/A′/B + inflation 一般化 + B1′ + Lemma C + Hall field) | ConjugationBrauer/InflationCharacter/S08/S03 | ~190 |
| 6 | `coherentYFamily` (hn・軌道代表・irr を入力→engine) | S08 | ~70 |

**実装順 (c1-first で早期 build-green)**: #1→#2→#3→#4(c1分岐)→#6 で **c1 のみ build-green マイルストーン到達**
(coherentInducedDegreeOneFamily@S08:292 は landed なので Y coherent が c1 で閉じる)。c2 は #5 で後追い、
#4 の c2 分岐 sorry を埋める。**seam**: `coherentYFamily` は (hn[背理法 context], 軌道代表 linear sources,
pairwise 非共役) を入力に取り Y coherent を産む。各代表の inertia=H/既約性は #4-5 が供給。
T7 (X) → T8 (DadeChainStep) → T9/T10 (glue) → T11 (X∪Y=S + 最終 assembly) は後続 (critical path 不変)。

### ✅ 実装進捗 (2026-06-03, c1 path build-green)
**#1/#3/#4(c1)/#6 landed, full `lake build OddOrder` green, AxiomsCheck 登録 (#1/#3 の sorry-free 3 補題)**:
- **#1** `OddOrder/GroupTheory/RepresentationTheory/LinearCharacter.lean` (新): `linearClassFunction` /
  `linearIrreducibleCharacter` (χ:H→*ℂˣ ⟹ 1-dim rep `χ•id`, `isIrreducible_complex_rep`) +
  `_apply`/`_apply_one`(degree 1)/`_injective`/`_eq_trivial_iff`。`SchurCenterBound` の rep 構成を template。
- **#3** `InducedIrreducible.lean`: `card_mul_inner_induce` (2 引数 Mackey, self 版の near-copy) +
  `inner_induce_eq_zero_of_not_conj` (非共役 irreducible ⟹ ⟨Ind,Ind⟩=0; `conjBy_conjBy_inv` で矛盾)。
- **#4** S08 `isIrreducibleCharacter_induce_of_degree_one` (c1 分岐 = `isIrreducibleCharacter_induce_of_frobeniusGroup`
  で **sorry-free**; **c2 分岐のみ sorry** = S08:~334、唯一の新規 sorry、T6 §5 bridge 待ち)。
- **#6** S08 `coherentYFamily` (**sorry-free**): hyp+[H.Normal]+hn+χ+hpairwise+hirr ⟹ `Y=range(Ind∘linear∘χ)`
  coherent。hηinj は #3+norm-1(`irreducibleCharacter_inner_eq_ite`)、hθ_one は #1、engine= `coherentInducedDegreeOneFamily`。
  注: signature の `IrreducibleCharacter.conjBy` が `[H.Normal]` を要求するため instance binder で供給 (field は同 signature 内で instance 化不可の Lean 制約)。
- **#2 (card 列挙) は未実装** = T6 coherence には不要 (coherentYFamily は family を入力に取る); enumeration/T11 degree-sum 用に後続。
- **残**: #5 (c2 inertia bridge, S08:~334 sorry を埋める) → その後 coherentYFamily を実 family で呼ぶ (6.8) 本体 (T9–T11)。

### ✅ #5 完了 (2026-06-03, c2 inertia bridge — S08 c2 sorry 除去, full build green, axiom-clean)
**`isIrreducibleCharacter_induce_of_degree_one` の c2 分岐を `inertia_eq_H_of_c2` で閉じた。唯一残る
S08 sorry は capstone `sibleySetup_is_coherent` のみ。** 全補題 `[propext, Classical.choice, Quot.sound]`
のみ依存 (sorryAx なし、`#print axioms` 確認済)。

**追加した Hall 仮説 (faithful, scaffolding ではない)**: `SibleyDadeHypothesis.cases` の c2 連言に
`∧ Nat.Coprime (Nat.card ↥H) (Nat.card W1)` を追加 (S08:~202)。これは Peterfalvi (4.2.a) 「W₁ は L の
cyclic **Hall** subgroup」= `|W₁|` と `[L:W₁]=|H|` が互いに素、という本物の (6.8) 事実。`SibleyDadeHypothesis`
を構成する箇所はリポジトリに皆無 (grep 確認) なので連言追加は安全、将来カリア構成時に honest に供給される。

**証明骨子 (Route Y, 商 `Ḡ=L/⁅H,H⁆`・像 `H̄=H/⁅H,H⁆` で一貫)**:
- `θ` linear ⟹ `⁅H,H⁆.subgroupOf H = commutator ↥H ⊆ ker θ` (新 `IsIrreducibleCharacter.map_mul_of_apply_one_eq_one`
  /`apply_commutatorElement_eq_one_of_apply_one_eq_one` @ LinearCharacter.lean: 1-dim rep ⟹ `ρ g = θ(g)•id`
  ⟹ θ multiplicative ⟹ commutator を 1 に送る)。
- `θ` を `q : ↥H ↠ ↥H̄` に沿って `θ̄ : Irr H̄` から inflate (新 `exists_compHom_eq_of_subset_characterKernel`
  @ InflationCharacter.lean: `exists_inflate_eq` を任意全射準同型へ一般化、`quotientKerEquivOfSurjective` で transport)。
- **B1′** `C_{H̄}(w̄)=⊥` (w̄∈W̄₁∖1): 新 S03 補題 `quotient_centralizer_inf_kernel_eq_bot_of_fixedPoint_lift_of_le`
  (既存 `=⊥` 版を `C_K(x)⊓K ≤ N` 版へ緩和; c2 では `C_H(w)=W₂⊆⁅H,H⁆=N` で `=⊥` は偽だが `≤N` は真) +
  `fixedPoint_lift_of_generator_quotient_fixed` (Isaacs 3.28, coprime lift)。coprimality は Hall 仮説 + `orderOf w ∣ |W₁|`。
- H̄ abelian + B1′ ⟹ Brauer で `#fixed conj-classes(w̄)=1` (新 `card_fixedPoints_conjClassPerm_eq_one_of_commute_of_centralizer_inf_eq_bot`
  @ ConjugationBrauer.lean) ⟹ `w̄ ∉ I_Ḡ(θ̄)` (既存 `not_mem_inertia_of_ne_trivial_of_card_fixedClasses_eq_one`)。
- **inertia transfer** `w∈I_L(θ) ↔ w̄∈I_Ḡ(θ̄)` (新 `conjBy_compHom_eq_compHom_conjBy`/`mem_inertia_compHom_iff`
  @ ConjugationBrauer.lean: inflation–conjugation 同変性)。
- `I_L(θ)=H` を `le_antisymm`: `≥`=`subgroup_le_inertia`; `≤`= 一般 `g∉H` を complement `L=H⋊W₁` で `g=h·w`
  (w∈W₁∖1) に分解、`h∈H⊆I_L(θ)` を吸収して `w∈I_L(θ)` に帰着、上記 transfer で矛盾。

**新規 generic 補題 (再利用可能)**: ClassFunction.compHom_comp; LinearCharacter の 3 補題;
InflationCharacter.exists_compHom_eq_of_subset_characterKernel; ConjugationBrauer の abelian-bridge +
transfer 2 補題; S03 の `≤N` quotient-FPF 補題。

## F. T7 (X 特徴付け) 詳細設計 (2026-06-03, 2 並列 Plan agent + mmd L136-244 / (4.5)@04.6 照合)

**(6.8) 全体構造 (mmd L150-244)**: `S coherent` を**背理法**で示す。(6.5) で「H 非可換 p-群」に還元
(d_i∈ℕ=p冪, Z(H)∩H'≠1)。**重要 (anti-scaffold)**: p-群は `SibleyDadeHypothesis` の field に**しない**
((6.8) statement は H nilpotent のみ仮定; field 化は over-constrain で §9 caller が使えない)。代わりに
`sibleySetup_is_coherent` を `by_contra hnc` で開き、`peterfalvi_65_reduction hyp hnc` で p-群構造を
**背理法分岐内の局所仮説**として得る (peterfalvi_65_reduction は別 ~200-300 LOC task=T9/T11 圏、T7 外)。

**定義** (S08 `namespace SibleyDadeHypothesis` に直接 def; `FiltrationData`@S08:42 は dead legacy で不使用・将来削除):
- `SsubFiltration hyp (A:Subgroup ↥L) := {Ind_H^L θ | θ≠1, A.subgroupOf H ⊆ ker θ}` (= (6.1) S(A))
- `Z : Subgroup ↥L` — case A `(center ↥H).map H.subtype ⊓ ⁅H,H⁆` / case B `cert.W2`。`Z⊆H'` (caseA=inf_le_right / caseB=hW2), `Z⊆Z(H)` (caseA=inf_le_left / caseB=要 W₂⊆Z(H)=case B 定義), `Z≠⊥` (caseA=p-群還元由来=分岐内, caseB=cert.W2_nontrivial)
- `SsubZ hyp Z := SsubFiltration hyp Z`; `Xset hyp Z := hyp.S \ hyp.SsubZ Z`; `Y = SsubFiltration hyp ⁅H,H⁆`
- 推奨: `SibleyCaseAB` inductive (caseA/caseB, 各 branch が Z の 3 事実を供給)

**T7-c1 (Frobenius): 機械的・sorry-free, ~255 LOC**。S03 に既 landed の atoms で組める:
`not_subsetCharacterKernel_of_not_induce`(S03:589, (1.6.a) 逆)/`subsetCharacterKernel_induce_of_subgroupOf`
(S03:563)/`exists_inner_induce_ne_zero`(S03:636)/`irreducibleCharacter_mem_characterKernel_of_natSum_value_eq`
(S03:696, (6.6) G2.2 keystone)。`S⊆Irr L` は `isIrreducibleCharacter_induce_of_frobeniusGroup` (任意非自明θ)。
`X={χ∈Irr L|Z⊄ker χ}` は `S⊆Irr L` + 1.6.a bridge。`Xset⊆Irr L`=`diff_subset`。

**T7-c2 = `X⊆Irr L` (= 「θ≠1, Z⊄ker θ ⟹ inertia(θ)=H」+ 6.34) — 設計確定 (2026-06-03 brick② focused 設計で大幅訂正・縮小)**:
- **🔴 重大訂正 1: `X⊆Irr L` は case A 限定**。**case B は X⊆Irr L を必要としない**: mmd (6.8.2) L178-256 は
  可約 χ=Ind_H^L θ (Z⊄ker θ) を**許し**、(6.8.2.1/2/3) の isometry 拡張 (τ₂, η₁^τ₂=Y) で coherence を出す。
  ⟹ case B は **T10** (前提 T3/T4/T5 全 landed)。T7-c2 は **case A の X⊆Irr L のみ**にスコープ。
- **🔴 重大訂正 2: counting route (旧 ②a-d) は dead end**。②c (`#fixed classes H = #fixed classes H/Z`) は
  ConjClasses 対応として偽 (inj/surj 両方失敗; lift は Glauberman-Isaacs 類対応=未 landed・重い) で、真値は
  µ_ij 由来。**旧記載の「brick 2 つ / ~400-500 LOC」は撤回**。
- **✅ case A の clean 直接証明 (~95-115 LOC, sorry-free, 残不確実性ゼロ)**: case A 定義 `Z(H)∩W₂=1` ⟹
  `C_Z(w)=Z∩C_H(w)=Z∩W₂=1` ⟹ **w は Z 上 FPF** (mmd (6.8.3) L256 と一致)。θ が w-fixed なら [Is]2.27
  (`exists_central_linear_restriction`, Z≤Z(H)) の中心線形指標 φ が w-不変 → **新補題**
  `map_eq_one_of_fixedPointFree_invariant` (mathlib `MonoidHom.FixedPointFree.commutatorMap_surjective`,
  `a=b/fb` + 不変性 ⟹ φa=φb/φ(fb)=1, ~10 LOC) で φ=1 ⟹ Z⊆ker θ = **brick② (case A)**。
  wrapper `inertia_eq_H_of_c2_caseA` は T6 の le_antisymm/complement-split (S08:466-487) を**流用** (linearity 不使用) +
  `isIrreducibleCharacter_induce_of_inertia_eq` (6.34, 一般 θ)。**case-B は brick② 偽ゆえ touch しない**。
  - 新規: `map_eq_one_of_fixedPointFree_invariant` (~10) + `subset_characterKernel_of_inertia_caseA` (~55-75, FPF-equiv 構成が主) + wrapper (~30, 流用)。landed: 2.27 / FixedPointFree / 6.34 / S06 centralizer_W2。
- 要 (1.6.a) `A⊆ker θ ⟺ A⊆ker Ind θ` (case A の特徴付け, ~50 LOC, 未形式化だが小)。
- **case A の Z≠⊥ は p-群還元由来 (背理法分岐内)**; case-split `Z(H)∩W₂=1` は branch 仮説。

**T7→T8 (6.6) engine interface**: `peterfalvi_66_coherence_of_X_from_dade`(S07:5249) + `DadeChainStep`(S07:5065)
+ `coherentEqualDegree_fromDade`(S07:4842) + `exists_monotoneDegreeEnum`(S07:3661)。T7 が供給するのは
`Xset hyp Z`:Set + `Xset⊆Irr L` + `Xset={χ∈Irr L|Z⊄ker χ}`。degree-sum collapse (mmd L234) が hdeg_c に効く。
**⚠️ T8 境界 gap (T7 外だが要注意)**:
- **G1**: `DadeChainStep.hχsupp`(S07:5076) が**個別** `χ_i.support⊆H^#` 要求 — だが Ind θ_i は 1 で非零。
  Y-family は `coherentEqualDegree_fromDade` の差分 support 弱化 (S07:4713) で回避したが、`peterfalvi_66`/`DadeChainStep`
  は未弱化。`retarget_isCoherent_fromDade` の実 support 使用を読んで確認要 (差分のみ使うなら同様弱化で解決)。
- **G2**: `DadeChainStep.Dmem` per-member ψ=0 分解が T8 主負荷 (~300-450 LOC の大半)。

**T7 実装順 (c1-first)**: defs (Z/X/S(Z)/SibleyCaseAB ~95) → c1 特徴付け (S⊆Irr L / Xset_eq / Xset⊆Irr L ~100)
→ engine seam (~40) で **c1 build-green**。c2 は brick①②を後追い (~400-500, brick② 高リスク)。

## G. 🔴 方針監査結果 (2026-06-03, 4 並列 adversarial agent + 全 BLOCKER を自己再検証)

エラー頻度上昇を受けた全 spine 監査。**load-bearing な主張は grep/read で独立検証済**。

### BLOCKER (検証済・要対処)
- **(A) engine support-interface bug** [Agent 2+3 独立確認, 自己検証済]: `DadeChainStep.hχsupp`(S07:5076)/`retarget_isCoherent_fromDade`/`dadeOrthonormalCharacterImageFamily`(S07:4410) が **個別** `χ.support ⊆ supportInSubgroup A L` を要求。だが `A=sharpImage H` は 1 を除外、`χ=Ind_H^L θ` は χ(1)=|W₁|θ(1)≠0 ⟹ **X-member で偽=充足不能**。⟹ `peterfalvi_66_coherence_of_X_from_dade`(S07:5249) は実 X-family で **instantiate 不能 = T8 を塞ぐ**。抽象版 `peterfalvi_66_coherence_of_X`(S07:3934) は support field なしで健全。**内部は差分しか使わない**(両 agent が trace) ⟹ 修正 = Y-family が受けた差分 support 弱化 (`coherentEqualDegree_fromDade` S07:4842) を `DadeChainStep`/`retarget_isCoherent_fromDade`/`dadeOrthonormalCharacterImageFamily`/`dadeIntegralCharacterMap_inner_eq_on_supported_span`(S07:4326) に伝播。**T8 の前提タスク**(frozen-ish file の engine surgery、per-task LOC 見積りに未計上)。
- **(B) Track A/B 断絶 + 「実 sorry 2」の framing 誤り** [Agent 4, 自己検証済]: `card_G0_lower_bound`/`sibleySetup_is_coherent`/`IndChainDecomposition`/`FrobeniusFamily` は **defining file 外で消費者 0**。S09 は S08 シンボル不使用 ((6.8)→(7.10) は TODO コメントのみ)。`feitThompson`(FeitThompson.lean:21) は **body なし裸 sorry** (minimal-counterexample 還元 欠落)。実 FeitThompson 経路 = **Track B: BG.IsMinimalSimpleOdd + S16.Hypothesis → BG.AppC.final_contradiction**。「実 sorry 2 (0046/0044)」は **AxiomsCheck-guard 島のみ**の指標で、FeitThompson 推移閉包は ~144 sorry + opaque-Prop placeholder 多数 (vacuity risk は proof-fill 時、現状 consumer も sorry ゆえ benign)。**(6.8)/(7.10) は genuine な Peterfalvi 結果だが orphaned** — §10-16 が hoist しており、wiring は未構築の大タスク。**axiom-laundering / 循環は発見されず** (scaffold は honest)。

### STRATEGIC (検証要/対処要)
- **B4 m≥2 未解決** [Agent 3]: Y coherence ((1.4)) は n≥2 必須。plan §E は「caller 供給 (6.5 背理法由来)」とするが**導出が示されていない**。m=(|H/H'|−1)/|W₁|; (6.5) で H/H' は chief factor ⟹ W₁ が Irr(H/H')∖{1} に推移的なら m=1 で Y 非 coherent。要 Peterfalvi-level 解決 (odd-order FPF 境界 |H/H'|−1≥2|W₁| 等)。
- **Finding 1 H-Sylow** [Agent 1]: (6.7)=`peterfalvi_67_of_odd` は P Sylow 前提。(6.8) は P=H で適用 (mod |H|) ⟹ 「H^# TI p-群 ⟹ H∈Sylow」を T9/T10 が (6.5) 還元 context から放電要 (carrier にない)。
- **B1 (5.6) 反転欠落** [Agent 3]: (6.8.3) は (5.6) を**対偶**で使う (非 coherent ⟹ 次数和下界) が、engine は forward (`retarget_isCoherent` S07:2835) のみ。IsCoherent は Type なので `¬Nonempty(IsCoherent …)` の Prop-対偶 wrapper を書く要。T11 を塞ぐ (plan は「既landed」と誤記)。
- **B2 X-side degree-sum bridge 欠落** [Agent 3]: landed `sumNonInflatedDegreeSq_eq_index_mul`(InflationCharacter:374) は **Irr-L 側**和。(6.8.3) は **X 側** `Σχ(1)²/‖χ‖²` (case B で X は可約!) を扱う。bridge=(1.5.c,d) 共役崩壊は未 landed。T11 で要 (case A は両者一致ゆえ landed で足りるが case B は不足)。
- **Finding 3 / 「(4.2)-core で c2 足りる」未証明** [Agent 1]: plan の主張は (4.5) counting 経由なら (4.6)(b)(c)(d) 要。**ただし brick② の直接 FPF-on-Z 設計 (§F 訂正) が (4.5) を sidestep するので case A では moot** — brick② が正しく landed すれば Finding 3 は解消。
- **M1 (6.5) reduction は DAG node 欠落** [Agent 3]: (6.5)⟸(6.3)⟸(6.2)⟸(5.6)+(1.5) の深い依存、~200-300 LOC、T9/T10/T11 を塞ぐ。B1/B2 の機構を共有。
- **Finding 2 W-cyclic 欠落** [Agent 1, MINOR]: `CertainTypeHypothesis` に (4.2.c) W cyclic がない (消費者 0 で latent、(4.3)/(4.5) 構築時に必要)。
- **M2 I_L(φ)=L trap** [Agent 3, MINOR]: (6.8.2.2) は `[I_L(φ):Z] ≤ [L:Z]` 不等式形で足りる、=L を証明しようとすると hard/偽。T10 implementer 向け注意。

### VERIFIED-OK (健全確認 — 安心材料)
- **case-A-only X⊆Irr L** (V1): §F の訂正 (case B は X⊆Irr L 不要、reducible 許容) は mmd L160/L210 と一致・正しい。
- **tau = dadeIntegralCharacterMap は faithful な Dade map** (legacy global-isometry bug は解消済); IsCoherent core は (5.1) lattice-relative で faithful。
- **T4 (1.9)+(5.9.a) / T5 [Is]2.27 / T0 Cor2.30 健全** (axiom-clean 確認); 「wild-σ / star-commute 不要」は over-claim でない。
- **IndChainDecomposition + ofIsCoherent は faithful・proven** (orphaned だが正しい); (7.7.a)/(7.8)/(7.9) は honest 証明書 scaffold (laundering なし)。
- **brick② (T7-c2 case A) 設計は Finding 3 を sidestep** — (4.5)/(4.6)bcd 不要の直接 FPF route。

### 戦略的含意
本作業 (T6 完成, T7 設計) は **genuine な Peterfalvi 形式化**だが、現状 FeitThompson の実 critical path (Track B) には未配線。優先順位 = {(A)engine 修正して (6.8) 続行 / Track B (BG§7-16+S16/AppC+top-level 還元) に pivot / roadmap 全体を訂正版で再計画} の判断が必要。

## J. T8 (X-family DadeChainStep instance) leaf 分解 (2026-06-03, T7 完了後・active frontier)

engine (`peterfalvi_66_coherence_of_X_from_dade` S07:5593) + base (`coherentEqualDegree_fromDade`
S07:5109) + per-step (`DadeChainStep.advance` S07:5491) は全 landed (B surgery 完了)。残 = X=`Xset Z`
に対し engine の入力 — enumeration `e`/`pair`/`N` + base `S₀` coherence + 各 pair の `DadeChainStep`
instance (~30 field, S07:5399) — を構築。leaf 単位で (/goal 駆動, user 2026-06-03 承認):

- ✅ **T8.1** `xMember_characterFacts` (commit ccf17e2, axiom-clean): `hreal`/`hχχ`/`hχbarχbar`/`hχbarχ`/
  `hχχbar'`。非実 = (1.1) odd (`not_isReal_of_ne_trivial_of_odd_card'`) + `Xset_eq` の `Z⊄Ker χ` で χ≠1;
  ortho = `irreducibleCharacter_inner_eq_ite`。Frobenius case (χ 既約 = `isIrreducibleCharacter_of_mem_Xset_of_frobenius`)。
- ✅ **T8.2** `xMember_diffSupport` (commit 3e12608, axiom-clean, 初回 build green): `hdiffsupp`
  `(χ.conj−χ).support ⊆ supportInSubgroup (sharpImage H) L`。χ=Ind θ, H 正規 ⟹
  `support_induce_subset_of_normal` (InducedCharacter:343) で support⊆H; χ.conj−χ は 1 で消える
  (χ(1)=(n:ℂ) 実 via `exists_natDegree_charValue_one_dvd_card`) ⟹ ⊆ H^#=`sharpImage H`=map\{1}。standalone per-χ。
- ✅ **T8.3a/3b** `Xset_closedUnderConjugate` + `Xset_hasNoRealCharacters` (commit b6d0ce1, axiom-clean):
  set-level `ClosedUnderConjugate`/`HasNoRealCharacters (Xset Z)`。conj-closure = `Xset_eq` +
  `characterKernel_conj` (Z⊴L ⟹ Ker χ̄=Ker χ); no-real = T8.1 を quantify。**enumeration の入力**。
- **T8.3** degree data (`a`/`famRatio`/`famDegree`/`famDegree_chi`/`famRatio_chi1`): enumeration 依存ゆえ
  T8.6 と一体化 (induce_apply_one P1✅ + index_H_eq_card_W1✅ で χ(1)=|W₁|θ(1))。
- **T8.4** `Dmem` per-member ψ=0 分解 (`CharacterPsiDecomposition`) — §H/§I G2 主負荷、design-heavy、**/goal 不向き=直接実装**。
- **T8.5** `hdeg_c` (5.6) 次数不等式 `2a<∑aᵢ²/‖χᵢ‖²` — §G B2 (X-side degree-sum bridge) 要、design-heavy。
- **T8.6** enumeration: X を degree-monotone 列挙 (`exists_monotoneDegreeEnum` S07:3804)→共役 pair {χ,χ̄}、
  S₀=min-degree 等次数族→`coherentEqualDegree_fromDade` で base coherence。design。
- **T8.7** assemble → `peterfalvi_66_coherence_of_X_from_dade` → `IsCoherent τ X A`。
- → glue X∪Y (Y=T6✅) via `coherentUnion_of_glued` + (6.5)還元 (M1, §G) → capstone `sibleySetup_is_coherent`。

### J.1 design pass (2026-06-03, engine 通読・実 instance 構築可能性 確定)

**🟢 全 engine backbone が landed — fundamental blocker 無 (Frobenius case)**:
- enumeration: `exists_monotoneDegreeEnum` (S07:3804, degree-monotone e:Fin n→X) /
  `two_le_ncard_of_conjugate_closed_of_noReal` (3851, n≥2 ← T8.3a/3b) / `pairSet`/`pairUnion` (3866/3874) /
  `mem_pairUnion`/`pairUnion_eq_of_cover`/`pairUnion_eq_of_enumCover` (3915/3943/4031, cover→X 復元)。
- iteration: `coherentPairChain` (3969, N-帰納) / `coherentOfPairChainCover` (4007) — `peterfalvi_66_coherence_of_X_from_dade`
  (5593) が直接消費。
- base: `coherentEqualDegree_fromDade` (5109, 等次数 n≥2 族→coherence)。
- **Dmem 構成子 landed**: `decompositionDaFromDadeOfDiff` (S07:4708, B surgery) — `CharacterPsiDecomposition`
  struct (974) は B surgery で `tau1_inner_eq_on_support` を差分 sublattice に弱化済 ⟹ X-member (χ(1)≠0) でも
  構成可 (個別 support 不要)。`retarget_isCoherent_fromDade_X` (5314) / `DadeChainStep.advance` (5491) が使用。
- **hdeg_c machinery landed**: `two_mul_lt_sq_of_primePow_gap` (S07:1696) + `sumInflatedDegreeSq`
  (InflationCharacter:311)。**Frobenius case は X⊆Irr L (‖χ‖²=1) ⟹ X 側和=Σχ(1)² が Irr-L 側と一致** ⟹
  §G B2 (X-side bridge) は **case B のみの問題**, Frobenius case は landed で足りる見込み (要実装確認)。

**構築プラン (Frobenius case 先行)**: X=`Xset Z` に対し
1. n≥2: T8.3a/3b + X.Nonempty (←broader context/(6.5)) → `two_le_ncard...`。
2. enumeration e ← `exists_monotoneDegreeEnum`。**pairing 構成** (X を S₀=min-degree block + 共役 pair 列に分解、
   cover 3 条件 `hS₀`/`hpairs`/`hcoverIdx` を証明) = **最も combinatorial な新規部分** (X conj-closed ゆえ非実 χ は
   χ̄ と pair; 同次数ゆえ degree-monotone enum 内で隣接化可能だが injective enum は χ,χ̄ の隣接を保証しない →
   pairing は別途構成要)。
3. base S₀ coherence ← `coherentEqualDegree_fromDade` (S₀=min-degree 等次数, n≥2)。
4. per-step `hstepData i`: `DadeChainStep` instance = T8.1(facts)✓ + T8.2(diffsupp)✓ + T8.3(degree, a/famRatio) +
   T8.4(Dmem via `decompositionDaFromDadeOfDiff`) + T8.5(hdeg_c via gap leaf) + famS/famPairwise/famSupp 等
   (T8.1/8.2 系の quantify)。
5. → `peterfalvi_66_coherence_of_X_from_dade` → `IsCoherent τ X A`。

**残リスク (design-heavy, 直接実装)**: (a) **pairing 構成** (step 2, 共役 pair への分割 = 新規 combinatorics,
~100-200 LOC)。(b) **Dmem family** (step 4, 各 prior member の差分-support ψ=0 分解を `decompositionDaFromDadeOfDiff`
から組む, engine-internal 理解要)。(c) **hdeg_c** (step 4, degree-sum→gap leaf wiring; Frobenius は landed 見込みだが
未実装確認)。(d) X.Nonempty は (6.5)還元 context 由来 (standalone leaf では仮説化)。

**leaf 順**: T8.1✅/T8.2✅/T8.3a3b✅ (clean, done) → **pairing 構成 (次)** → base wiring → per-step (Dmem/hdeg_c) → assemble。
clean leaf は /goal、design-heavy (pairing/Dmem/hdeg_c) は attended 直接。**T8 は feasible・大 (Frobenius case で ~400-600 LOC 見積)**。

### J.2 backbone 進捗 (2026-06-03, T8 leaf 4-10 完了 — **base coherence + 共役 pair cover 達成**)
- ✅ **T8.4** `xSet_finite` (31eea58): X⊆Irr L 有限 = `hXfin`。
- ✅ **T8.5** `xBaseBlock` + subset/degree_re_eq/closedUnderConjugate (79821fb): base S₀=最小次数ブロック。
- ✅ **T8.6** `sMember_support_subset_H` + `sMember_diffSupport_of_charValue_eq` (eefc87e): 等次数差 χ−χ' ⊆ H^# = base `hsuppdiff`。
- ✅ **T8.7** `exists_finEnum_irreducible` (41052b8): 有限既約集合→`Fin k` 単射 enum (range=T) = `coherentEqualDegree_fromDade` の Fin n interface bridge。
- ✅ **T8.8** `two_le_xBaseBlock_ncard` (8f6271e): `X.Nonempty` → S₀ に χ と共役 χ̄≠χ → `2 ≤ |S₀|` = base の `2 ≤ n`。
- ✅ **T8.9** `xBaseBlock_isCoherent` (本コミット, axiom-clean #print 確認済 propext/Classical.choice/Quot.sound): **base block S₀ coherence 完成**。`coherentEqualDegree_fromDade hyp.dade hyp.hconj` を `A = sharpImage H` で適用 → 結論の Dade map = `hyp.tau` (abbrev 同一)・set = `range χ` を `hrange` で `xBaseBlock Z` に rw。入力: enum=T8.7 (`choose` で Type-goal にデータ抽出, `obtain` 不可)・n≥2=T8.8・`hsuppdiff`=T8.6 (H^# = sharpImage H が engine の A と一致)・`hdeg`=`xBaseBlock_degree_re_eq` (re 等) + `irreducibleCharacter_apply_one_eq_pos_natCast` (degree=正整数 ⟹ re 等で value 等)・`h1notA`=`simp [sharpImage]`。**`noncomputable def` (IsCoherent は Type-値=ν 担持)**。`hZH`/`[Z.Normal]`/`hXne` 引数。
- ✅ **T8.9' (2026-06-04, codex)**: base-block 補題群を `hX : ∀ φ∈X, IsIrreducibleCharacter φ` に一般化。新規 `xMember_characterFacts_of_irreducible_X` / `xMember_diffSupport_of_irreducible_X` / `Xset_closedUnderConjugate_of_irreducible_X` / `Xset_hasNoRealCharacters_of_irreducible_X` / `xSet_finite_of_irreducible_X` / `xBaseBlock_closedUnderConjugate_of_irreducible_X` / `two_le_xBaseBlock_ncard_of_irreducible_X` / `xBaseBlock_isCoherent_of_irreducible_X` を landed、既存 Frobenius API は特殊化として維持。さらに `xBaseBlock_isCoherent_caseA` で `isIrreducibleCharacter_of_mem_Xset_caseA` から case-A base coherence を直接供給可能にした。leaf/full build green + #print axioms は allowlist のみ。
- ✅ **T8.10** `exists_conjugatePairCover` (本コミット, **抽象**=`{Γ}[Group Γ]`, axiom-clean #print 確認済): **共役 pair cover の組合せ核完成**。有限 conj-closed no-real irreducible 集合 `X` + conj-closed base `S₀` から `peterfalvi_66_coherence_of_X_from_dade` の入力一式を ∃-bundle: enum `e`(`exists_monotoneDegreeEnum`)・`pair`/`N`/`hpairχ`・`hsurj`/`hpairs`/`hcoverIdx`/`hpair0`/`hpair1` + **次 leaf 用の 2 事実**=各 pair の `Disjoint (pairSet pair j) (pairUnion S₀ pair j)`(⟹ `χⱼ,χ̄ⱼ⊥S₁`)+ degree-monotone。**構成**: 共役 index involution `cidx`(`e(cidx i)=(e i).conj`, no-real で FPF, `∉S₀` 保存)→ 索引 transversal `T={i|e i∉S₀∧i<cidx i}`(`Finset.orderEmbOfFin` でソート)→ `pair j=(e tⱼ, (e tⱼ).conj)`。cover は `i<cidx i`(i∈T)/`cidx i<i`(cidx i∈T)の 2 分岐、disjoint は 4 index-等式を strict-mono `t`+involution で矛盾。**Prop ∃ bundle ゆえ次 leaf は `choose` で消費**(個別 support 不要)。
- ✅ **T8.10′ (2026-06-04, codex)** `Xset_isCoherent_from_adjoinSteps_of_irreducible_X`: T8.10 cover を `Xset Z`/`S₀=xBaseBlock Z` に特殊化し、`xBaseBlock_isCoherent_of_irreducible_X` を base にして `xChainCoherent` へ接続する wrapper を landed。`obtain` では `IsCoherent`(Type 値)へ ∃ 消去できないため `choose` で witness を抽出。残は `hstep` として露出した per-step `XAdjoinStepInput` builder のみで、cover 由来の `hpairs`/disjoint-prefix/degree-monotone を直接受け取れる。
- ✅ **T8.11a (2026-06-04, codex)** `pairCover_orthogonal_to_prefix`: T8.10 の `Disjoint (pairSet pair i) (pairUnion S₀ pair i)` と `X⊆Irr` から `χ_i, χ_i.conj ⊥ pairUnion S₀ pair i` を導く set→inner-product bridge を landed。これで `XAdjoinStepInput.hχ_S1`/`hχbar_S1` は cover 由来データだけで放電可能。
- ✅ **T8.11b (2026-06-04, codex)** `xPair_stepCoreFacts_of_irreducible_X`: T8.10/T8.11a の pair-cover データから `XAdjoinStepInput` 前半 8 field (`hrealχ`/`hdiffsuppχ`/`hχχ`/`hχbarχbar`/`hχχbar`/`hχbarχ`/`hχ_S1`/`hχbar_S1`) を一括放電する bridge を landed。新 pair 自身の基本 character facts は `xMember_characterFacts_of_irreducible_X`/`xMember_diffSupport_of_irreducible_X`、prefix 直交性は `pairCover_orthogonal_to_prefix`。
- ✅ **T8.11c (2026-06-04, codex)** `exists_pairUnion_memberFamily_of_irreducible_X`: running accumulator `pairUnion (xBaseBlock Z) pair i` を `Fin k` 上の単射 irreducible family として列挙し、range 等式、`hmemreal`/`hmemdiffsupp`、`hmemS1`/`hmembarS1`、共役直交 `hmemconjortho`、pairwise orthonormal `hmemortho` を一括放電する bridge を landed。base block の共役閉性 + pair cover の `(χ, χ̄)` 形から accumulator の共役閉性を作り、finite enum は T8.7 を再利用。
- ✅ **T8.11d (2026-06-04, codex)** `sMember_scaledDiffSupport_of_charValue_eq`: `S`-member の degree-ratio 等式 `χ(1)=aχ₁(1)` から `χ-aχ₁` の support ⊆ `H^#` を直接作る scaled support bridge を landed。degree ratios が入れば `hmemdegdiffsupp`/`hdiffasuppχ` はこの補題で放電できる。
- ✅ **T8.11e (2026-06-04, codex)** `scaledDiff_dadeImage_mem_ZIrr`: supported scaled diff `χ-aχ₁` から `τ(χ-aχ₁)∈ZIrr G` を作る `htau1_memaχ` bridge を landed。proof は `dadeIntegralCharacterMap_mem_ZIrr_of_supported` + `χ.mem_ZIrr` + `nsmul_mem χ₁.mem_ZIrr a`。
- ✅ **T8.11f/g (2026-06-04, codex)** `xMember_scaledDiffSupport_of_degreeData` / `xMember_scaledDiffSupports_of_degreeData`: `X`-membership + degree-ratio equation から新 pair の `hdiffasuppχ` と accumulator family の `hmemdegdiffsupp` を放電する bridge を landed。degree ratios の構築自体は未解決だが、support field への接続は完了。
- ✅ **T8.11h (2026-06-04, codex)** `S03.exists_pos_natDegreeRatioFamily_of_dvd`: divisibility data から `deg i₁=1` を固定した positive degree-ratio family と ratio equations を作る汎用 bridge を landed。T8.11 builder 側では (6.6)(b) の divisibility 証明を入れれば `deg`/`ha1`/ratio equations を取り出せる。
- ✅ **T8.11i (2026-06-04, codex)** `S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs`: accumulator family が `S₁` を cover し、各 `χᵢ-degᵢχ₁` の support が `A` に入るなら `ℤ[S₁] ≤ span(ℤ[S₁,A] ∪ {χ₁})` を返す pure module bridge を landed。T8.11 builder の `hSgen` field は member-family + T8.11f/g の support data から放電できる形になった。
- ✅ **T8.11j (2026-06-04, codex)** `S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration`: `hSgen` と value-at-one degree data (`χ(1)=aχ₁(1)`, `χ̄(1)=χ(1)`, `χ₁(1)≠0`, `1∉A`) から `zSupportedSpan (S₁∪{χ,χ̄}) A ≤ span(ℤ[S₁,A] ∪ {χ-χ̄,χ-aχ₁})` を返す pure module bridge を landed。T8.11 builder の `hgen` field は degree-ratio data から放電できる形になった。
- ✅ **T8.11k (2026-06-04, codex)** `S08.XAdjoinStepInput.adjoin`: `XAdjoinStepInput` から `hgen` field を削除し、`adjoin` 内で `hSgen` + `hdiffasuppχ` + irreducible degree-at-one facts + `1∉A` から T8.11j を使って導出するようにした。per-step input は `hSgen` までで足りる。
- **次 = per-step `XAdjoinStepInput` builder** (T8.11, 最重・残): `∀ i<N, IsCoherent τ (pairUnion S₀ pair i) A → XAdjoinStepInput ... (χs i)` を構成。残 field: (6.6)(b)/(c) からの divisibility・degree-gap 証明 (`a`/`hDeg` と family `hdvd`)。`Dmem`/`crux1`/`hgen` はこれらの field から `xAdjoinStep`/`adjoin` 内部で組み立つ。新 pair の `hreal`/`hdiffsupp`/row-ortho/prefix-ortho は T8.11b、accumulator member-family data は T8.11c、scaled support conversion は T8.11d/T8.11f/g、supported-diff ZIrr wiring は T8.11e、family ratio extraction は T8.11h、`hSgen` generation は T8.11i で解決済み。
- その後 (assembly, 軽い): T8.11(hstepData)→ `Xset_isCoherent_from_adjoinSteps_of_irreducible_X` → `IsCoherent τ X A` → glue X∪Y → capstone。
- **全 leaf axiom-clean (propext/Classical.choice/Quot.sound), full build 3576 green**。

### J.3 🔴 T8.11 BLOCKER 検証 (2026-06-03 着手→独立監査): DadeChainStep は X で充足不能、engine 手術が真の残務

**結論**: T8.11(per-step `DadeChainStep` instance)は **leaf でなく engine 手術**。`DadeChainStep`/`retarget` が **member 個別 support**(`x.support ⊆ H^#`)を要求するが、X-member `χ=Ind θ` は `χ(1)=|W₁|θ(1)≠0` ⟹ `1∈support`, `1∉H^#` ⟹ 充足不能。これは master-roadmap の 🔴 で、B-surgery round-1 では **未解決**(round-1 は新規 pair の差分 `hdiffsupp`/`hdiffasupp` のみ弱化、member family は手付かず)。§J.1/§I の「engine bug 解消」は member family については **誤り**(訂正)。

**根本原因(コード照合済)**:
- `zSupportedSpan S A = {φ | φ∈zSpan S ∧ φ.support⊆A}` ⟹ `DadeChainStep.hmemSupp`/`hchi1supp`/`famSupp` は個別 support 要求。
- `retarget_isCoherent_fromDade_X`(S07:5314)は `hmemSupp`→`hmemTau1 (ν x=τ x)` と `hchi1supp`→`htau1_chi1 (ν chi1=τ chi1)` を `extends_on_supported` 経由で製造。両方 support 必須。
- **より深い**: core `retarget_isCoherent_of_decompositions`(S07:3309)が `htau1_chi1 : Da.tau1 chi1 = ν chi1` を直接消費。`Da=decompositionDaFromDadeOfDiff` は `ofProjection ... τ ...`(S07:4739)で **`Da.tau1=τ`** ⟹ `htau1_chi1 = (τ chi1 = ν chi1)`、unsupported chi1 で **偽**。adapter だけでなく **core retarget** に届く。
- 対照: `coherentEqualDegree`(S07:3078, T8.9 を X で構成)は `hsuppdiff` のみ・member support **不要** ⟹ 差分ベース all-at-once は X で動く実証。

**原理的 fix(option A, deep)**: retarget が `ν(χ)` を「`τ chi1=ν chi1` 仮定」でなく **`ν(χ) := τ(χ−a·chi1) + a·ν(chi1)`**(両項 integral: supported 差分の Dade 像 + `ν chi1∈ZIrr`)で **定義** し直す ⟹ `τ chi1=ν chi1` 不要。`hperElem (∀ξ∈ℤ[S₁], ν ξ⊥R(χ))` は ℤ[S₁]=⟨chi1⟩∪{x−aₓchi1 (supported)} 生成で:
  - (B) `⟨ν chi1,α⟩=0`: `a·ν chi1 = Da.Y`(↑の定義)+ `Da.Y_orthogonal`(struct field: Y⊥R(χ))+ `a≠0`。**solid**。
  - (A′) `⟨ν(x−aₓchi1),α⟩=⟨τ(x−aₓchi1),α⟩=0`: degree-matched 差分 supported の Dade 像 ⊥ R(χ)(caller 供給、`hmemOrtho` と同形だが supported ⟹ 構成可)。
  touch = `retarget_isCoherent_of_decompositions`(3309) core + 下流。multi-session 規模。
**option B(comparable depth)**: `coherentEqualDegree`(差分ベース・running ν 無)を **不等次数に一般化**(generators χⱼ−aⱼχ₁)。τ-vs-ν 整合問題が **構造的に発生しない**(incremental でなく一括)。(6.6) を実質再導出。
**両者とも (6.6) の真の技術核**(supported-family 用 engine を induced X に拡張)。leaf でなく、どちらも multi-session の新規形式化。

#### J.3.1 option A 完全 reduction (2026-06-03, user 承認後の深掘り — 実装 SPEC)

surgery を 2 系統に分解(`IsCoherent` field 確認済: `extension`=ν, `extension_inner_eq`=ν は ℤ[S₁] 上 isometry, `extends_on_supported`=ν=τ on supported; `CharacterPsiDecomposition.Y_orthogonal`=Y⊥R は struct field S07:1008):

- **member 側(clean fix・教科書通り、support 不要)**: 各 member の per-member 直交 `⟨ν x,α⟩=0`(α∈R(χ))は **member 分解の aux isometry を τ でなく ν にする**だけで解ける。`Dmem x : CharacterPsiDecomposition τ x 0` を **`tau1=ν` で構成**(base は τ だが aux = ν = `hS₁.extension`)。根拠: ν x∈ZIrr(coherence)かつ ‖ν x‖²=⟨x,x⟩=1 ⟹ ν x=±irr ⟹ ν x∈ℤ[R(x)](R(x)=`(x−x̄)^τ=ν(x−x̄)` の構成元={ν x,ν x̄})⟹ ψ=0 分解 Y=0, X=ν x 構成可。`tau1_agrees`(ν(x−x̄)=τ(x−x̄))は supported で ✓。すると `inner_extension_member_orthogonal_imageSet`(3243)の `htau1 : Dmem.tau1 x=ν x` が **rfl**(hmemSupp 不要)。`hmemOrtho`(R(x)⊥R(χ))は `⟨(x−x̄)^τ,(χ−χ̄)^τ⟩=⟨x−x̄,χ−χ̄⟩=0`(supported isometry, χ,χ̄⊥S₁)+ 直交正規(差分和直交⟹構成元集合 disjoint)で証明可。⟹ **adapter `retarget_isCoherent_of_supportedDecomposition_and_memberFamily`(3514)は member 側で既に support-free**(`hmemTau1` を抽象に取る)、`_fromDade_X`(5314)が `hmemSupp` 経由で製造する所だけ ν-aux 構成に差し替え。
- **chi1/Da 側(真の crux・残)**: `Da`(新 pair, χ∉ℤ[S₁] を含む)は τ ベース必須 ⟹ `Da.tau1 chi1=τ chi1`。core が要求する `htau1_chi1 : Da.tau1 chi1=ν chi1` ⟹ `τ chi1=ν chi1`(=defect δ=ν chi1−τ chi1=0)が unsupported chi1 で偽。**δ は base block 上一定**(ν(chi_j−chi_0)=τ(chi_j−chi_0) ⟹ ν chi_j−τ chi_j=ν chi_0−τ chi_0)。原理的 fix = `ν'(χ):=τ(χ−a·chi1)+a·ν chi1`(両項 integral)で χ の像を定義 ⟹ Da を `tau1 χ=ν'(χ)` で構成すれば `Da.tau1 chi1=ν chi1` 成立。**残 crux = ν'(χ) が norm-1 + ν(S₁) と直交正規であること** ⟺ **`⟨τ(χ−a·chi1), ν chi1⟩=−a`**(norm 条件: ‖ν'(χ)‖²=(1+a²)+a²+2a·Re⟨τ(χ−a·chi1),ν chi1⟩=1)。supported chi1 なら Dade isometry で −a だが、unsupported chi1 では ν chi1 と Dade 像の内積を base coherence(coherentEqualDegree)の構成詳細から導く要 = (5.6) の真の content・multi-session。
- **実装順(parallel 構成で build-green 維持)**: (1) member ν-aux 分解補題(上記, clean・先行可能)→ (2) crux `⟨τ(χ−a·chi1),ν chi1⟩=−a` を base coherence 構成から導出(hard)→ (3) 補正 Da 構成子(`tau1 χ=ν'(χ)`)→ (4) `retarget_isCoherent_fromDade_X` 差分化(hmemSupp/hchi1supp 除去)→ (5) `DadeChainStep` struct 差分化 + `advance` rewrite。**(2) が律速**。

#### J.3.2 crux 攻略 — surgery を単一恒等式へ還元 (2026-06-03, user「crux 攻略」指示後)

**🟢 base `retarget_isCoherent`(S07:2844)は再利用可・core 再導出不要**: image `X`/`Xbar` を **明示引数**で取り、`hXX`/`hXbarXbar`/`hXXbar`/`hXbarX`(image 直交正規)・`hX_ortho`/`hXbar_ortho`(`⟨ν ξ,X⟩=0`)・`himg : τ(χ−a·chi1)=X−a·ν chi1` を **仮説**として取る(decomposition から X を計算しない)。⟹ **`X := ν'(χ) := τ(χ−a·chi1)+a·ν chi1` を直接渡せる** ⟹ `himg` は **rfl**(`htau1_chi1` を完全 bypass)。`hagree_ratio`(τ₂(χ−a·chi1)=τ(χ−a·chi1))も himg 経由で成立。

**🎯 surgery 全体が単一恒等式 crux1 へ還元**(代数済): X=ν'(χ) で
- `himg`: 定義より trivial。
- `hX_ortho ⟨ν ξ,X⟩`: ξ=ξ_supp+m·chi1 分解 + ν-isometry(ℤ[S₁])+ Dade-isometry(supported)で `= m·(a + conj⟨τ(χ−a·chi1),ν chi1⟩)` ⟹ **crux1 ⟺ 0**。
- `hXX ‖X‖²`: `= ‖τ(χ−a·chi1)‖² + 2a·Re⟨τ(χ−a·chi1),ν chi1⟩ + a²‖ν chi1‖² = (1+a²)+a²+2a·Re(crux1)` ⟹ **=1 ⟺ Re(crux1)=−a**。
- `crux2 := ⟨τ(χ−χ̄),ν chi1⟩ = 0`: **clean**(`τ(χ−χ̄)∈ℤ[R(χ)]`, `ν chi1∈ℤ[R(chi1)]`(ν-aux 分解), `R(χ)⊥R(chi1)` ← `⟨(χ−χ̄)^τ,(chi1−c̄)^τ⟩=⟨χ−χ̄,chi1−c̄⟩=0`)⟹ `hXXbar`/`hXbar*` 系も crux1 のみに依存。

⟹ **残 = crux1 `⟨τ(χ−a·chi1), ν chi1⟩ = −a` ただ 1 本**。`τ(χ−a·chi1)=Da.X−Da.Y`, `Da.X∈ℤ[R(χ)]⊥ν chi1`(R 直交)⟹ `crux1 = −⟨Da.Y,ν chi1⟩`、両者 ⊥R(χ) の overlap = (5.6) Feit–Sibley の真の content。supported case は `inner_self_chi_eq_sum_coeff`(S07:1220)+`inner_self_chi_add_psi_eq`(1300)+ degree 不等式で `‖Da.X‖²=1`(⟹`‖Da.Y‖²=a²`⟹`‖τ chi1‖²=1`)を導出。crux1 は同 machinery + degree 不等式の適応で出る見込み。

**⚠️ bridge lemma は Dade レベル**: `‖τ(χ−a·chi1)‖²=1+a²` は χ∉ℤ[S₁] ゆえ IsCoherent の `inner_eq_on_supported`(ℤ[S₁] 限定)では出ず、**Dade isometry `dadeIntegralCharacterMap_inner_eq_on_supported_span`** が要る ⟹ bridge は `retarget_isCoherent_fromDade_*` レベルで書く。

**✅ bridge 完成** = `retarget_isCoherent_of_extensionImage`(S08, **axiom-clean** propext/Classical.choice/Quot.sound, full build 3562 green): `τ`+`hτ:τ=dade` でパラメタ化し、crux1`⟨τ(χ−a·chi1),νchi1⟩=−a`+crux2`⟨τ(χ−χ̄),νchi1⟩=0`+`hSgen:ℤ[S₁]≤span(ℤ[S₁,A]∪{chi1})` を仮説に取り、`X:=τ(χ−a·chi1)+a·νchi1` で `hXX`/`hXbarXbar`/`hXXbar`/`hXbarX`/`hX_ortho`/`hXbar_ortho`/`himg`(rfl) を全導出 → base `retarget_isCoherent` 呼ぶ。`hX_ortho` は生成系 induction(supported は Dade+ν isometry, chi1 は crux1)。**これで surgery が crux1+crux2+hSgen に帰着**(crux2/hSgen は clean に discharge 可)。**残 = crux1 を decomposition norm machinery(`inner_self_chi_eq_sum_coeff`/`inner_self_chi_add_psi_eq`)+ degree 不等式で discharge(本丸・(5.6) Feit–Sibley)→ DadeChainStep 代替の per-step glue → capstone**。**重要教訓(set の罠)**: `set τ`/`set ν` は τ/ν が `hS₁` の型に現れる/`hS₁.extension` を含むため `hS₁`→`hS₁✝` dagger を起こし、param `hcrux*` と goal の fold 不一致を招く ⟹ engine 補題は **τ を明示 param + `hτ:τ=dade`** で取るのが安全(`set` 回避)。

#### J.3.3 crux1 深掘り精査 — crux1 = (5.6.1)/(5.6.2) collapse for induced χ (2026-06-03, 「続けてください」)

mmd (5.6)(04.7 L59-105) + (6.8.1)(04.8 L166-177) + 既存 S07 machinery を精査し crux1 を厳密 scope:

**crux1 = 真の (5.6.2) collapse `Da.Y = a·νχ₁`(ν=coherent extension)**:
`τ(χ−a·chi1) = Da.X − Da.Y`(`Da.tau1_image`+`htau1_diff`)。`Da.X∈ℤ[R(χ)]`, `νchi1∈ℤ[R(chi1)]`, `R(χ)⊥R(chi1)`((5.2.e))⟹`⟨Da.X,νchi1⟩=0`。よって `Da.Y=a·νchi1` ⟹ `⟨τ(χ−a·chi1),νchi1⟩=⟨Da.X−a·νchi1,νchi1⟩=0−a·1=−a` = **crux1**。
↔ (6.8.1) 流に言えば `⟨(χ−a·η₁)^τ,η₁^{τ₁}⟩=b−a`(L176)で **crux1 ⟺ b=0**(case A の b=0 論証=(6.7)+norm bound+a>1; X-chain 経由(6.6)では generic (5.6.2) λ-form)。

**🔴 構造的発見 1(重大)**: `IsCoherent.extension : IntegralCharacterMap = CF L →ₗ[ℤ] CF G`(S07:165 abbrev)で **ZIrr-codomain field 無し**(struct field は `nonzero`/`extension`/`extension_inner_eq`/`extends_on_supported` のみ, S07:1421)⟹ **`ν x ∈ ZIrr` は IsCoherent から導出不能**。member ν-aux 分解(`CharacterPsiDecomposition τ x 0` を `ofProjection` で構成)は `htau1_mem : ν x∈ZIrr` 要求 ⟹ **member R-分解は仮説として注入要**(既存 engine の `Dmem` field と同形;`IsCoherent` を強化するか、caller=実 coherence engine が供給)。

**🔴 構造的発見 2**: 既存 `Y_eq_nsmul_tau1_of_lambdaForm`(S07:1940)は `hvc1 : vc i₁ = D.tau1 chi1` で **member family を `D.tau1` に hardwire**。`Da=decompositionDaFromDadeOfDiff` は `Da.tau1=τ`(Dade)⟹ 結論 `Da.Y=a·D.tau1 chi1=a·τchi1`(≠`a·νchi1`!)。unsupported chi1 で τchi1≠νchi1 ⟹ **直接再利用不可**。代わりに `lambda_eq_zero_and_Z_eq_zero`(S07:1852, **family `vc` 自由**)を `vc i=νχᵢ` で直叩き要。

**crux1 discharge 経路(確定, multi-session)**:
1. `Da := decompositionDaFromDadeOfDiff hyp hconj χ …`(S07:4708, B-surgery, supported 差分のみ ⟹ **χ unsupported でも構成可**)→ `Da.X∈ℤ[R(χ)]`, `Da.Y`, `Da.tau1_image`, (5.4.a) opening bound。
2. member ν-aux family(**仮説注入**, 発見1): 各 χᵢ∈S₁ に `νχᵢ∈ℤ[R(χᵢ)]`((5.5))+ orthonormal(ν isometry on ℤ[S₁])。
3. member R-orthogonality `R(χᵢ)⊥R(χ)`((5.2.e), `⟨(χᵢ−χ̄ᵢ)^τ,(χ−χ̄)^τ⟩=0`)→ 既存 `inner_extension_orthogonal_imageSet_of_members`(S07:3267, **support-free**)で ℤ[S₁] へ lift。
4. (5.6.1) λ-form `Da.Y=a·νχ₁−λ∑rᵢ·νχᵢ+Z`(**本丸 hard**): 係数を `⟨τ(χ−a·chi1),ν(χⱼ−aⱼchi1)⟩=⟨χ−a·chi1,χⱼ−aⱼchi1⟩`(↓foundational lemma)から計算。
5. `lambda_eq_zero_and_Z_eq_zero`(degree 不等式(c) `2a<∑aᵢ²/‖χᵢ‖²` = (6.6) prime-power gap, S07:1696 landed)→ λ=0,Z=0 → `Da.Y=a·νχ₁`。
6. crux1 = `⟨Da.X−a·νχ₁,νchi1⟩=−a`(発見の R-直交 + ‖νchi1‖²=1)。

**✅ foundational lemma landed**(本コミット, S08 `inner_dade_extension_of_supported`, axiom-clean #print 確認): supported `u` + supported `δ∈ℤ[S₁]` で `⟨τ u,ν δ⟩=⟨u,δ⟩`(ν=τ on supported + Dade isometry)= (5.6.1) L79 cross-term の retargeting move(step 4 の基盤)。**注意: δ=chi1 には適用不可**(chi1=Ind θ unsupported)= crux1 が直接系でない理由を体現。

**⚠️ scope 評価**: crux1 = (5.6.1)/(5.6.2) engine を induced(unsupported)member 用に再導出 = (6.6)/(5.6) の真の技術核, **multi-session**。member R-family 注入で `IsCoherent` 拡張 or 新 carrier 要。かつ master-roadmap 上 (6.8) は **orphaned**(FeitThompson 未配線; 実 critical path = BG §7-16 Track B)⟹ crux1 grind 継続は戦略判断要。

#### J.3.4 crux1 進捗 — member 側完全 discharge, 残 = (5.6.2) collapse のみ (2026-06-04, user「最終的に必要 → 続行」)

ユーザー確認: (6.8) は orphaned だが Peterfalvi 指標理論の本物の片翼で **最終的に必須** → crux1 続行。
**FeitThompson 配線の現状（grep 確認済）**: 最上位 `feitThompson`(`OddOrder/FeitThompson.lean:24`)= 裸 sorry(還元無)、`noMinimalSimpleOdd_of_section16` は `S16.Hypothesis`(未構成 carrier)を仮説に取るのみ、`sibleySetup_is_coherent` は消費者 0、S16 は coherence を import せず。⟹ crux1 完遂しても §10-16 配線が別途必要(全体が未完足場)。

**✅ crux1 の step 1/3/6 + 端部代数を完全 landed**(S08, 全 axiom-clean, build 3320):
- `crux1_of_collapse`(端部): `himg : w=X−Y` + collapse `Y=a·νχ₁` + `⟨X,νχ₁⟩=0` + `‖νχ₁‖²=1` ⟹ crux1 `⟨w,νχ₁⟩=−a`(純内積代数, abstract over G)。
- `memberExtensionDecomposition`(step 2, (5.5) member ν-aux): member χ∈S₁ に `D':CharacterPsiDecomposition τ χ 0` を **tau1=ν** で構成(`ofProjection`; `ν χ∈ZIrr` を注入)⟹ `D'.tau1 χ=ν χ`(**rfl, 実 context で検証済**), `ν χ=D'.X∈ℤ[R(χ)]`。
- `inner_dadeDiff_conjDifference_eq_zero` + `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`(step 3, (5.2.e)): 差分 support 版 `R(χ₁)⊥R(χ)`(既存 individual-support 版は induced で不可ゆえ新規)。
- `inner_decomposition_X_extension_member_eq_zero` + `inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero`(step 3 assembled): **`⟨Da.X,νχ₁⟩=0` を注入データから完全導出**(member ν-aux + family ⊥ + per-α 和)。
- `inner_dade_extension_of_supported`(step 4 基盤, 既 landed): `⟨τ u,ν δ⟩=⟨u,δ⟩`(supported)。

⟹ **crux1 残 = (5.6.2) collapse `Da.Y=a·νχ₁` ただ 1 本**(step 4-5)。これを得れば `crux1_of_collapse`(`himg`=`Da.tau1_image`(Da.tau1=τ)+`htau1_diff`, `‖νχ₁‖²=1`=ν-isometry, `⟨Da.X,νχ₁⟩=0`=上記)で crux1 → bridge → coherence。

**残 step 4-5 (本丸・(5.6.1)/(5.6.2) λ-form)**: member family `vc i=νχᵢ`(i over S₁ の有限 enum)を用意し、λ-form `Da.Y=a·νχ₁−λ∑rᵢνχᵢ+Z` を `⟨τ(χ−a·chi1),ν(χⱼ−aⱼchi1)⟩=⟨χ−a·chi1,χⱼ−aⱼchi1⟩`(`inner_dade_extension_of_supported` を δ=χⱼ−aⱼchi1 supported で適用)から係数計算 → 既存 `lambda_eq_zero_and_Z_eq_zero`(S07:1852, vc 自由)+ degree 不等式(c)で λ=0,Z=0 → collapse。**注意**: 既存 `Y_eq_nsmul_tau1_of_lambdaForm`(S07:1940)は vc i₁=D.tau1 chi1=τchi1 に hardwire ⟹ 不使用、`lambda_eq_zero_and_Z_eq_zero` 直叩き。member enum + λ-form 組立が残 work(multi-session)。

#### J.3.5 ✅✅ crux1 完全 discharge — λ-form collapse capstone landed (2026-06-04)

**crux1 → coherence の全 lemma chain が build-green・axiom-clean で landed**(step 4-5 含む全 step 完了):
1. `inner_dade_extension_of_supported`(foundational cross-term, e1253de)
2. `crux1_of_collapse`(端部代数, 60cdf56)
3. `memberExtensionDecomposition`((5.5) member ν-aux, 4f6a19f)
4. `inner_dadeDiff_conjDifference_eq_zero` + `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`(差分 support family ⊥, 992c0c3)
5. `inner_decomposition_X_extension_member_eq_zero` + `inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero`(member R-直交 assembled, b2c6a45)
6. `inner_Y_extension_member_eq`((5.6.1) member coefficient `⟨Da.Y,νχⱼ⟩=a·⟨χ₁,χⱼ⟩−(a+μ)·aⱼ`, 88aaef1)
7. `exists_indexed_intProjection_of_orthonormal_ZIrr`(indexed 直交射影, 1b368c4)
8. **`crux1_of_memberFamily`(CAPSTONE: λ-form collapse ⟹ crux1, 8461d5c)** — indexed projection + 係数同定 `cᵢ=a·[i=i₁]−λ·aᵢ`(λ=a+μ, μ=⟨τ(χ−a·χ₁),νχ₁⟩∈ℤ via `inner_mem_ZIrr_int`)+ `lambda_eq_zero_and_Z_eq_zero`(degree 不等式 2a<∑aᵢ²)⟹ λ=0 ⟹ **μ=−a = crux1**。
9. `retarget_isCoherent_of_extensionImage`(bridge: crux1 ⟹ coherence, e982181)

⟹ **crux1 は X-family enumeration data の関数として完全証明済**。`crux1_of_memberFamily` の仮説 = case-A 用 (X⊆Irr L, ‖χᵢ‖²=1): finite orthonormal member family {χmem i}⊆S₁ + `hcoeffval`(= `inner_Y_extension_member_eq` を per-member 適用)+ a₁=1 + degree 不等式 + `Da`(=`decompositionDaFromDadeOfDiff`)+ Da.Y∈ZIrr + νχᵢ∈ZIrr 注入。

**残 = 最終 assembly のみ(math 完了, glue 残)**: T8 backbone の X-family enum(`Xset Z`/`xBaseBlock`/`exists_conjugatePairCover` の conjugate-pair chain)を上記 lemma に wire:
- per-step: `inner_Y_extension_member_eq`(member R-直交 + foundational cross-term から hcoeffval)→ `crux1_of_memberFamily`(crux1)→ `retarget_isCoherent_of_extensionImage`(coherence adjoin)。
- chain: `xBaseBlock_isCoherent`(base)から conjugate-pair cover を induction で adjoin → `IsCoherent τ (Xset) A`。= **DadeChainStep 代替の per-step glue**(notes §J.3.1 step 5)。
- 必要な X-family 固有 fact: 各 adjoined χ の `decompositionDaFromDadeOfDiff` 構成、degree 不等式(= (6.6) prime-power gap `two_mul_lt_sq_of_primePow_gap` S07:1696)、Da.Y∈ZIrr、νχᵢ∈ZIrr(coherence engine が供給)。
- その後: glue X∪Y → capstone `sibleySetup_is_coherent`(S08 唯一の sorry)。

**全 math lemma 完了ゆえ残は mechanical-ish wiring(但し T8 enum との接続は非自明・substantial)。**

#### J.3.6 🔶 最終 assembly の blocker = ZIrr-codomain gap (2026-06-04, 着手→診断)

最終 assembly(chain fold で X-coherence 構築)を着手して判明: **`crux1_of_memberFamily` の `hνZ : νχⱼ∈ZIrr` が IsCoherent から取れない**(§J.3.3 構造的発見1 が最終段で blocker 化)。`νχⱼ∈ZIrr` の用途 = (a) indexed projection の integer 係数、(b) μ∈ℤ(`inner_mem_ZIrr_int`)— 両方必須。

**chain fold は再利用可**: `peterfalvi_66_coherence_of_X`(S07, abstract)は per-step `hstep : ∀i<N, IsCoherent (pairUnion S₀ pair i) → IsCoherent (pairUnion S₀ pair (i+1))` を取る ⟹ bridge ベース per-step を供給すれば良い(`DadeChainStep` 不使用)。但し per-step が `crux1_of_memberFamily` を呼ぶ ⟹ running accumulator の member family(orthonormal + ZIrr + degree)が要る。

**ZIrr-codomain は誘導的に維持可(コード診断済)**: `retarget τ₁ χ χ̄ X Xbar = τ₁∘orthoResidualMap + ⟨χ,·⟩•X + ⟨χ̄,·⟩•Xbar`(S07:2348)⟹ `retarget…φ ∈ ZIrr`(φ∈ZIrr L)は **X,Xbar∈ZIrr + 旧 τ₁ が ZIrr→ZIrr + orthoResidual が ZIrr 保存(χ,χ̄∈ZIrr L で integer projection)**で出る。bridge の X=τ(χ−a·chi1)+a·νchi1 は ZIrr(supported Dade 像 + νchi1∈ZIrr)、Xbar=X−τ(χ−χ̄) も ZIrr。⟹ **誘導不変量として thread 可能**。

**2 つの実装路(設計 fork)**:
- **(A) `IsCoherent` 強化**(正攻法・invasive): field `extension_mem_ZIrr : ∀φ∈ZIrr L, extension φ∈ZIrr G` 追加。影響 = S07 の IsCoherent 構成 ~5 site(`retarget_isCoherent`(2916, 要 X,Xbar∈ZIrr 新仮説 + χ,χ̄∈ZIrr L)/`coherentEqualDegree`(3095)/`coherentEqualDegree_fromDade`(5109)/`galoisTransport`(1471)/他)が新 field を証明。consumer(S08-S16)は不変(struct 強化のみ)。bridge/DadeChainStep に X,Xbar∈ZIrr 伝播。**正しい定義(coherence=ℤ[Irr G] への isometry)だが multi-site refactor、retarget ZIrr 証明は非自明**。
- **(B) ZIrr companion thread**(localized・S08): `(IsCoherent τ Sᵢ A) × (∀x∈Sᵢ, ν x∈ZIrr)` を per-step で thread、custom chain fold(`peterfalvi_66_coherence_of_X` の induction を companion 付きで再導出)。S07 不変だが chain logic 重複。companion 維持: x∈S₁⟹τ₂ x=τ₁ x∈ZIrr(直交)、χ↦X∈ZIrr、χ̄↦Xbar∈ZIrr。

**現状(2026-06-04 時点)**: crux1 hard core(9 lemma chain)完全完了・axiom-clean。最終 assembly は (A)/(B) いずれかの ZIrr-codomain 解決が gate。

#### J.3.7 ✅✅ ZIrr-codomain gap **解消済**(2026-06-05 確認 + cleanup) — 上記 J.3.6 fork は STALE

**重要訂正**: 上の「(A)/(B) fork が gate」は **STALE**。**path (A) は既に実装済**:
- **`IsCoherent` に `extension_mem_ZIrr` field が追加済**(commit a054bc8 "route A: IsCoherent gains ZIrr-codomain field on ℤ[S]", S07:1577): `∀φ∈zSpan S, extension φ∈ZIrr G`。**zSpan S 相対**(全 ZIrr L ではない — base Dade map は global ℤ[Irr] endo でないため、zSpan-S-relative が正しい定義)。全 IsCoherent 構成 site で証明済(`galoisTransport`@1619 / retarget@3284 span-induction 等)、build green。
- **`xAdjoinStep`(S08:1427, per-step X-adjoin bridge)は既に route A で `hmemνZ` を field から導出**(S08:1487-1488, コメント "route A")。
- **2026-06-05 cleanup(commit 0482531)**: `crux1_of_memberFamily` の injected `hνZ` を除去し `hmemS1`+field で内部導出。stale docstring("ν χ∈ZIrr not derivable from IsCoherent")訂正。
- **`retarget_mem_ZIrr`(全 ZIrr L 版)は不要・revert 済**(1f478dc→reset): base map が全 ZIrr L を保存しないので過剰仮説。zSpan-S-relative field(span-induction 証明)が正しい道具。

**⟹ ZIrr gap は gate でない。残 = capstone の最終 assembly のみ**(`sibleySetup_is_coherent` の sorry, S08): X-chain fold(`xAdjoinStep` を conjugate-pair enumeration で fold → `IsCoherent τ (Xset Z) A`)+ X∪Y glue(`coherentS_of_frobenius_pairUnion...` 系は **sorry-free で landed 済**, S08:5920-5965)+ Frobenius/p-群還元 wiring。X-chain machinery は全 sorry-free。**真の残務 = capstone def 本体の組立**(substantial; T8 enum fold + glue data 供給)。次セッションは J.3.6 の (A)/(B) を再検討せず capstone assembly に直行すべし。

#### J.3.8 ✅ capstone X-empty (abelian) case closed (2026-06-05, commit 166d3b5)
`sibleySetup_is_coherent` の bare sorry を `by_cases hXe : Xset ⁅H,H⁆ = ∅` に分割:
- **X-empty branch 完全証明**: `coherenceTarget_of_Xset_empty`(新, axiom-clean): `X=∅ ⟹ S=Y`(`Xset_union_Yset_eq_S` で `S=∅∪Yset=Yset`)⟹ `CoherenceTarget = coherentYset`(Y-coherence, T6 既 landed)。glue 不要。
- **X-nonempty branch のみ sorry**(真の §8 glue): `hyp.cases`(Frobenius/CertainType)で分岐。`hXne` は `hXe` 否定から放電可。Frobenius case = `coherentS_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner`(5925, sorry-free)を invoke、要 `hF`(cases)+ **`hstepData`**(`PairUnionBaseAnchorCommonIndexPrimePowerStepData`@5685 構成 = (6.6) prime-power 次数 gap, **bottleneck = hard content**)+ glue(`ν`/`hagree`/`hmixed`/`hgen`)。**次セッション = hstepData 構成 + glue data 供給**。

#### J.3.9 ✅ (6.5) p-群還元の group-theory core landed (2026-06-05, commit f2aea41)

hstepData の前提「H が p-群 ∴ θ(1)=p-冪」を供給する **(6.5) reduction** の group-theory 半分を実装。

**(6.5) 依存ツリー(status 込み)**:
```
(6.5)(b) "H は非可換 p-群"  [reduction target]
├─ isPGroup_of_isNilpotent_of_isPGroup_abelianization ✅ [H nilp + H/H' p-群 ⟹ H p-群]
│  └─ H/[H,H] が p-群  ✅NEW = isPGroup_of_card_le_of_isFrobeniusAction (f2aea41)
│     ├─ p-primary 成分 P: Sylow characteristic ∴ R-invariant ✅(Sylow.characteristic_of_normal)
│     ├─ |R| | |P|-1: card_modEq_one(restricted via IsFrobeniusAction.subgroup)✅
│     ├─ |R| | |A:P|-1: 純算術 |A|=|A:P|·|P|, |A|≡|P|≡1 ✅ (quotient-Frobenius 不要!)
│     ├─ two_mul_add_one_le_of_odd_dvd + six_five_chief_factor_contradiction ✅
│     └─ bound |A| ≤ 4|R|²+1  🔴 = char theory (6.2)/(6.3) = Sibley packaging
├─ H 非可換: S 非coherent + S([H,H]) coherent(coherentYset)から ✅可導
└─ FPF R-作用 on Abelianization H  ⚠️ = Sibley (c1) Frobenius wiring
```

**新 lemma 2 本**(S08, axiom-clean, AxiomsCheck 登録):
- `isPGroup_of_card_le_of_isFrobeniusAction`: 抽象 chief-factor core(可換 A + FPF R-作用 + odd + `|A|≤4|R|²+1` ⟹ A は p-群)。
- `isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization`: (6.5)(b) reduction interface(`IsFrobeniusAction R (Abelianization H)` + odd + bound ⟹ `∃p, IsPGroup p H`)。

**残ギャップ**:
1. **bound(char theory)** = (6.5) の唯一の真ブロッカー。`theta_degree_le_index_mul_sqrt_index`(完成済)を S(A)/S(B) coherence + 実 index に結線 → `six_three_HH1_le` 適用。**Sibley packaging frontier・heavy**。
2. **FPF 作用 on Abelianization H**(Sibley (c1))= 純群論。`IsFrobeniusGroup ↥L H W1`(`hyp.cases`左)→ `toFrobeniusAction`(`IsFrobeniusAction ↥W1 ↥H`)→ `IsFrobeniusAction.quotient`(commutator ↥H invariant)→ FPF on `↥H ⧸ commutator`。**friction**: `Abelianization H`(semireducible def)vs `↥H ⧸ commutator H` の instance(CommGroup/MulDistribMulAction)が自動転送されない。tractable だが ~30-50 LOC bridge 要。char bound でどのみちブロックされるので **premature**。
3. odd: `card_L_odd` から H, W1, Abelianization の odd(divisor-of-odd)。容易。

**深 brick は全て既存だった**(再発見): `IsFrobeniusAction.card_modEq_one`/`.subgroup`/`.quotient`/`coprime_card`(FrobeniusActionTI), `coprime_fixedPoints_quotient`(Cor3.28, Ch04), `Sylow.characteristic_of_normal`/`ne_bot_of_dvd_card`(mathlib), p-冪次数(`exists_finrank_eq_prime_pow_of_isPGroup`)。

## H. T7 実装状況 + 特徴付け設計確定 (2026-06-03, Plan agent + atom 照合済)

**landed (S08, build-green)**: def 層 `SsubFiltration`(=(6.1)S(A))/`Xset`(=S−S(Z))/`Yset`(=S(H'))
+ `mem_SsubFiltration`/`mem_Xset` + **c1 `S⊆Irr L`** (`isIrreducibleCharacter_of_mem_S_of_frobenius`,
[Is]6.34) + **c1 `Xset⊆Irr L`** (`isIrreducibleCharacter_of_mem_Xset_of_frobenius`)。
**c1 の engine-facing 部分 (Xset⊆Irr) 完了** = T8/B が要求する X-family 既約性入力を供給。

**🟢 重大訂正: [Is] 2.21 は不要** (Plan agent が atom 照合で確定)。§F:362「要 (1.6.a) iff (2.21 converse 含む)」は
**過剰**。`Xset_eq : X={χ∈Irr L|Z⊄Ker χ}` の両方向とも 2.21 を回避:
- **(⊆)**: φ∈X (φ=Ind θ,θ≠1,φ∉S(Z)),φ既約。Z⊆Ker φ 仮定→**Res_H φ genuine** (H0)→θ は Res φ の
  constituent (Frobenius `inner_induce_eq_inner_restrict` InducedCharacter:531)→G2.2 (S03:696, Res φ の
  ℕ分解 via `exists_natFinsupp_eq_sum` Clifford:1009)→Z.subgroupOf H⊆Ker θ→φ∈S(Z) 矛盾。
  **鍵: Ind θ を genuine 扱いしない** (induce は class-function-level only, `IsCharacter (Ind θ)` 不在)。
- **(⊇)**: χ既約,Z⊄Ker χ。`exists_inner_induce_ne_zero`(S03:636)→θ。θ≠1 & Ind θ∉S(Z) は両方
  「Z⊆Ker(Ind θ')→(G2.2 constituent inherit)→Z⊆Ker χ 矛盾」。inherit に **Ind θ の ℕ分解** (H2) 要
  (Ind θ∈ZIrr `induce_mem_ZIrr` + Fourier係数≥0 via Frobenius+`inner_irreducible_nonneg` Clifford:988)。
  最後 Ind θ∈X→hX→Ind θ既約→`irreducibleCharacter_inner_eq_ite`(ZIrrFourier:40)で Ind θ=χ。

**✅✅ T7 char 完了 (2026-06-03, commit ece4803; full `lake build OddOrder` 3562 + AxiomsCheck green,
axiom-clean = `#print axioms` で propext/Classical.choice/Quot.sound のみ, 新 sorry 0)**:
- **H0** `isCharacter_restrict` (commit 3bb133a, S08:45) — `restrict_repCharacterClassFunction` 経由。
- **H1-core** `characterKernel_subset_of_natFinsupp_eq_sum` (S08) — G2.2 keystone を Finsupp ℕ分解から
  再パッケージ (dite-totalized `IrreducibleCharacter` 族 + natural degrees `exists_natDegree_charValue_one_dvd_card`)。
- **H1-genuine** `characterKernel_subset_of_isCharacter_of_inner_ne_zero` — core ∘ `exists_natFinsupp_eq_sum`。
- `inner_isCharacter_nonneg` (⟨genuine,genuine⟩≥0) — RHS 分解 → `inner_irreducible_nonneg` 各項。
- **H2** `induce_exists_natFinsupp_eq_sum` — Ind θ の ℕ分解を `ClassFunction.induce_mem_ZIrr` +
  Frobenius-nonneg (`ClassFunction.inner_induce_eq_inner_restrict` + `inner_isCharacter_nonneg`) で再現。
- **H2-wrapper** `characterKernel_subset_of_inner_induce_ne_zero` — core ∘ H2。
- 本体 `Xset_eq_irreducible_not_subset_characterKernel` (SibleyDadeHypothesis namespace, S08) — 最小 Z-仮説
  `Z≤H`+`[Z.Normal]` のみ。⊆=H1-genuine on Res / ⊇=H2-wrapper on Ind + `exists_inner_induce_ne_zero` +
  (1.6.a fwd `subsetCharacterKernel_induce_of_subgroupOf`) + orthonormality (`irreducibleCharacter_inner_eq_ite`)。
- 配置: S08-local (将来 S03 ConstituentKernel へ移設可)。**[Is] 2.21 不使用を実証**。
- **Lean 罠 (実装で判明)**: `inner_smul_right` は mathlib `_root_.inner_smul_right` と曖昧 → 完全修飾
  `OddOrder.RepresentationTheory.inner_smul_right`。`induce_mem_ZIrr`/`inner_induce_eq_inner_restrict` は
  nested `ClassFunction` namespace → `ClassFunction.` 前置。`coe_trivialIrreducibleCharacter` は
  `IrreducibleCharacter.` namespace。`star (↑n)`=`star_natCast`。

**✅✅ T7-c2 case A `X⊆Irr L` 完了 (2026-06-03, attended; full build 3562 green, axiom-clean #print 確認済, S08 sorry 不変=capstone のみ)**: brick① `eq_one_of_fixedPointFree_invariant` (S08, 汎用: 乗法的 `f` が FPF endo σ 不変 ⟹ `f≡1`, `commutatorMap_surjective`) + `inertia_eq_H_of_c2_caseA` (FPF-on-Z route: w∈I_L(θ)∩W₁∖1 なら [Is]2.27 の中心線形 φ が σ=(·)^w 不変 ⟹ φ≡1 ⟹ Z.subgroupOf H⊆Ker θ; 対偶 + complement split `L=H⋊W₁` で `I_L(θ)=H`; σ=`Z.normalizerMonoidHom ⟨w,_⟩`, C_Z(w)=Z∩W₂=⊥ で FPF; **Hall coprime 不要・任意 θ**) + `isIrreducibleCharacter_of_mem_Xset_caseA` (χ=Ind θ∈X⟹χ∉S(Z)⟹Z⊄Ker θ⟹bridge⟹6.34)。仮説 (hZH/hZcentral/hZnorm/hZfpf) は明示引数 (case-A の具体 Z 構成・(6.8) assembly 時に放電; honest, scaffolding 無)。AxiomsCheck は S08 を未 import (T6 結果も未登録) ゆえ未登録, #print axioms で clean 確認。
**🔜 T7 残**: なし (c1 Xset_eq✅ + case A X⊆Irr L✅; case B は X⊆Irr L 不要=T10)。**次 = T8** (DadeChainStep 実 instance: T8.3 degree + T8.4 Dmem 最重 + T8.5 hdeg_c[B2 待ち] + T8.6 enum)。
**次 = T8** (`DadeChainStep` 実 instance; B engine surgery で blocker 解消済 = `peterfalvi_66_coherence_of_X_from_dade`
が X-family で instantiate 可) → T9/T10 (glue) → T11 + capstone `sibleySetup_is_coherent` (S08 唯一の sorry)。

## I. B (engine surgery) refined plan — TRACTABLE adapter, NOT parallel engine (2026-06-03)

**🟢 重大発見: `retarget_isCoherent`(S07:2835) は X,Xbar を bare class function で取る (D₀ 非依存)**。
D₀ 結合は wrapper `retarget_isCoherent_of_decomposition`(3127, `D.retargetTargetPair` 経由) のみ。
⟹ B = **X-family adapter** (既存 engine `retarget_isCoherent` を直接呼ぶ)、parallel engine 不要。

**核心: X := Da.X** (Da = `CharacterPsiDecomposition τ χ (a•chi1)`, ψ=a•χ₁ supported decomp,
`htau1_mema:τ(χ−a·χ₁)∈ZIrr` から構成。**htau1_mem0(τχ∈ZIrr) 不要**)。`Da.X = D₀.X` (hX_eq) ゆえ同値。

**{X,X̄} facts は全部 supported route で導出可 (検証済, ψ=0/τχ∈ZIrr 不使用)**:
- `‖X‖²=1`: himg `τ(χ−a·χ₁)=X−a·ext(χ₁)` + `‖τ(χ−a·χ₁)‖²=‖χ−a·χ₁‖²=1+a²`(supported isometry,χ⊥χ₁)
  + `X⊥ext(χ₁)`((5.2.e) hperElem, X∈ℤ[R(χ)]⊥ext(χ₁)) + `‖ext(χ₁)‖²=‖χ₁‖²=1`。
- `‖X̄‖²=1`,`⟨X,X̄⟩=0` (X̄=X−τ(χ−χ̄)): `⟨X,τ(χ−χ̄)⟩=⟨τ(χ−a·χ₁),τ(χ−χ̄)⟩=⟨χ−a·χ₁,χ−χ̄⟩=1`
  (∑Da.coeff=⟨τ(χ−a·χ₁),∑R(χ)⟩=⟨τ(χ−a·χ₁),τ(χ−χ̄)⟩, supported isometry)。
- `X∈ZIrr`/`X̄∈ZIrr`: Da.X_eq (∑ over R(χ)) + τ(χ−χ̄)∈ZIrr。

**実装ステップ (build-green incremental, 既存 D₀/retargetTargetPair/of_decomposition stack は不変=supported-χ 用)**:
1. **`retargetTargetPair_fromSupported`** (~80): X:=Da.X の {X,X̄} orthonormality+ZIrr を上記 supported 導出で。
   入力 = Da + himg + supported-isometry facts + hperElem(X⊥ext(S₁)) + χ⊥χ₁/χ⊥χ̄/‖χ‖²=1 等。
2. **`retarget_isCoherent_of_supportedDecomposition`** (~40): Da + data → (1) で X facts 構成 → `retarget_isCoherent` 直呼。
3. **`retarget_isCoherent_fromDade_X`** (~60): Dade 層 wrapper。Da を htau1_mema (supported diff, provable) から構成、
   個別 support → **difference-support 弱化** (χ−a·χ₁ は 1 で消え H^# supported)、(2) を呼ぶ。
4. **rewire** `DadeChainStep.advance`(5173) を X-version に (or 分岐)。`peterfalvi_66_coherence_of_X_from_dade` 接続。
5. 抽象 `peterfalvi_66_coherence_of_X`(3934) 不変、AxiomsCheck clean、各 step `lake build OddOrder` green。

**要読込 (実装前)**: `RetargetTargetPair` struct(2169) / `eq_sum_of_psi_eq_zero` / supported-isometry lemma 名
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`) / `imageFamily.image_eq` / hperElem source。

### I 進捗 (2026-06-03 セッション)
- ✅ **step1** `retarget_isCoherent_of_supportedDecomposition` (commit 0ba7572, build-green): X:=Da.X の
  {X,X̄} 6 facts を supported route で導出 (‖X‖²=1 via `inner_self_chi_add_psi_eq`, ‖Y‖²=a²,
  ⟨X,(χ−χ̄)^τ⟩=⟨χ,χ⟩=1 via `inner_self_chi_eq_sum_coeff`)。**htau1_mem0 blocker 解消**。
- ✅ **step2** `retarget_isCoherent_of_supportedDecomposition_and_memberFamily` (commit 0a664bf): hperElem を
  Dmem family から discharge (既存 `inner_extension_*_orthogonal_imageSet*` 再利用)。
- 🔜 **step3**: (a) `dadeOrthonormalCharacterImageFamily`(~4500) を**差分-support** に弱化
  — `dadeIntegralCharacterMap_inner_eq_on_supported_span`(4460, 個別 support `hS:∀s∈S,supp⊆A` 要求) を
  差分集合 S={0, χ̄−χ} 等で適用 (χ−χ̄ は 1 で消え A-supported; iter1 設計と同じ)。
  (b) `retarget_isCoherent_fromDade_X`: Da を `ofProjection`(htau1_mema のみ, htau1_mem0 不要)で構成、
  差分-support imageFamily を渡し step2 を呼ぶ。
- 🔜 **step4**: `DadeChainStep.advance`(5146) を X-version に rewire (or 分岐) → `peterfalvi_66_coherence_of_X_from_dade` 解禁。

### I 訂正 (2026-06-03, anti-scaffold gate) — §I の「tractable adapter / htau1_mem0 解消」は誤り
step1-2 (`retarget_isCoherent_of_supportedDecomposition*`) は **X-family で scaffold** と判明
(`Da : CharacterPsiDecomposition τ χ (a•chi1)` が X で構成不能: structure field `tau1_inner_eq_on_support`
が full lattice {χ,χ.conj,ψ} の τ₁-isometry を要求, unsupported χ で `⟨τχ,τχ⟩≠⟨χ,χ⟩`)。
**真の fix = `CharacterPsiDecomposition.tau1_inner_eq_on_support` を差分 sublattice `zSpan{χ−χ.conj,χ−ψ}` に弱化**
(全 4 使用箇所 S07:1227/1296/2216/3473 は差分のみ; ofProjection→decompositionPair→sharedDecomposition→fromDade を
貫流する htau1_inner_eq param を差分集合 isometry に re-target, ~7-10 関数, invasive=attended)。
詳細 = `notes/meta/b_xpath_wiring_goal.md` 🛑 LOOP STOPPED 節。✅ step3a (`dadeOrthonormalCharacterImageFamilyOfDiff`,
18238b9) は genuine な差分-support R(χ) で field 弱化後の正当部品。

### I 進捗 2 (2026-06-03 attended, B engine surgery 大幅前進)
**✅ 完了・build-green・commit 済 (X-family per-step coherence path 全通)**:
- 真の fix: `tau1_inner_eq_on_support` 差分 sublattice 弱化 (9640c03)
- `decompositionDaFromDadeOfDiff` (ded579e): Da を X で ofProjection 直構成
- `dadeOrthonormalCharacterImageFamilyOfDiff` (18238b9): 差分-support R(χ)
- step1 `retarget_isCoherent_of_supportedDecomposition` + step2 `_and_memberFamily` (de-scaffolded)
- **`retarget_isCoherent_fromDade_X` (83f91c2)**: X-member の per-step adjoining 完成
  chain = fromDade_X → step2 → step1 → `retarget_isCoherent`、D₀/τχ∈ZIrr/個別 support 一切なし。

**🔜 残 step4 (DadeChainStep iteration layer, mechanical)**: `DadeChainStep`(S07:5397, ~30 field, 個別
support `hχsupp`/`hχbarsupp`/`haχ1supp` + famS 次数列) の X-version (`DadeChainStepX`: 差分-support 化) +
`advance` の X-version (`advanceX`: fromDade_X を呼ぶ) + `peterfalvi_66_coherence_of_X_from_dade` を X-chain に。
fromDade_X が per-step を供給済ゆえ、残りは structure の差分化と advance の付け替えのみ。

### I 進捗 3 — ✅✅ B engine surgery 完了 (2026-06-03): T8 engine blocker 解消
`peterfalvi_66_coherence_of_X_from_dade` が X-family で instantiate 可能に (full build + AxiomsCheck green)。
chain: DadeChainStep(差分-support) → advance(fromDade_X) → step2 → step1 → retarget_isCoherent、
Da=decompositionDaFromDadeOfDiff、hY=dade_Y_collapse_of_family(差分弱化)。commits 50bf9f0/5dda578。
**T8 の真の blocker (htau1_mem0/個別 support, 2 loop が STOP) 解消済**。残=T7 char data + DadeChainStep
実 instance + T9-T11 glue。

## 2026-06-13 (session 38 cont.⁴, /loop, user=「現状 RECON + 着手計画」): case-B 現状再精査 + 着手計画

**(4.10) 完成後の S08 sole sorry (`sibleySetup_is_coherent` X-nonempty branch, S08_CoherenceTheorems:59) 再 RECON。**
旧 RECON (session 37 cont.³「open blocker 多数」) より**大幅に良い状態** — 以下が全部 BUILT 判明:

### ✅ BUILT (旧 RECON で未認識だった完成部品):
- **capstone glue** `coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_generator_mixed_inner`
  (S08_CoherenceCore:5026): `hXirr` + `hX` (X-coh) + `ν` + `hagreeX/Y` (generator-level) + `hmixed`
  (generator cross-inner) + `hgen` (span gen) → **`hyp.CoherenceTarget` を直接生成**。最終組立は完成。
- §7 engine `coherentUnion_of_glued` (+変種) / Y-coh `coherentYset` / Frobenius X-coh engine (T8
  `peterfalvi_66_coherence_of_X_from_dade` 差分-support 化済) — 全 DONE。
- **c2 X-coh `certainType_isCoherent`** (S06_CertainTypeCoherence:505, =(4.9)(b)): `(h:Hypothesis46)(hk:k≠1)
  → IsCoherent (dadeIntegralCharacterMap h.dade0 h.tau) (certainTypeSet h k) (supportInSubgroup A L)`. DONE。
- Frobenius consumer `indChainDecomposition_of_frobenius_pairUnionBaseAnchor...` (S08_CoherenceTheorems:339)
  も CoherenceTarget を内部構成 (glue data 与えれば)。

### 🔴 残 (sorry filling, `hyp.cases` で c1/c2 分岐):
- **shared glue** (両 case 要, 構造的): `hXirr` (Xset 既約) / `hgen` (Xset∪Yset span gen) / `ν` (合成 ext) /
  `hmixed` (cross-inner)。部分支援あり (`inner_span_Xset_Yset_eq_zero_of_irreducible_X` 既在)。
- **Frobenius (c1)**: `hstepData` = `PairUnionBaseAnchorCommonIndexPrimePowerStepData` (S08_CoherenceCore:8743,
  ~30 field の per-step 素冪次数データ; idx/p/m₁/mχ/mmem… = Ind from Frobenius kernel の次数の素冪構造、
  (6.6)) を構成 = **T7 char-theory 本体 (genuine, 中〜大)**。→ `Xset_commutator..._of_frobenius hF hXne hstepData`
  を hX に渡し `coherentS_..._generator_mixed_inner` で組立。
- **CertainType (c2)**: **Hypothesis46-from-Sibley bridge** = SibleyDadeHypothesis + cert
  (CertainTypeHypothesis + |W₂|素/W₂⊆[H,H]/coprime|H||W1|) から (4.6) Hypothesis46 を構成
  (subH / A_covers (4.6.d 被覆) / tic TI-cyclic on G / dade0=dade / tau / …) = **大 (A_covers/tic 検証が本体)**。
  → certainType_isCoherent → certainTypeSet=Xset 同定 → glue。

### ▶ 着手計画 (build-green incremental, 推奨順):
1. **shared glue helpers** (最低リスク, 両 case 基盤): hXirr / hgen / ν+hmixed の構成パターン確立。
2. **Frobenius branch 完遂** (c2 より tractable): hstepData (T7) 構成 → `coherentS_..._generator_mixed_inner`
   で c1 case discharge。**ただし sorry 全消には c2 も要** (1 sorry → 分岐後も両 branch 実証明必須、
   scaffold 分割は不可 [[scaffold-sorry-free-not-done]])。
3. **c2 branch**: Hypothesis46-from-Sibley bridge (大) → certainType_isCoherent → glue。
4. **wire `hyp.cases`**。
**effort: Frobenius=中大 (T7), c2=大 (bridge)。複数セッション。FT 経路 (§9 (7.10) card_G0_lower_bound) の入力。**
**正本=本 session 38 cont.⁴。capstone glue + 両 X-coh constructor + Y-coh + engine 全 BUILT; 残=T7 stepData + c2 bridge + shared glue。**

## 2026-06-13 (session 38 cont.⁵, /loop): case-B RECON 訂正 — Frobenius producer + 両 hXirr 既存

**訂正**: cont.⁴ で「shared glue hXirr 要」としたが**誤り** — 既存:
- `isIrreducibleCharacter_of_mem_Xset_of_frobenius` (S08_CoherenceCore:5067, Frobenius hXirr)
- `isIrreducibleCharacter_of_mem_Xset_caseA` (5275, c2 case-A hXirr)
- **Frobenius CoherenceTarget producer `coherentS_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner`
  (10057)**: `hF + hXne + hstepData + ν + hagreeX + hagreeY + hmixed + hgen → CoherenceTarget`
  (hXirr は内部 discharge)。⟹ Frobenius branch = この def 1 呼び出し + (hstepData, ν, hagreeX/Y, hmixed, hgen) 構成。
(自作 `Xset_irreducible_of_frobenius` は冗長判明 → reverted。教訓: 部品 build 前に既存 lemma を grep。)

### ⚠ 正味進捗評価 (honest): case-B は RECON 3 tick で net-0 code (redundant 1 個 revert)。
infra はほぼ全 BUILT (10057 + capstone 5026 + 両 hXirr + Y-coh + engine)。残は**大 piece のみ**:
- **Frobenius**: `hstepData` (PairUnionBaseAnchorCommonIndexPrimePowerStepData, ~30 field, (6.6) 素冪次数
  解析 = deg(Indθ)=|W₁|θ(1), θ(1)=p^m for p-group H) = **不可分の大構造 (incremental landable でない)**。
  + glue (ν/hagreeX/hagreeY/hmixed/hgen)。
- **c2**: Hypothesis46-from-Sibley bridge (subH/A_covers/tic 構築) + glue。
両 branch 必須 (sorry 全消)。**各 multi-session、incremental-easy piece 無し** ⟹ case-B は sustained 多セッション grind。
**判断: ユーザーに scope 確認 (case-B grind commit vs (4.10) milestone 区切り)。正本=本 cont.⁵。**

## 2026-06-13 (session 38 cont.⁶, /loop): stale-note 訂正 + 正直な進捗 flag (空転)

**🔧 stale 訂正**: 旧 Agent 分析の「B4 m≥2 未解決」「(6.5) DAG 欠落」は**少なくとも B4 は解決済**:
`two_le_Yset_ncard` (S08_CoherenceCore:4893) は**証明済 sorry-free** (`two_le_ncard_of_conjugate_closed_of_noReal`
+ Yset closure/no-real)、`coherentYset` 稼働。⟹ **Y-coherence は B4-blocked ではない (済)**。
S08_CoherenceCore 全体 sorry-free (唯一の sorry = S08_CoherenceTheorems:59 X-nonempty branch)。

**case-B X-nonempty sorry の真の残り** (infra は Y-coh/capstone glue/X-coh constructor/両 hXirr 全 built):
- **Frobenius**: hstepData (`PairUnionBaseAnchorCommonIndexPrimePowerStepData`, ~30-field 不可分構造,
  prime-power 次数 = **H p-群要**; SibleyDadeHypothesis.H は NILPOTENT のみ ⟹ p-群還元 (6.5) が前提) + glue。
- **c2**: Hypothesis46-from-Sibley bridge (Hypothesis46 全 field 構築, (6.5)-independent だが不可分大構造) + glue。
- 両 branch とも**大・不可分構造 (sorry scaffold 不可) + deep sub-pieces** ⟹ 60s-loop-grind に不適。

**⚠ 正直な進捗 flag (thumbs-down)**: case-B は RECON ~5 tick で **net-0 code** (冗長 hXirr 1 revert)。
infra は揃うが残りは focused 多セッション構築要 (loop-grind 不向き)。(4.10) は完成・full build+AxiomsCheck 緑。
**判断はユーザーへ**: (4.10) 区切り / c2-bridge を地道 loop grind / (6.5) reduction 専念。正本=本 cont.⁶。

## 2026-06-13 (session 39, /loop, user=「Bレーンを進める。難所を回避しない」): c2-bridge grind 着手 — `tic` lift infra landed

ユーザー裁可 = **c2-bridge を地道 grind** (難所回避禁止)。RECON 空転を断ち切り**実コード landed** (net-0 脱却)。

### ✅ landed: `TICyclicHypothesis.mapOfInjective` (S05_TICyclic:84, build-green + axiom-clean [propext/choice/Quot のみ])
一般 lemma: 単射 `φ : H →* G` に沿って `TICyclicHypothesis H` を `TICyclicHypothesis G` へ transfer。
14 field 中 **13 = 機械的 transfer** (W-block: `map_mono`/`map_eq_bot_iff`+`ker_eq_bot_iff`/`map_sup`/
`disjoint_def`+`mem_map`/`card_map_of_injective`/`equivMapOfInjective`+`isCyclic_of_surjective`、
V-block: sharp は `map_one`+inj、`mem_map_of_mem`、`W_normalizes_V` は `map_mul`/`map_inv`)。
**残 1 field = `V_ti` を仮説 `hVti : IsTISubset (φ '' V) (W.map φ)` として取る** = c2 bridge の真の障害を 1 点に隔離。

### 🎯 確定した真の障害 (深掘り RECON、cont.⁶ より精密):
- **c2 `tic` の核心 = G-level `V_ti` (= W−W₂ が **G** で TI)**。これは (4.6.b)。
  **(4.3.a) の L-level `toTICyclicHypothesis` (TI in ↥L) からは transfer 不可** — `IsTISubset` は
  ambient を上げると条件が強くなる (G 全体を走る g が conj を起こしうる; `IsTISubset` 定義
  TISubset.lean:72 参照)。`CertainTypeHypothesis` は `Hypothesis ↥L` (L-level W-data) + `dade : S04.Hypothesis G A L`
  のみ保持、G-level TI-cyclic は**未保有**。⟹ G-level V_ti は新規構成 ((4.6.b) 本体)。
- **Frobenius `hstepData` の核心 = prime-power 次数** (`hθχ:θχ=p^mχ` 等, structure 8743 確認)。
  deg(Ind θ)=|W₁|·θ(1); θ(1)=p^m は **H が p-群のとき**のみ。`H_nilpotent` だけでは不足 ⟹ **(6.5) p-群還元が前提**。

### ▶ 次の一手 (c2 grind 継続、推奨順):
1. **c2 bridge の easy field を landable lemma 化**: `subH:=K:=H` で `A_covers` (A=sharpImage H, K=H ⟹
   x∈C_H(hh), x≠1 ⟹ x∈H# = A、ほぼ自明)、`subH_le_K`/`W2_le_subH` (W₂⊆[H,H]⊆H)。
2. **G-level V_ti = (4.6.b)** 本体: W=(W₁⊔W₂).map L.subtype が G で TI。W cyclic Hall の TI 性。←真の hard core。
   `mapOfInjective` が他 13 field を吸収済 ⟹ これだけ供給すれば `tic` 完成。
3. `dade0`/`tau` = A₀=A∪V^L への Dade datum 拡張。
→ `tic`+`A_covers`+`dade0`+`tau` で `Hypothesis46`-from-cert bridge → `certainType_isCoherent` →
   `certainTypeSet=Xset` 同定 + `dadeIntegralCharacterMap=hyp.tau` 同定 → glue。
**正本=本 session 39。`mapOfInjective` は再利用可能 (Frobenius branch でも W-lift に使える可能性)。**

## 2026-06-13 (session 39 cont., /loop): 🔑🔑 KEY FIX — `cases` を `Hypothesis46` へ強化 (faithfulness gap 是正)

**🔑 決定的発見 (mmd 照合)**: 教科書 **(6.8)(c2)** は literal "**Hypothesis (4.6) holds**" (04.8 mmd L146)。
そして **(4.6)** (04.6 mmd L53-63) は **(4.6.b) "G and W satisfy (3.1)"** = ambient TI-cyclic (`tic`) を**含む**
+ (4.6.d) A₀=A∪V^L 上の Dade datum (`dade0`/`tau`)。⟹ **(4.6) = repo の `Hypothesis46` そのもの**。

**旧 `cases` の faithfulness gap**: c2 disjunct が **弱い `CertainTypeHypothesis`** ((4.2) 構造 +A 上 dade のみ)
を供給 → ambient TI-cyclic を**未供給**。session 39 で確定したとおり G-level V_ti は (4.3.a) の ↥L-TI から
**transfer 不可** ⟹ 旧 cases では c2 X-coh は**構成不能** (「ambient TI を無から作る」= 不可能)。
**これが過去 ~5 tick 空転の真因** — 教科書が**仮定する**ものを構成しようとしていた。

### ✅ 是正 commit (build-green): `cases` c2 disjunct を `∃ h46 : Hypothesis46, h46.dade=dade ∧ h46.K=H ∧ …` へ
- `SibleyDadeHypothesis.cases` (S08_CoherenceCore:3309) を `CertainTypeHypothesis` → `Hypothesis46` に強化。
  side conds (prime/W₂⊆[H,H]/coprime) は不変、`cert.X` → `h46.X` (extends 経由で全 projection 解決)。
- import `S06_CertainHypothesis46` 追加 (cycle 無: S06→S08 正方向)。
- 唯一の destructure 消費点 (3864 `isIrreducibleCharacter_induce_of_degree_one`) を
  `h46.toCertainTypeHypothesis` 射影で adapt (hK/hW1/hW2 は defeq でそのまま通過)。
- **producer 不在** (SibleyDadeHypothesis は orphaned, 消費のみ) ⟹ 破壊なし; S09 consumer は cases 非 destructure。
- 全 build + AxiomsCheck 緑 (sorry 不増 = S08_CoherenceTheorems:59 の 1 本のみ、guard 不変)。

### 🎯 これで c2 が**構成可能**に: (4.6)-construction 義務は **producer** (§9 (7.10) application = maximal-subgroup
structure が供給) へ移動 — **教科書と同じ配置**。`mapOfInjective` (session 39) は今や producer 側
(eventually (4.3.a) tic を L→G lift し (4.6).tic を作る) の infra と reframe。

### ▶ 次の一手 (c2 X-coh wiring、`Hypothesis46` 在庫前提):
1. **certainTypeSet h k = hyp.Xset ⁅H,H⁆ 同定** (X の定義照合; certainType の (4.6) 定義 vs Sibley Xset)。
2. **τ-bridge**: `certainType_isCoherent h46 hk` は A₀-map (`dadeIntegralCharacterMap h46.dade0 h46.tau`) 上の
   coherence。Sibley capstone は `hyp.tau` (A=H# map) 上を要求。両者を関連付け = (6.8.2)/(6.8.2.3) 内容
   (η₁^{τ₁} 定数 on Z# 等)。これは genuine だが tractable (構成不能でない)。
3. → X-coh w.r.t. hyp.tau → 既存 capstone glue (`coherentS_..._generator_mixed_inner`) で Y-coh と合流。
**正本=本 session 39 cont.。難所の root cause を特定し faithful 化で解除 (回避でなく是正)。**

## 2026-06-13 (session 39 cont.², /loop): case-B coherence の**正確な inventory** (旧 framing 訂正) + 新 leaf 着手

**🔧 旧 framing 訂正 (重要)**: 「c2 X-coh = `certainType_isCoherent` (4.9) + certainTypeSet=Xset 同定」は
**oversimplification/誤り**。`certainTypeSet` = {列和 μ_j 同次数} = (4.9) の 𝒯 で、Sibley Xset = {Ind_H^L θ}
とは別パラメータ化。教科書 **(6.8.2)** の case-B coherence は**自己完結の別論法** (mmd 04.8 L178-224):
- **(6.8.2.1)** η^{τ₁} は Z^# 上定数 [(1.9) Galois + (5.9.a) + Z⊆ker η]。
- **(6.8.2.2)** (6.7)-合同 inner-product 公式 [reg-char 分解 + |H| mod]。
- **(6.8.2.3)** X-側 (χ−aη₁)^τ 分解 [[Is]2.27, Z⊆Z(H)]。
- τ₂ 組立。
⟹ `certainType_isCoherent` は (4.9) として (6.8.2.3) 等で**部分利用**されうるが、case-B coherence の
直接 producer ではない。**Don't re-grind「certainType_isCoherent=c2 X-coh 直結」**。

**🔍 実 inventory (S08_CoherenceCore, 直接 grep; notes は信頼不可と判明)**: case-B は **central-Zc
program** (Zc=`centralCommutator`=Z(H).map⊓[H,H]) として実装、**Frobenius + c2-caseA variant が大半 built**:
- `Xset_centralCommutator_isCoherent_of_{frobenius,c2_caseA}` (9290/9325) / `_of_irreducible_X` (9112)。
- `restrict_extension_Yset_const_on_centralCommutator_of_frobenius` (9820) = **(6.8.2.1) for Frobenius** (Zc, degree-value route)。
- `coherentXunionYset_centralCommutator_of_himg_ortho` (9854) = X∪Y coh shell、**残=`himg_ortho`** (b≡c≡0 mod a, L3(3b))。
- 全 `_of_frobenius` は `[IsPGroup p ↥H]` を**仮説 thread** ⟹ (6.5) p-群還元は capstone caller の義務。
- **frontier = c2-math-case-B variant (Z=W₂ central prime) + himg_ortho + (6.5) + capstone 配線。**

**🎯 重要 infra 発見 (notes 未記載)**: **(6.8.2.1) は一般形で既存** =
`OddOrder.Peterfalvi.S07.IsCoherent.extension_constant_on_sharp_of_prime` (S07_CoherenceGalois:424、
Z prime 要)。case-B は w₂ prime ゆえ適用可。かつ **`hyp.tau = dadeIntegralCharacterMap hyp.dade …`**
(S08:3459 abbrev) ゆえ一般 lemma が `hyp.coherentYset` に直接適用可。
- discharge 要件: hSirr (✅`isIrreducibleCharacter_of_mem_Yset` 4652)、hpair (✅`two_le_Yset_ncard`)、
  hZp (✅case-B w₂ prime)、hZA (W₂⊆[H,H]⊆H ⟹ W₂^#⊆H^#=sharpImage H、易)、
  hlat (✅coherentYset.extension_mem_ZIrr)、**hSu (Yset Galois-closed)**、**hspan (support)**、**hηx (η const on W₂)**。

### ✅ landed (新 leaf `S08_CaseBCoherence.lean`, build-green+axiom-clean, full build 3802): keystone 補題
`OddOrder.RepresentationTheory.ClassFunction.mapRingEquiv_induce` (一般): `σ(Ind_H^G θ) = Ind_H^G(σθ)`
(σ:ℂ≃+*ℂ)。σ は ring hom で ⅟|H| (∈ℚ, `map_natCast`/`map_inv₀`) を固定 + induceTerm に termwise。
⟹ **Yset Galois-closure (hSu) の engine** (各 Ind_H^L(linear χ) ↦ Ind_H^L(linear(σ∘χ)))。
新 leaf は c2-case-B coherence の蓄積先 (root closure 配線済 OddOrder.lean:144)。

### ▶ 次の一手 (新 leaf で積む、推奨順):
1. **hSu = Yset Galois-closure**: `mapRingEquiv_induce` + linear-char Galois (σ∘χ linear≠1) + `mem_Yset_iff_exists_linear_source`。
2. **hηx = η const on W₂** (case-B): η=Ind(linear θ), θ trivial on [H,H]⊇W₂, W₂⊆Z(H) ⟹ Ind 値計算 η(w)=η(1)。
3. **hspan** (support 条件) + **hZA** (易) → これで `extension_constant_on_sharp_of_prime` を coherentYset@W₂ に適用 = **(6.8.2.1)-for-c2-case-B** landed。
4. → (6.8.2.2) [(6.7)合同, peterfalvi_67 既存] → (6.8.2.3) → τ₂ 組立。‖ himg_ortho (Frobenius 側、別途)。

**⚠ 正直評価**: case-B coherence は sustained-expert 多セッション仕事 (各 step に sub-lemma 群)。loop-tick
では incremental brick を積む方針。本 session 39 全体: faithful cases fix (cont.) + 正確 inventory (cont.²) +
keystone `mapRingEquiv_induce`。**正本=本 session 39 cont.²。**

## 2026-06-13 (session 39 cont.³, /loop): hSu = Yset Galois-closure landed (S08_CaseBCoherence)

**✅ landed (build-green + axiom-clean, full build 3802)**: (6.8.2.1)-for-c2-case-B の discharge を 2 補題前進。
- **`ClassFunction.mapRingEquiv_linearIrreducibleCharacter`** (一般): `σ(linear χ) = linear((Units.map σ)∘χ)`
  (`mapRingEquiv_apply`+`linearIrreducibleCharacter_apply`+`Units.coe_map`、`rfl`)。
- **`SibleyDadeHypothesis.Yset_mapRingEquiv_mem` = `hSu`** (Yset Galois-closed): η=Ind(linear χ)∈Y ⟹
  σ(η)=Ind(linear((Units.map σ)∘χ))∈Y (`mapRingEquiv_induce`+上記 linear twist+`induce_linearIrreducibleCharacter_mem_Yset`;
  χ'≠1 は `Units.map_injective σ.injective`)。

### `extension_constant_on_sharp_of_prime` 適用に向けた discharge 状況 (coherentYset @ Z=W₂, case B):
- ✅ hτ (coherentYset)、✅ hSirr (`isIrreducibleCharacter_of_mem_Yset`)、✅ hpair (`two_le_Yset_ncard`)、
  ✅ hZp (w₂ prime)、✅ hlat (coherentYset.extension_mem_ZIrr)、✅ **hSu (本 session)**、✅ hA' (le_refl)。
- 🔴 残 2: **hZA** (W₂^#⊆sharpImage H、W₂⊆[H,H]⊆H ゆえ易) + **hspan** (φ∈zSpan Yset, φ(1)=0 ⟹ supp⊆A')
  + **hηx** (η const on W₂; η=Ind(linear θ), θ trivial on [H,H]⊇W₂, W₂⊆Z(H) ゆえ Ind 値計算)。
  ※ hx/hy は適用時の W₂ 元 (case-B context で供給)。

### ▶ 次の一手 (S08_CaseBCoherence で積む):
1. **hZA** (易、case-B W₂≤[H,H] から) — 次の brick。
2. **hηx** (η const on W₂) — Ind 値計算 (W₂ central + θ trivial on [H,H])。
3. **hspan** (Yset span support 条件) — Yset 元は H 上 supported ゆえ。
4. → `extension_constant_on_sharp_of_prime` を組んで **(6.8.2.1)-for-c2-case-B** 完成 (η^{τ₁} const on W₂^#)。
→ (6.8.2.2) [(6.7)合同] → (6.8.2.3) → τ₂。**正本=本 session 39 cont.³。**

## 2026-06-13 (session 39 cont.⁴, /loop): hZA + hηx landed (S08_CaseBCoherence)

**✅ landed (build-green + axiom-clean, full build 3802)**: (6.8.2.1)-for-c2-case-B の discharge 2 件:
- **`SibleyDadeHypothesis.coe_mem_sharpImage_of_mem_commutator` = `hZA`**: z∈⁅H,H⁆, z≠1 ⟹ (z:G)∈sharpImage H
  (⁅H,H⁆≤H via `Subgroup.commutator_le`+`commutatorElement_def`)。
- **`SibleyDadeHypothesis.Yset_apply_eq_apply_one_of_mem_commutator` = `hηx`** (η const on ⁅H,H⁆):
  η=Ind(linear χ), z∈⁅H,H⁆⊆H◁L ⟹ 全 conj g⁻¹zg∈⁅H,H⁆ (normal)、χ は ⁅H,H⁆ で trivial
  (commutator ↥H ↦ commutator ℂˣ=⊥ via `map_commutator`+`commutator_eq_bot_iff_le_centralizer`;
  ⁅H,H⁆↔commutator ↥H は `(commutator ↥H).map H.subtype = ⁅H,H⁆`)、各 induceTerm=1 ⟹
  η z = ⅟|H|·|L| = |W₁| = η 1 (`index_mul_card`+`index_H_eq_card_W1`+`invOf_mul_self`)。

### (6.8.2.1)-for-case-B discharge: 残 hspan のみ (ほぼ free)
🎯 **`hspan` は `zSpan_S_support_subset_of_apply_one_eq_zero` (S08_CoherenceCore:5775) からほぼ自動**:
それは S 版 (φ∈zSpan S, φ(1)=0 ⟹ supp⊆supportInSubgroup(sharpImage H)L)。Yset⊆S (`Yset_subset_S`)
⟹ zSpan Yset⊆zSpan S ⟹ Yset 版が span monotone で従う。

### ▶ 次の一手:
1. **hspan-for-Yset** (zSpan_S 版 + Yset⊆S、ほぼ free)。
2. **(6.8.2.1)-for-case-B assembly**: `extension_constant_on_sharp_of_prime` を coherentYset@W₂ に適用
   (hyp.cases から case-B data 抽出: h46/W₂ prime; hSirr=isIrreducibleCharacter_of_mem_Yset,
   hlat=coherentYset.extension_mem_ZIrr, hpair=two_le_Yset_ncard wiring)。
   ⟹ `coherentYset.extension η` は W₂^# 上定数 = **Peterfalvi (6.8.2.1)** 完成。
3. → (6.8.2.2) [(6.7)合同 peterfalvi_67] → (6.8.2.3) → τ₂。**正本=本 session 39 cont.⁴。**

## 2026-06-13 (session 39 cont.⁵, /loop): 🎉 Peterfalvi (6.8.2.1) for case B COMPLETE

**✅✅ milestone landed (build-green + axiom-clean, full build)**: case-B coherence の**第一 sub-step 完成**:
`SibleyDadeHypothesis.coherentYset_extension_const_on_W2` (S08_CaseBCoherence): W₂ prime ∧ W₂⊆⁅H,H⁆,
η∈Yset, x,y∈W₂^# ⟹ `coherentYset.extension η (y:G) = coherentYset.extension η (x:G)` (η^{τ₁} は W₂^# 上定数)。
`S07.IsCoherent.extension_constant_on_sharp_of_prime` に全 hyp 供給して組立:
- hSirr=`isIrreducibleCharacter_of_mem_Yset`、hSu=`Yset_mapRingEquiv_mem`、hlat=`extension_mem_ZIrr`+`subset_span`、
  hpair=`Set.exists_ne_of_one_lt_ncard`(`two_le_Yset_ncard`)、hZp=hprime、hZA=`coe_mem_sharpImage_of_mem_commutator`、
  hηx=`Yset_apply_eq_apply_one_of_mem_commutator`、hspan=`zSpan_S_support_subset_of_apply_one_eq_zero`(span_mono Yset⊆S)。
- gotcha: lemma は **S07_CoherenceGalois** 在 (import 追加要); dot-notation 不可 → 完全修飾名で hτ 明示引数。

### ▶ 次の一手 = Peterfalvi (6.8.2.2) (mmd 04.8 L186-206):
φ∈Irr Z (Z=W₂), φ≠1 ⟹ `(Ind_Z^L φ − |H:Z|η₁)^τ = X − |H:Z|Y` (X⊥Y^{τ₁}, Y=η₁^{τ₁} or m=2 で −η₂^{τ₁})。
証明骨子: α:=Ind_Z^L φ − |H:Z|η₁ は Supp⊆H^# → reciprocity `⟨α^τ,ψ⟩=⟨α,Res_L ψ⟩`、(6.8.2.1) で
Res_Z ψ = aρ_Z+b1_Z、(6.7) `peterfalvi_67` で b≡ψ(1) mod |H| ⟹ ⟨α^τ,ψ⟩≡0 mod |H:Z|、norm 評価
‖α^τ‖²=‖α‖²<2|H:Z|² で (x−1)²+(m−1)x²≤1 ⟹ x∈{0,1}。**(6.7) machinery (peterfalvi_67_centralCommutator,
reg-char sumNonInflatedDegreeMulChar) は既 landed; reciprocity inner_dadeIntegralCharacterMap_eq_inner_restrict も既存。**
→ (6.8.2.3) → τ₂ assembly。**正本=本 session 39 cont.⁵。**

## 2026-06-13 (session 39 cont.⁶, /loop): (6.8.2.2) 着手 — α-support step landed

**✅ landed (build-green + axiom-clean)**: (6.8.2.2) の「Supp(α)⊆H^#」step (α=Ind_{W₂}^L φ − c·η₁):
- 一般 **`ClassFunction.support_induce_subset_of_le_normal`** (H'≤N, N◁G ⟹ supp(Ind_{H'}^G θ)⊆N;
  `support_induce_subset_of_normal` の非正規 source 一般化、`induceTerm_of_not_mem`+`Normal.conj_mem`)。
- **`SibleyDadeHypothesis.support_indW2_sub_smul_subset_sharpImage`**: W₂≤H, α(1)=0 (=Ind_{W₂}φ(1)=c·η₁(1))
  ⟹ supp(Ind_{W₂}φ − c·η₁)⊆supportInSubgroup(sharpImage H)L (両 piece H-supported + α(1)=0 で 1 除去)。
  ※ c (=|H:W₂|) は α(1)=0 仮説で defer (index 計算回避)。

### ⚠ (6.8.2.2) 残ステップ + prerequisite gap:
(6.8.2.2) 本体 = `(Ind_Z^L φ − |H:Z|η₁)^τ = X − |H:Z|Y` (X⊥Y^{τ₁})。残:
1. **reciprocity** `⟨α^τ,ψ⟩=⟨α,Res_L ψ⟩` (✅ `inner_tau_eq_inner_restrict` + α-support 本 session)。
2. 🔴 **reg-char 分解** `Res_Z ψ = aρ_Z + b1_Z` — **ρ_Z (regular character) が repo に無い** (要新規 def/補題)。
   ψ=η^{τ₁} は (6.8.2.1) `coherentYset_extension_const_on_W2` で Z^# 上定数 ⟹ Res_Z ψ は Z^# 上定数
   ⟹ aρ_Z+b1_Z 形。**ρ_Z 構築 + 「Z^# 上定数 ⟹ aρ+b1」が次の主 prerequisite。**
3. **(6.7) 合同** b≡ψ(1) mod |H| (✅ `peterfalvi_67_centralCommutator`)。
4. **norm endgame** ‖α^τ‖²=‖α‖²<2|H:Z|² ⟹ (x−1)²+(m−1)x²≤1 ⟹ x∈{0,1}。

### ▶ 次の一手: **ρ_Z (regular character) + 「class fn on Z const on Z^# = aρ_Z+b1_Z」**
これが (6.8.2.2) reg-char step の前提。汎用 (任意有限群 Z)。→ then (6.8.2.2) assembly。
**正本=本 session 39 cont.⁶。** **進捗 honest 評価: case-B coherence は (6.8.2.1)✅→(6.8.2.2)[multi-tick,
ρ_Z 要]→(6.8.2.3)→τ₂→capstone→(6.5) の長い grind。steady brick/tick で進行中 (空転なし)。**

## 2026-06-13 (session 39 cont.⁷, /loop): (6.8.2.2) reciprocity step landed

**✅ landed (build-green + axiom-clean)**: `SibleyDadeHypothesis.inner_tau_indW2_sub_smul_eq`:
α=Ind_{W₂}φ−c·η₁ (α(1)=0), ψ∈CF G ⟹ `⟨α^τ,ψ⟩ = ⟨φ,Res_{W₂}Res_L ψ⟩ − c·⟨η₁,Res_L ψ⟩`
(= (6.8.2.2) の `⟨α,Res_L ψ⟩ = ⟨φ,Res_Z ψ⟩ − |H:Z|⟨η₁,Res_L ψ⟩`)。
`inner_tau_eq_inner_restrict` (α-support 経由) + `inner_sub_left`/`inner_smul_left` +
Frobenius reciprocity `inner_induce_eq_inner_restrict`。**gotcha**: `inner φ (...)`/`induce W₂` の
inner は ↥W₂ 上 ⟹ `[Fintype ↥W2]` を**binder** に要 (statement elaboration は proof の haveI より先)。

### (6.8.2.2) 残: reg-char 分解 (ρ_Z) + 合同 + norm
1. ✅ reciprocity (本 session)。
2. 🔴 **reg-char 分解 (ρ_Z) — 次の主 prerequisite**: ψ const on Z^# ((6.8.2.1)) ⟹ Res_Z ψ=aρ_Z+b1_Z、
   a=⟨φ,Res_Z ψ⟩∈ℤ、ψ(1)=a|Z|+b。**鍵関係 `ψ(1)−ψ(z) = |Z|·⟨φ,Res_Z ψ⟩` (z∈Z^#, φ∈Irr Z, φ≠1)**。
   ρ_Z は repo に無いが `column_orthogonality_diagonal`/`_not_conjugate` (ColumnOrthogonality.lean) が道具。
   ρ_Z を直接 `fun g => if g=1 then |Z| else 0` で def + ext で分解、or 鍵関係を column-orth で直接。
3. (6.7) `peterfalvi_67_centralCommutator` で b≡ψ(1) mod |H| ⟹ a|Z|≡0 mod |H| ⟹ **a≡0 mod |H:Z|**。
4. ⟹ ⟨α^τ,ψ⟩ = a − |H:Z|⟨η₁,Res ψ⟩ ≡ 0 mod |H:Z| + norm endgame ((x−1)²+(m−1)x²≤1)。

**▶ 次の一手 = reg-char 分解 (鍵関係 ψ(1)−ψ(z)=|Z|⟨φ,Res ψ⟩ via column orthogonality)。正本=本 session 39 cont.⁷。**

## 2026-06-13 (session 39 cont.⁸, /loop): (6.8.2.2) reg-char relation landed (ρ_Z 不要)

**✅ landed (build-green + axiom-clean)** — ρ_Z を陽に作らず inner-product 直接計算で:
- **`sum_apply_eq_zero_of_ne_trivial`** (一般): φ≠trivial irr ⟹ ∑_{g∈Γ} φ(g)=0
  (orthonormality `irreducibleCharacter_inner` ⟨φ,1⟩=0 + trivial char 値1)。
- **`apply_one_sub_apply_eq_card_mul_inner`** (一般, = (6.8.2.2) reg-char core): φ linear (φ(1)=1) nontrivial,
  f const on Γ^# ⟹ **`f(1) − f(z) = |Γ|·⟨f, φ⟩`** (z≠1)。`Res_Z ψ = a ρ_Z + b 1_Z`, a=⟨Res ψ,φ⟩,
  ψ(1)−ψ(z)=a|Z| の実質。innerSum split (`Finset.add_sum_erase` at 1) + ∑φ=0 + f-const + `classical` (erase 要 DecidableEq)。

### (6.8.2.2) 残: (6.7) 合同統合 + norm endgame
1. ✅ α-support, ✅ reciprocity (⟨α^τ,ψ⟩=⟨φ,Res ψ⟩−c⟨η₁,Res ψ⟩), ✅ reg-char relation (本 session)。
2. 🔴 **統合**: a:=⟨Res_{W₂}Res_L ψ, φ⟩∈ℤ (φ linear ∈ Irr W₂)、ψ(1)−ψ(z)=|W₂|·a (reg-char relation)、
   (6.7) `peterfalvi_67_centralCommutator`: ψ(1)≡ψ(z) mod |H| ⟹ |W₂|a≡0 mod |H|=|H:W₂||W₂| ⟹ **a≡0 mod |H:W₂|**。
   ⟹ ⟨α^τ,ψ⟩ = a − |H:W₂|⟨η₁,Resψ⟩ ≡ 0 mod |H:W₂|。**conjugate 注意: ⟨φ,Resψ⟩ vs ⟨Resψ,φ⟩ (a 実整数で一致)。**
3. 🔴 **norm endgame**: ‖α^τ‖²=‖α‖²<2|H:W₂|² ⟹ (x−1)²+(m−1)x²≤1 ⟹ x∈{0,1}, m=2 if x=1。
→ (6.8.2.2) 完成 → (6.8.2.3) → τ₂。**正本=本 session 39 cont.⁸。**

## 2026-06-13 (session 39 cont.⁹, /loop): c2 H-Sylow (coprimality-only) landed — (6.7) への前提

**✅ landed (build-green + axiom-clean)**: `SibleyDadeHypothesis.sylow_map_subtype_of_coprime`:
H p-群 + `Nat.Coprime (card H) (card W1)` ⟹ ∃ Q∈Syl_p(G), Q=H.map L.subtype。
**🔑 発見: `sylow_map_subtype_of_frobenius` は hF を coprimality 取得 (`coprime_card_kernel_complement`) に
1 箇所しか使わない** ⟹ coprimality を直接取れば Frobenius でも c2 でも動く一般版。c2 case の `cases` 側
条件 hcop がそれを供給。(dedupe 候補: S08_CoherenceCore の Frobenius 版はこれへ delegate 可。)

### これで c2 (6.7) が組める: 残 (6.8.2.2) endgame
1. ✅ α-support, reciprocity, reg-char relation, **c2 H-Sylow (本 session)**。
2. 🔴 **c2 (6.7)**: `peterfalvi_67_centralCommutator` の c2 版 — `peterfalvi_67_of_odd` (SylowTICongruence:140) を
   Q:=Ĥ (sylow_map_subtype_of_coprime), W₂⊆H# (coe_mem_sharpImage_of_mem_commutator) で適用。
   ψ=η^{τ₁} は virtual char ⟹ irreducible constituents に (6.7) 適用 + 合成 (or ZIrr 版)。
   結果: ψ(z)≡ψ(1) [ALGMOD |H|] for z∈W₂#。
3. 🔴 **統合**: reg-char relation ψ(1)−ψ(z)=|W₂|·a (a=⟨Res ψ,φ⟩∈ℤ) + (6.7) |W₂|a≡0 mod |H| ⟹ a≡0 mod |H:W₂|
   (ALGMOD→ℤ 整除 bridge 要)。⟹ ⟨α^τ,ψ⟩≡0 mod |H:W₂|。
4. 🔴 **norm endgame**。
→ (6.8.2.2) → (6.8.2.3) → τ₂。**正本=本 session 39 cont.⁹。**

## 2026-06-13 (session 39 cont.¹⁰, /loop): η^{τ₁}=±irr landed; norm-1-ZIrr 既存判明

**🔧 既存判明 (grep 不足の反省)**: norm-1 ZIrr 分類は**既存** — `exists_single_of_sum_sq_eq_one`
(InducedIrreducible:322) + `exists_zsmul_irreducibleCharacter_of_inner_self_one` (398, docstring に
「Peterfalvi (5.9.a) normalization step」明記)。自作 2 補題は重複 → revert。**再調査不要: norm-1 ZIrr=±irr は既存。**

**✅ landed (build-green + axiom-clean)**: `SibleyDadeHypothesis.coherentYset_extension_eq_zsmul_irreducible`:
η∈Yset ⟹ ∃ ε=±1, ξ∈Irr G, `coherentYset.extension η = ε • ξ`。η irr (⟨η,η⟩=1 via bundled
`irreducibleCharacter_inner`) + coherence norm 保存 (`extension_inner_eq`) + ZIrr (`extension_mem_ZIrr`)
⟹ η^{τ₁} norm-1 ⟹ ±irr (`exists_zsmul_irreducibleCharacter_of_inner_self_one`)。
**⟹ ψ=η^{τ₁} の (6.7) は単一既約 ξ に帰着** (ξ は η^{τ₁} の W₂^#-定数性を sign 込みで継承)。

### (6.8.2.2) 残: c2 (6.7) for ξ + 統合 + norm
1. ✅ α-support, reciprocity, reg-char relation, c2 H-Sylow, **η^{τ₁}=±irr (本 session)**。
2. 🔴 **c2 (6.7) for irreducible ξ**: `peterfalvi_67_of_odd` (SylowTICongruence:140) を Q:=Ĥ
   (`sylow_map_subtype_of_coprime`), Z:=W₂, ξ const on W₂# で適用。
   **hconst の第2項 = centralizer-card 定数性 |N_G(Ĥ)⊓C_G(w)| const on W₂#** が要 — c2 では
   W₂⊆Z(H) (case B) ⟹ C_L(w)=H⋊C_{W₁}(w); W₁ の W₂ 上作用の定数性が鍵 (certain-type 構造、要精査)。
   Frobenius は `inf_centralizer_centralCommutator_map` で供給; c2 W₂ 版は新規。
3. 🔴 ALGMOD→ℤ 整除 + 統合 (a≡0 mod |H:W₂|) + norm endgame。
**▶ 次 = centralizer-card 定数性 on W₂# (c2) or その精査。正本=本 session 39 cont.¹⁰。**

## 2026-06-14 (session 39 cont.¹¹, /loop): centralizer-card 定数性 core landed (W₂ 中心性経由)

**✅ landed (build-green + axiom-clean)**: `SibleyDadeHypothesis.inf_centralizer_eq_of_mem_center`:
w∈Z(↥L) ⟹ `(L:Subgroup G) ⊓ C_G((w:G)) = L`。**case B で W₂⊆Z(↥L)** (math-B 条件 W₂⊆Z(H) + W=W₁⊔W₂ cyclic
⟹ W₂ も W₁ と可換 ⟹ W₂ 中心) ゆえ、W₂# 上 centralizer-card = |L| 定数 = `peterfalvi_67_of_odd` hconst
第2項。Frobenius `inf_centralizer_centralCommutator_map` (=H) の case-B 類似 (=L、より単純)。

### (6.8.2.2) 残: c2 (6.7) 組立 + 統合 + norm
1. ✅ α-support, reciprocity, reg-char relation, c2 H-Sylow, η^{τ₁}=±irr, **centralizer-card core (本 session)**。
2. 🔴 **W₂⊆Z(↥L) 導出** (case B): math-B 条件 W₂⊆Z(H) [dichotomy `eq_bot_or_eq_of_le_of_card_prime` on Z(H)∩W₂、
   W₂ prime] + W₁,W₂ 可換 (W cyclic) ⟹ W₂⊆Z(↥L)。**要: case-B 分岐の W₂⊆Z(H) を hypothesis 化 or 導出。**
3. 🔴 **c2 (6.7) 組立**: `peterfalvi_67_of_odd` (P:=Ĥ via sylow_map_subtype_of_coprime, Z:=W₂,
   ξ const on W₂#, hconst = [ξ const (要、ξ は η^{τ₁}=±ξ の W₂#-定数性継承) ∧ centralizer-card (本 session)])
   → ξ(z)≡ξ(1) [ALGMOD |H|] → η^{τ₁}(z)≡η^{τ₁}(1) (ε 倍)。
4. 🔴 ALGMOD→ℤ 整除 (a≡0 mod |H:W₂|) + 統合 + norm endgame。
**▶ 次 = W₂⊆Z(↥L) 導出 (case-B) or c2 (6.7) 組立 (hconst の ξ-const 部分精査)。正本=本 session 39 cont.¹¹。**

## 2026-06-14 (session 39 cont.¹², /loop): 逆 ALGMOD→ℤ bridge landed + warning cleanup

**✅ landed (build-green + axiom-clean)**: `dvd_of_intCast_algMod`: (j:ℂ)≡(k:ℂ)[ALGMOD n] (j,k,n:ℤ, n≠0)
⟹ n∣(j−k) in ℤ。`cong_def` で (j−k)/n が alg-int ⟹ rational ゆえ整数 (`isIntegral_rat_imp_int`
ClassSumAlgebra) ⟹ n∣(j−k)。**🔑 (6.7) の ALGMOD|H| を rational-integer 差 ψ(1)−ψ(z)=|W₂|·a に適用 →
|H|∣|W₂|·a (整除) の変換。gotcha: `set q:ℚ` で single Rat.cast に保つ (← のため; 分配されると
isIntegral_rat_imp_int が unify せず)。`open scoped OddOrder.AlgInt` で [ALGMOD] 記法。**
+ warning cleanup (unused hyp→_hyp ×2, unused smul_eq_mul simp arg ×2; long-line は残置=cosmetic)。

### (6.8.2.2) 残: c2 (6.7) 組立 + 統合 + norm
✅ α-support, reciprocity, reg-char relation, c2 H-Sylow, η^{τ₁}=±irr, centralizer-card core, **逆 ALGMOD bridge (本 session)**。
🔴 残: (1) **W₂⊆Z(↥L) 導出** (case-B: W₂⊆Z(H)+W cyclic); (2) **c2 (6.7) 組立** =
`peterfalvi_67_of_odd` を ξ (η^{τ₁}=±ξ の rep 版、要 IrreducibleCharacter→Representation bridge),
P:=Ĥ, Z:=W₂, hconst=[ξ const on W₂# ∧ centralizer-card (本 session core)] で適用 → ξ(z)≡ξ(1) [ALGMOD|H|];
(3) **統合**: reg-char (ψ(1)−ψ(z)=|W₂|a) + 逆 bridge (本 session) ⟹ |H|∣|W₂|a ⟹ a≡0 mod |H:W₂| ⟹
⟨α^τ,ψ⟩≡0 mod |H:W₂|; (4) **norm endgame**。
**▶ 次 = IrreducibleCharacter→Representation bridge (c2 (6.7) 組立用) or W₂⊆Z(↥L) 導出。正本=本 session 39 cont.¹²。**

## 2026-06-14 (session 40, /loop): case-B (6.7) machinery + 統合 core 完成 (3 commits)

**✅✅✅ landed (build-green + axiom-clean, S08_CaseBCoherence)** — (6.8.2.2) の (6.7) 鎖を一気に 3 brick:

1. **`peterfalvi_67_central` (74a0f0b1)** = case-(B) (6.7) adapter (Frobenius `peterfalvi_67_centralCommutator`
   の central-Z 版)。abstract `Z ≤ H` central in ↥L (`Z ≤ Subgroup.center ↥L`) + irreducible ρ const on
   (Z.map L.subtype)^# ⟹ `ρ.character z ≡ ρ.character 1 [ALGMOD |H|]`。`peterfalvi_67_of_odd` の全構造仮説を
   P:=Ĥ (`sylow_map_subtype_of_coprime`)・Z:=Z.map L.subtype で discharge: hZnormal (central⇒normal inline),
   hPz (Ĥ≤L≤C_G(z) since z central), hconst centralizer-card (両辺=|L| via `inf_centralizer_eq_of_mem_center`)。
   **Sylow は `cases` の coprimality のみ使用 (Frobenius 非依存)。**

2. **`restrict_extension_Yset_charValue_cong_caseB` (a1c7b699)** = consumer (Frobenius
   `restrict_extension_Yset_charValue_cong_of_frobenius` ミラー)。η^{τ₁}=ε•ξ
   (`coherentYset_extension_eq_zsmul_irreducible`) → **ξ=ρ.character は `ξ.isIrreducible` で既存**
   (🔧 「bridge を作る」は grep 不足の誤認; IrreducibleCharacter→Representation は既存) → (6.8.2.1) constancy
   `coherentYset_extension_const_on_W2` を ρ.character へ transfer (ε cancel) → adapter →
   `Res^G_L(η^{τ₁})(z) ≡ Res^G_L(η^{τ₁})(1) [ALGMOD |H|]` for z∈W₂^#。**`W₂ ⊆ Z(↥L)` は hypothesis (deferred)。**

3. **`card_H_dvd_card_W2_mul_regCharCoeff` (7b875b23)** = 統合 core。φ linear nontrivial ∈ Irr W₂,
   a=⟨Res_{W₂}Res_L ψ, φ⟩=m∈ℤ ⟹ **`|H| ∣ |W₂|·m`**。z₀∈W₂^# (prime⇒nontrivial) で f=Res_{W₂}Res_L ψ
   const on W₂^# (`coherentYset_extension_const_on_W2`) → reg-char `apply_one_sub_apply_eq_card_mul_inner`
   で f(1)−f(z₀)=|W₂|·m → (6.7) consumer で f(z₀)≡f(1) → f(1)−f(z₀)≡0 → 差が ℤ 値 |W₂|·m ⟹
   `dvd_of_intCast_algMod` で |H|∣|W₂|·m。gotcha: `set f` 下で `simpa using restrict_apply` は
   `this→True` に潰れる → term-mode `:= restrict_apply ...` (W₂.subtype 1 ≡ 1 defeq) で hf1/hfz。

### ⚠ (6.8.2.2) 残 (司令塔/次 loop 向け):
1. **|W₂| cancel**: `|H| ∣ |W₂|·m` + `|H| = (W₂.subgroupOf H).index · |W₂|` (`index_mul_card` +
   `card_subgroupOf` + `inf_eq_left.mpr hW2H`) ⟹ `(W₂.subgroupOf H).index ∣ m` (`mul_dvd_mul_iff_left`, |W₂|>0)。
2. **⟨α^τ,ψ⟩ ≡ 0 mod |H:W₂|** (ψ∈𝒴^{τ₁})**: reciprocity `inner_tau_indW2_sub_smul_eq`
   (⟨α^τ,ψ⟩=⟨φ,Res_{W₂}Res_L ψ⟩−c⟨η₁,Res_L ψ⟩, c=|H:W₂|, α(1)=0 要) + ⟨φ,Res ψ⟩=conj(m)=m (整数) +
   |H:W₂|∣m (step1) + ⟨η₁,Res ψ⟩∈ℤ (`mem_ZIrr_inner_int`) ⟹ ⟨α^τ,ψ⟩ = m − |H:W₂|·(ℤ) ∈ |H:W₂|ℤ。
   ※ α^τ∈ZIrr G & ψ∈ZIrr G で ⟨α^τ,ψ⟩∈ℤ (`inner_mem_ZIrr_int`) — 整数値の divisibility として述べる。
3. **j>1 の値**: ⟨α^τ, η_j^{τ₁}−η_1^{τ₁}⟩ = ⟨α, η_j−η_1⟩ = |H:Z| (reciprocity + Y-degree |W₁|)。
4. **α^τ 分解**: α^τ = X − |H:Z|η_1^{τ₁} + x|H:Z|∑_j η_j^{τ₁}, X⊥𝒴^{τ₁} (step2,3 から)。
5. **norm**: ‖α^τ‖²=‖α‖²=|L:Z|+|H:Z|² (Pf (1.5.b)), |L:Z|=|W₁||H:Z|<|H:Z|² (W₁ FPF on H/Z) ⟹
   ‖α^τ‖²<2|H:Z|² ⟹ (x−1)²+(m−1)x²≤1 ⟹ x=0, or x=1∧m=2。⟹ **(6.8.2.2) 完成** → (6.8.2.3) → τ₂。
- **W₂⊆Z(↥L) 導出 (deferred 仮説)**: math-B `W₂⊆Z(H)` (`eq_bot_or_eq_of_le_of_card_prime` on Z(H)⊓W₂,
  prime) + W cyclic (W₁,W₂⊆W abelian) ⟹ W₂⊆Z(↥L)。Hypothesis46 の W cyclic structure 要精査。
**正本=本 session 40。** 進捗良好 (空転なし, steady brick/tick)。

## 2026-06-14 (session 40 cont., /loop): (6.8.2.2) step 1 完成 — ⟨α^τ,ψ⟩≡0 mod |H:W₂| (2 commits)

**✅✅ landed (build-green + axiom-clean)** — (6.8.2.2) の第一主ステップ完了:

4. **`index_W2_dvd_regCharCoeff` (c8930ded)** = |W₂| cancel。`card_H_dvd...` (|H|∣|W₂|m) +
   |H|=|W₂|·[H:W₂] (`index_mul_card` on W₂.subgroupOf H + `subgroupOfEquivOfLe` で card 同一視 +
   `relIndex` defeq subgroupOf.index) + `mul_dvd_mul_iff_left` (|W₂|≠0) ⟹ `(W₂.subgroupOf H).index ∣ m`
   (= 教科書 a≡0 mod |H:Z|)。
5. **`inner_tau_alpha_dvd_index` (b75a06da)** = **⟨α^τ,ψ⟩ ∈ ℤ ∧ |H:W₂| ∣ it** (ψ=η'^{τ₁}∈𝒴^{τ₁})。
   - **c=|H:W₂| を直接計算** (hypothesis 化不要): Ind_{W₂}φ(1)=[L:W₂]·φ(1)=[H:W₂]·|W₁|=|H:W₂|·η₁(1)
     (`induce_apply_one`+`relIndex_mul_index`+`index_H_eq_card_W1`+`Yset_apply_one`)。
   - reciprocity `inner_tau_indW2_sub_smul_eq` で ⟨α^τ,ψ⟩=⟨φ,Res_{W₂}Res_L ψ⟩−|H:W₂|·⟨η₁,Res_L ψ⟩。
   - ⟨φ,Res⟩=star⟨Res,φ⟩=m (`inner_conj_symm`+`mem_ZIrr_inner_int`, m整数), |H:W₂|∣m (step4);
     ⟨η₁,Res_L ψ⟩=b'∈ℤ (flip)。⟹ ⟨α^τ,ψ⟩=m−|H:W₂|·b', |H:W₂|∣it。
   - gotchas: `inner_conj_symm` は mathlib `_root_.inner_conj_symm` と ambiguous→`OddOrder.RepresentationTheory.`
     完全修飾; `restrict_mem_ZIrr`→`ClassFunction.restrict_mem_ZIrr`; `[Fintype ↥W2]` は型に出ない
     (inner は G 上のみ)→ binder 削除 + `haveI := Fintype.ofFinite _` (sibling lemmas は型に W₂-inner があり要)。

### ⚠ (6.8.2.2) 残 (decomposition + norm cluster, 次 loop):
6. **j>1 の値**: ⟨α^τ, η_j^{τ₁}−η_1^{τ₁}⟩ = ⟨α, η_j−η_1⟩ = |H:Z| (reciprocity `inner_tau_eq_inner_restrict`
   + Y inner: Res_L(η_k^{τ₁}) と η_j の inner; η^{τ₁} coherence の等長性使用)。←要 Y-coherence inner API 精査。
7. **α^τ 分解**: step5+6 から α^τ = X − |H:Z|η_1^{τ₁} + x|H:Z|∑_j η_j^{τ₁}, X⊥𝒴^{τ₁} (x∈ℤ)。
   ← 𝒴^{τ₁} 正規直交基底への射影分解。
8. **norm endgame**: ‖α^τ‖²=‖α‖² (τ 等長, Pf (1.5.b)/(2.x)) =|L:Z|+|H:Z|², |L:Z|=|W₁||H:Z|<|H:Z|²
   (W₁ FPF on H/Z≠1) ⟹ ‖α^τ‖²<2|H:Z|² ⟹ (x−1)²+(m−1)x²≤1 ⟹ x=0, or x=1∧m=2 ⟹ **(6.8.2.2) 完成**。
   ← ‖α‖² 計算 (Ind norm + η₁ norm + cross term) + W₁-FPF-on-H/Z の |L:Z|=|W₁||H:Z| が要点。
→ (6.8.2.3) → τ₂ → (6.8) capstone。**正本=本 session 40 cont.。** 全 brick build-green+axiom-clean, 空転なし。

## 2026-06-14 (session 40 cont.², /loop): decomposition+norm 基盤 2 brick + 構造解明

**🔑 構造解明 (再調査不要)**: (6.8.1) Frobenius case が (6.8.2.2) と**構造平行**で直接テンプレ:
- `inner_tau_scaledDiff_tau_Yset_diff_of_frobenius` (S08_CoherenceCore:10462) = step6 cross-term テンプレ。
- `inner_self_tau_scaledDiff_of_frobenius` (:10524) = step8 norm テンプレ。
- **Dade isometry** = `S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp.dade hyp.hconj (S:={...}) (hsupp) (mem)(mem)` ⟹ ⟨τφ,τψ⟩=⟨φ,ψ⟩ (φ,ψ supported on `supportInSubgroup (sharpImage H) L`)。**`hyp.tau` は defeq `dadeIntegralCharacterMap hyp.dade (fullDadeIsometryData hconj)`** ゆえ `exact` 一発。
- **coherence agreement** = `S07.IsCoherent.extends_on_supported`: β∈zSupportedSpan Yset A ⟹ extension β = tau β (A=supportInSubgroup, NOT L^#)。**Y-diff η_j−η_1 は supported** (`sMember_diffSupport_of_charValue_eq`, η_j(1)=η_1(1)=|W₁|)。
- **η∈Y は W₂ 上定数** = `Yset_apply_eq_apply_one_of_mem_commutator` (W₂⊆⁅H,H⁆) ⟹ Res_{W₂}η_j=Res_{W₂}η_1。

**✅✅ landed (build-green + axiom-clean)**:
6. **`inner_self_tau_indW2_sub_smul` (57c4ccc8)** = **‖α^τ‖²=‖α‖²** (α=Ind_{W₂}φ−c•η₁, α(1)=0)。
   `support_indW2_sub_smul_subset_sharpImage` + Dade isometry on {α} singleton。`exact` 一発。
7. **`inner_induce_W2_Yset_diff_eq_zero` (4dde3faa)** = **⟨Ind_{W₂}φ, η'−η⟩=0** (Res_{W₂}η'=Res_{W₂}η, η const on W₂)。
   reciprocity `inner_induce_eq_inner_restrict` + restrict 等価。

### ⚠ (6.8.2.2) 残 (次 loop):
- **step6 full** `⟨α^τ, η_j^{τ₁}−η_1^{τ₁}⟩=|H:Z|`: agreement [(η_j^{τ₁}−η_1^{τ₁})=extension(η_j−η_1)=tau(η_j−η_1),
  extension の map_sub 線型 + extends_on_supported] + isometry [dadeICM_inner_eq on {α, η_j−η_1}] +
  source [本 session ⟨Ind φ,η_j−η_1⟩=0 ∧ ⟨η₁,η_j−η_1⟩=−1 (Y orthonormal)] ⟹ ⟨α,η_j−η_1⟩=0−|H:Z|(−1)=|H:Z|。
- **step7 分解**: α^τ = X − |H:Z|η_1^{τ₁} + x|H:Z|∑_j η_j^{τ₁}, X⊥𝒴^{τ₁} (step1 ≡0 mod |H:Z| + step6 から
  𝒴^{τ₁} 正規直交基底への射影)。
- **step8 norm endgame**: ‖α‖²=‖Ind_{W₂}φ‖²−2|H:Z|Re⟨Ind φ,η₁⟩+|H:Z|²‖η₁‖²。⟨Ind φ,η₁⟩=⟨φ,Res η₁⟩=
  |W₁|⟨φ,1⟩=0 (φ nontrivial), ‖η₁‖²=1, ‖Ind_{W₂}φ‖²=⟨φ,Res Ind φ⟩=|I_L(φ):W₂|=|L:W₂| (要 I_L(φ)=L, Pf(1.5.b)) ⟹
  ‖α‖²=|L:W₂|+|H:W₂|²。|L:W₂|=|W₁||H:W₂|<|H:W₂|² (W₁ FPF on H/Z, |W₁|<|H:W₂|) ⟹ ‖α^τ‖²<2|H:W₂|² ⟹
  (x−1)²+(m−1)x²≤1 ⟹ x=0 or x=1∧m=2 ⟹ **(6.8.2.2) 完成**。← ‖Ind φ‖²=|L:W₂| (Mackey/inertia) と FPF が要点。
→ (6.8.2.3) → τ₂ → capstone。**正本=本 session 40 cont.²。** 全 brick green+axiom-clean、空転なし。

## 2026-06-14 (session 40 cont.³, /loop): cross-term + agreement + inertia=⊤ (3 brick)

**✅✅✅ landed (build-green + axiom-clean)**:
8. **`inner_tau_indW2_sub_smul_tau_Yset_diff` (9eb006cf)** = step6 cross-term `⟨α^τ, (η'−η₁)^τ⟩ = c`
   (Dade isometry on {α, η'−η₁} + source `inner_induce_W2_Yset_diff_eq_zero` + Y-orthonormal)。
   **inner は arg1 線型** (`inner_smul_left` = `c * ⟨⟩`, NOT star c) → 値は c。
9. **`coherentYset_extension_Yset_diff_eq_tau` (44d38256)** = agreement `η'^{τ₁}−η₁^{τ₁} = (η'−η₁)^τ`
   (`extends_on_supported` + `map_sub` + zSupportedSpan membership)。cross-term を extension 形へ変換。
10. **`inertia_eq_top_of_le_center` (339e848c)** = central W₂ ⟹ `inertia φ = ⊤` (conjBy 自明、`mem_center_iff`)。
    一般補題 (hyp 不要、`omit [Fintype G][Fintype ↥L][Invertible G][Invertible ↥L]`)。

**⚠ 過程ミス (記録)**: warning cleanup で `omit … in` を docstring の後ろに置き build-red commit (917fc62d)→follow-up 3 件で復旧。教訓=build 緑確認と commit を別 bash step に ([[feedback-verify-build-before-commit]])。

### ⚠ (6.8.2.2) 残 (次 loop):
- **‖Ind_{W₂}φ‖² = |L:W₂|**: `card_mul_inner_self_induce_eq_card_inertia` (|W₂|·‖Ind φ‖²=|inertia|) +
  `inertia_eq_top_of_le_center` (=⊤, card=|L|) + |W₂| 除算 ⟹ ‖Ind φ‖²=|L|/|W₂|=|L:W₂|。φ:IrreducibleCharacter W₂ 要。
- **‖α‖² = |L:W₂| + |H:W₂|²**: ‖Ind φ − c•η₁‖² 展開。⟨Ind φ,η₁⟩=⟨φ,Res η₁⟩=|W₁|⟨φ,1⟩=0 (φ nontrivial; Res η₁=|W₁|·1 既証
  `inner_induce_W2_Yset_diff_eq_zero` の中身), ‖η₁‖²=1, c=|H:W₂|。
- **|L:W₂| < |H:W₂|²** = |W₁|<|H:W₂| (W₁ FPF on H/Z; case-B 構造要精査) → ‖α^τ‖²<2|H:W₂|²。
- **step7 分解** (α^τ を 𝒴^{τ₁} 正規直交基底へ射影) + **step8 quadratic** ((x−1)²+(m−1)x²≤1 ⟹ x∈{0,1})。
→ (6.8.2.2) 完成 → (6.8.2.3) → τ₂。**正本=本 session 40 cont.³。**

## 2026-06-14 (session 40 cont.⁴, /loop): norm-source 完成 (3 brick) — ‖α^τ‖²=|L:W₂|+c·c̄

**✅✅✅ landed (build-green + axiom-clean, 各 commit 前に別 step で緑検証)**:
11. **`inner_self_induce_eq_index_of_le_center` (6045d392)** = **‖Ind_{W₂}φ‖²=|L:W₂|=W₂.index** (central W₂)。
    `card_mul_inner_self_induce_eq_card_inertia` (|W₂|·‖Ind φ‖²=|inertia|) + `inertia_eq_top_of_le_center`
    (=⊤, `Subgroup.card_top`=|L|) + `card_mul_index` (|L|=|W₂|·index) + `mul_left_cancel₀`。
    ⚠ `card_mul_inner_self_induce_eq_card_inertia` は `[Invertible (Nat.card ↥W2:ℂ)]` 要 (instance 失敗が whnf timeout 誘発)。
12. **`inner_induce_W2_Yset_eq_zero` (5a7d6a69)** = **⟨Ind_{W₂}φ, η⟩=0** (φ nontrivial)。reciprocity +
    Res_{W₂}η=const|W₁| (η const on ⁅H,H⁆⊇W₂) + ∑_w φ(w)=0 (`sum_apply_eq_zero_of_ne_trivial`)。
13. **`inner_self_indW2_sub_smul_eq` (64b3a78c)** = **‖α‖²=W₂.index + c·star c** (α=Ind φ−c•η₁)。
    展開 + ‖Ind φ‖²=index + ⟨Ind φ,η₁⟩=0 (+conj) + ‖η₁‖²=1。c=(|H:W₂|:ℂ) で c·c̄=|H:W₂|² ⟹ |L:Z|+|H:Z|²。

### 📋 norm endgame 材料 全 landed:
- ‖α^τ‖²=‖α‖² (`inner_self_tau_indW2_sub_smul`) ∘ ‖α‖²=W₂.index+c·c̄ (`inner_self_indW2_sub_smul_eq`)
  ⟹ **‖α^τ‖² = W₂.index + c·star c**。
- step1: ⟨α^τ,ψ⟩∈ℤ ∧ |H:W₂|∣it (`inner_tau_alpha_dvd_index`)。
- step6: ⟨α^τ,(η'−η₁)^τ⟩=c (`inner_tau_indW2_sub_smul_tau_Yset_diff`) + agreement (`coherentYset_extension_Yset_diff_eq_tau`)。

### ⚠ (6.8.2.2) 残 = 最終 assembly (次 loop; ここからが構造的ハードコア):
- **FPF bound `|W₁| < |H:W₂|`** ⟹ W₂.index=|L:W₂|=|W₁|·|H:W₂|<|H:W₂|² ⟹ ‖α^τ‖²<2|H:W₂|²。
  ← case-B (c2) 構造: W₁ acts FPF on H/W₂ (C_H(w)=W₂ for w∈W₁#)。Hypothesis46/certain-type 要精査。
- **step7 分解**: α^τ を 𝒴^{τ₁} 正規直交基底へ射影 → α^τ = X − c·η_1^{τ₁} + x·c·∑_j η_j^{τ₁}, X⊥𝒴^{τ₁}
  (step1 ≡0 mod c + step6 差=c から係数決定)。← 射影論法 (Frobenius (6.8.1) に類似テンプレ有?要調査)。
- **step8 quadratic**: ‖α^τ‖²=‖X‖²+c²(x−1)²+(m−1)x²c² <2c² ⟹ (x−1)²+(m−1)x²≤1 ⟹ x=0 or x=1∧m=2。
- **最終 statement** `α^τ = X − |H:Z|η_1^{τ₁}` (b=0 reduction) → (6.8.2.3) → τ₂。
**正本=本 session 40 cont.⁴。** norm-source 完結、残=射影分解+FPF+quadratic。空転なし。

## 2026-06-14 (session 40 cont.⁵, /loop): variant trichotomy landed; decomposition recipe確定

**✅ landed (build-green + axiom-clean)**:
14. **`eq_zero_or_edge_of_dvd_of_normLt` (cbf69fc6)** = quadratic trichotomy `< 2a²` 変種
    (`eq_zero_or_edge_of_dvd_of_normBound` の `≤1+a²` を `<2a²` に; case-B norm |L:Z|+a²<2a² 用)。pure ℤ。

### 🔑 decomposition assembly recipe (Brick C, 次 loop = full focus 一気に):
**テンプレ = `coeff_eq_neg_or_edge_of_frobenius` (S08_CoherenceCore:10639-10780) を逐行ミラー**、ingredient 差替:
- step3 bb: `dvd_inner_tau_scaledDiff_extension...frobenius` → **`inner_tau_alpha_dvd_index` (η':=η₁)**
  ⟹ `∃ bb, ⟨α^τ, extension η₁⟩=bb ∧ index∣bb`。
- hcoeff (⟨α^τ,extension η⟩=bb or bb+c): `inner_tau_scaledDiff_tau_Yset_diff...frobenius` →
  **`inner_tau_indW2_sub_smul_tau_Yset_diff` (=c) + `coherentYset_extension_Yset_diff_eq_tau` (agreement)**。
  η≠η₁ 枝: htaud = agreement.symm, hconst = cross-term, `inner_sub_right` で ⟨α^τ,ext η⟩=bb+c。
- Bessel: **`sum_sq_le_inner_self_re horth (α^τ) hβval`** (S08_CoherenceCore:150) — そのまま。
  horth/hEinj/hβval/hsum は Frobenius と同形 (Yset_finite.toFinset.image extension, hYon, hEinj)。
- norm_re: `inner_self_tau_scaledDiff...frobenius` (=1+a²) → **`inner_self_tau_indW2_sub_smul` ∘
  `inner_self_indW2_sub_smul_eq`** ⟹ ‖α^τ‖²=W₂.index + c·star c。c=(index:ℂ) real ⟹ star c=c ⟹ =W₂.index+c²。
  `.re` 取り: (W₂.index + c²).re = W₂.index+c² (実)。⚠ c=((W₂.subgroupOf H).index:ℂ), star c=c via `Complex.star_ofNat`/`star_natCast`。
- trichotomy: `eq_zero_or_edge_of_dvd_of_normBound` (≤1+a²) → **`eq_zero_or_edge_of_dvd_of_normLt` (<2a²)**。
  hsum: bb²+(m−1)(bb+c)² ≤ W₂.index+c² (Bessel)。**要 FPF bound W₂.index<c²** ⟹ <2c² ⟹ apply variant
  (a=c=(W₂.subgroupOf H).index, b=bb+c, m=Yset.ncard)。⟹ bb=−c ∨ (m=2∧bb=0)。
- 結論: `⟨α^τ, extension η₁⟩ = −c ∨ (Yset.ncard=2 ∧ ⟨α^τ,extension η₁⟩=0)` (= Frobenius と同形)。

### ⚠ 残 (Brick C と並行 or 後):
- **Brick B = FPF bound `W₂.index < |H:W₂|²`** (= |W₁|<|H:W₂|): case-B C_H(w)=W₂ (w∈W₁#) ⟹ W₁ FPF on H/W₂ ⟹
  |W₁| ∣ |H:W₂|−1 ⟹ |W₁|<|H:W₂|。**Brick C は FPF を hypothesis で受けて defer 推奨** (W₂⊆Z(↥L) と同パターン)。
  Hypothesis46/certain-type の C_H(w)=W₂ + FPF-order-divides 要調査。
- Brick C 後: 最終 (6.8.2.2) statement (b=0 reduction, m=2 swap) → (6.8.2.3) → τ₂。
**正本=本 session 40 cont.⁵。全 ingredient 在庫確認済 (Bessel/Yset_finite/two_le_Yset_ncard/variant)。空転なし。**

## 2026-06-14 (session 40 cont.⁶, /loop): 🎉 coefficient dichotomy COMPLETE (Brick C, first-try build)

**✅✅✅ MILESTONE landed (build-green + axiom-clean, 初回 build 一発)**:
15. **`coeff_eq_neg_or_edge_caseB` (b487fab8)** = **(6.8.2.2) coefficient dichotomy**
    `⟨α^τ, η₁^{τ₁}⟩ = −|H:Z| ∨ (|Y|=2 ∧ =0)` (α=Ind_{W₂}φ−|H:Z|η₁)。
    `coeff_eq_neg_or_edge_of_frobenius` (S08_CoherenceCore:10639) を逐行ミラー、ingredient 全差替成功:
    inner_tau_alpha_dvd_index (bb) / inner_tau_indW2_sub_smul_tau_Yset_diff + coherentYset_extension_Yset_diff_eq_tau
    (hcoeff) / sum_sq_le_inner_self_re (Bessel) / inner_self_tau_indW2_sub_smul∘inner_self_indW2_sub_smul_eq
    (norm |L:Z|+|H:Z|²) / eq_zero_or_edge_of_dvd_of_normLt (trichotomy)。
    **deferred hypotheses: hc2 (2≤|H:Z|), hFPF (|L:Z|<|H:Z|²)** = W₁-FPF-on-H/W₂ inputs。
    → **(6.8.2.2) の inner-product/norm/dichotomy 解析は全完了**。残=構造的 input + 最終 X-structure。

### ⚠ (6.8.2.2) 残 = 構造的 input + 最終 statement (次 loop):
- **Brick B = FPF bound `hc2`/`hFPF`** (deferred): case-B (c2) で C_H(w)=W₂ (w∈W₁#) ⟹ W₁ acts FPF on H/W₂
  (H/W₂≠1) ⟹ |W₁| ∣ |H:W₂|−1 ⟹ |W₁|<|H:W₂| ⟹ |L:W₂|=|W₁||H:W₂|<|H:W₂|² (=hFPF), 2≤|H:W₂| (=hc2)。
  **要調査**: Hypothesis46/certain-type の C_H(w)=W₂ field + FPF-order-divides (Frobenius 群 |kernel|≡1 mod |compl|?
  Isaacs Ch06 IsFrobeniusGroup or coprime action の `card_eq_...` 系)。|L:W₂|=|W₁||H:W₂| は relIndex_mul_index。
- **X-structure (step 4)** = `coeff_eq_neg_or_edge_of_frobenius` 後の Frobenius step-4 (S08_CoherenceCore:10774
  `...X-structure...`) を case-B でミラー: bb=−|H:Z| branch で X:=α^τ+|H:Z|η₁^{τ₁} ⊥ 𝒴^{τ₁}, ‖X‖²=‖Ind φ‖²/...,
  X∈ZIrr ⟹ α^τ=X−|H:Z|η₁^{τ₁}。→ (6.8.2.3) → τ₂ assembly → (6.8.2) capstone。
**正本=本 session 40 cont.⁶。** 🎉 dichotomy は (6.8.2.2) 最大の技術的山場、first-try で landed。空転なし。

## 2026-06-14 (session 40 cont.⁷, /loop): good-case X-structure landed; FPF deferred (deep)

**✅ landed (build-green + axiom-clean)**:
16. **`orthogonal_tau_indW2_add_extension_caseB` (b1cdc2d5)** = (6.8.2.2) good-case X-structure。
    `orthogonal_normOne_tau_scaledDiff_add_extension` (S08_CoherenceCore:10786) ミラー (norm 落とし)。
    hgood (⟨α^τ,η₁^{τ₁}⟩=−|H:Z|) ⟹ X:=α^τ+|H:Z|η₁^{τ₁} ⊥ 𝒴^{τ₁} ∧ X∈ZIrr G ⟹ α^τ=X−|H:Z|η₁^{τ₁}。
    Ind_{W₂}φ∈ZIrr=`induce_mem_ZIrr`+`IsIrreducibleCharacter.mem_ZIrr φ.2`; α^τ∈ZIrr=`dadeIntegralCharacterMap_mem_ZIrr_of_supported`。
    gotcha: `classical` 要 (if-Decidable); `if_neg (Ne.symm hee)` (`.symm` は ¬-arrow に projection 不可)。

### 🔭 FPF bound (hc2/hFPF) discharge = 深い構造 (調査結果, defer 継続):
- 必要: case-B `CertainTypeHypothesis.centralizer_W2` (C_L(x)⊓K=W₂, x∈W₁#) → W₁ acts FPF on H/W₂ →
  `IsFrobeniusGroup` 化 → `card_kernel_modEq_one` (Isaacs Ch06 FrobeniusGroup:274, |kernel|≡1 mod |compl|)
  ⟹ |W₁| ∣ |H:W₂|−1 ⟹ |W₁|<|H:W₂| ⟹ |L:W₂|=|W₁||H:W₂|<|H:W₂|² (=hFPF), |H:W₂|≥2 (=hc2)。
- **generic W2 と certain-type W₂ の接続**: 私の lemma 群は generic W2 (hW2comm/hW2cen 仮説)。case-B 適用時
  W2=h46.W2。FPF は h46.W2 専用 ⟹ **discharge は capstone wiring 時 (Hypothesis46 構造完備の場所)**。
  faithful (textbook も case-B 仮説下で (6.8.2.2) 証明)。**今は defer 継続が正しい**。

### ⚠ (6.8.2.2) 残 (character-theoretic, 次 loop tractable):
- **m=2 swap case** (bb=0 branch): η₁^{τ₁}↔−η₂^{τ₁} 入替で good-case に帰着 (textbook L: "second case reduces")。
- **(6.8.2.2) 最終 statement** = dichotomy + X-structure (両 branch) を `α^τ = X − |H:Z|Y` 形に組立。
- → **(6.8.2.3)** (χ∈X 版, [Is]2.27) → **τ₂ assembly** (6.8.2 proof) → capstone case-B branch。
**正本=本 session 40 cont.⁷。** (6.8.2.2) decomposition は good-case 完成。残=m=2 case + (6.8.2.3) + τ₂ + FPF(capstone時)。

## 2026-06-14 (session 40 cont.⁸, /loop): m≥3 good-case wrapper; hub merged b-peterfalvi (28 commits)

**🔀 hub 合流確認**: main `34c91f5e Merge 'b-peterfalvi' (Pf §6): (6.8.2) case B coherence — 新 leaf
S08_CaseBCoherence (28 commits)`。ff-merge で main 取込 (BG §12/§13, Pf §10-13 も同期)。

**✅ landed (build-green + axiom-clean)**:
17. **`inner_tau_indW2_extension_Yset_eq_neg_caseB` (e6d17c8f)** = |Y|≥3 で good case (relabel 不要)。
    `inner_tau_scaledDiff_extension_Yset_eq_neg_of_frobenius` (S08_CoherenceCore:11246) ミラー。
    dichotomy rcases + edge(m=2) を hm3 で omega 排除。⟹ |Y|≥3 で α^τ=X−|H:Z|η₁^{τ₁} 無条件。

### 📏 ⚠ S08_CaseBCoherence.lean = 1300 行 (分割閾値 1500 接近)。
次の主結果 (6.8.2.3 等) は**新 leaf** を切るか、frozen 部分 (3.x ヘルパー〜(6.8.2.2) ingredient) を
hub に分割依頼。S08_CaseBCoherence は現状 §3 helper + (6.8.2.1)〜(6.8.2.2) decomposition の混在。

### ⚠ (6.8.2.2)/(6.8.2) 残:
- **m=2 relabel case** (η₁^{τ₁}↔−η₂^{τ₁}): Frobenius S08_CoherenceCore:11550+ をミラー (intricate)。
- **(6.8.2.3)** (χ∈X 版) → **τ₂ assembly** (Frobenius `crux_of_third_anchor`/`coherentXunionYset_...glued`
  /`Xset_isCoherent` の case-B 版 = 大アーキテクチャ)。
- **構造的 cluster** (FPF/W₂⊆Z(↥L)/C_H(w)=W₂): capstone wiring 時に Hypothesis46/certain-type から discharge。
**正本=本 session 40 cont.⁸。honest 評価**: (6.8.2.2) decomposition (m≥3) は完成。capstone は τ₂ assembly +
§7 glue + 構造 discharge が残る marathon。steady brick で進行 (空転なし)、但し capstone は依然 distant。

## 2026-06-14 (session 40 cont.⁹, /loop): 🎉 m=2 relabel landed (uniform Y-witness); file 1387行

**✅ landed (build-green + axiom-clean, first-try)**:
18. **`exists_Ycoherence_hgood_caseB` (e2ec420f)** = m=2 relabel folded in → **uniform Y-coherence
    witness cY with ⟨α^τ, cY.extension η₁⟩ = −|H:Z|** (両 m≥3/m=2)。`exists_Ycoherence_hgood_of_frobenius`
    (S08_CoherenceCore:11555) ミラー。m=2: `coherentEqualDegree_swap_neg` (§7 generic) で η₁↦−η₂^{τ₁}、
    ⟨α^τ,η₂^{τ₁}⟩=|H:Z| (cross-term+agreement) ⟹ ⟨α^τ, cY' η₁⟩=−|H:Z|。eqRec transport 込みで first-try。
    → **(6.8.2.2) の "good value" production は m 全域で完成**。

### 📏 ⚠ S08_CaseBCoherence.lean = 1387 行 → 次 phase は新 leaf 必須。
**次 leaf = `S08_CaseBCoherence2.lean`** (import S08_CaseBCoherence) で:
- **general X-structure** (cY : IsCoherent param 版、`orthogonal_normOne_tau_scaledDiff_add_extension_general`
  ミラー): coherentYset hardcode を cY param 化 (cY.extends_on_supported で agreement inline)。
- **crux / α^τ = X − |H:Z|·cY η₁** (general cY): `exists_Ycoherence_hgood_caseB` の cY を消費。
- **(6.8.2.3)** (χ∈X 版, [Is]2.27) + **τ₂ assembly** (Frobenius `crux_of_third_anchor`/`coherentXunionYset
  _...glued`/`Xset_isCoherent` の case-B 版 = 大アーキテクチャ)。

### ⚠ 構造的 cluster (capstone wiring 時): FPF/W₂⊆Z(↥L)/C_H(w)=W₂ ← Hypothesis46/certain-type。
**正本=本 session 40 cont.⁹。honest**: (6.8.2.2) good-value production 完成 (m 全域)。残=assembly (general
X-structure→crux→τ₂→glue) + 構造 discharge = marathon だが character-theoretic content は (6.8.2.2) 完了間近。

## 2026-06-14 (session 40 cont.¹⁰, /loop): 🎉 (6.8.2.2) COMPLETE — packaged decomposition (new leaf)

**✅✅ landed (build-green + axiom-clean, both first-try; 新 leaf S08_CaseBCoherence2)**:
19. **`orthogonal_tau_indW2_add_extension_general_caseB` (16c3d108)** = general X-structure (cY param)。
    `orthogonal_normOne_tau_scaledDiff_add_extension_general` ミラー、cY.extends_on_supported で agreement inline。
20. **`exists_decomposition_caseB` (6aabacc2)** = **(6.8.2.2) packaged decomposition**
    `∃ cY X, α^τ = X − |H:Z|·cY.extension η₁ ∧ X⊥𝒴 ∧ X∈ZIrr`。`exists_Ycoherence_hgood_caseB` (uniform
    good value) + general X-structure を結合。**τ₂ assembly が消費する (6.8.2.2) の最終出力。Y:=cY.extension η₁。**
    → **🎉 (6.8.2.2) character-theoretic content 完全完成 (m 全域、m=2 relabel 込み)。**

### 🗂 ファイル構成 (現在):
- `S08_CaseBCoherence.lean` (1387行, frozen): §3 helpers + (6.8.2.1) + (6.8.2.2) ingredients + good-value production。
- `S08_CaseBCoherence2.lean` (新, active): general X-structure + packaged decomposition。assembly phase 継続先。

### ⚠ 残 = τ₂ assembly architecture (大) + 構造 discharge:
- **(6.8.2.3)** (χ∈X 版, [Is] Lemma 2.27): X-side `(χ−aη₁)^τ = X₁ − aY` 分解。Frobenius `crux_of_third_anchor`
  系の X-side。
- **τ₂ assembly** (Pf (6.8.2) proof): Z-linear map τ₂ on Z[X∪Y], coincides with τ on Z[X∪Y,L^#], η₁^{τ₂}=Y。
  Frobenius `coherentXunionYset_...glued_withDiagonal` / `Xset_isCoherent` の case-B 版 = **数百行アーキテクチャ**。
- **§7 glue + capstone** (`sibleySetup_is_coherent` の case-B branch)。
- **構造 cluster** (FPF/W₂⊆Z(↥L)/C_H(w)=W₂): Hypothesis46/certain-type から、capstone wiring 時。
**正本=本 session 40 cont.¹⁰。20 bricks landed across loop。(6.8.2.2) 完成は milestone。残=τ₂ marathon。**

## 2026-06-14 (session 40 cont.¹¹, /loop): 🗺 τ₂ assembly architecture 完全 mapping (投資 iteration)

**この iteration = アーキテクチャ投資** (Lean brick なし、残り全 path を確定)。(6.8.2.2) 完成後の
case-B coherence capstone (`sibleySetup_is_coherent` の case-B branch) への path を精査:

### 🔑 reuse 可能 (generic, 大幅省力):
- **X-coherence は Z-parametrized generic**: `Xset_centralCommutator_isCoherent_of_irreducible_X`
  (S08_CoherenceCore:9112) は `Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_withCover
  _of_irreducible_X (Z := ...)` (:9137) に delegate。Z=W₂ で reuse 可。per-step prime-power degree data
  は case-independent (X-degrees)。**case-B X-coherence = generic reuse + math-B X-irreducibility**。
- **§7 glue** (`coherentXunionYset_...glued_withDiagonal` / `coherentUnion_of_glued`) generic。
- **(6.8.2.2) decomposition** = `exists_decomposition_caseB` ✅ (glue の diagonal agreement input)。

### 🔴 構造的 cluster = bottleneck (certain-type/Hypothesis46 接続、deep):
1. **math-B X-irreducibility** (`isIrreducibleCharacter_of_mem_Xset_c2_caseB`, MISSING): case-A 版
   `_c2_caseA` (:5314) は `hA: Z(H)⊓W₂.subgroupOf H=⊥` + `centralizer_inf_..._eq_bot_of_c2_caseA` 経由。
   math-B (W₂⊆Z(H)) は別条件。generic `_caseA` (centralizer 条件 param) の math-B 版要。
2. **FPF bound** (hc2/hFPF): CertainTypeHypothesis.centralizer_W2 (C_L(w)⊓K=W₂) → W₁ FPF on H/W₂ →
   `card_kernel_modEq_one` (Isaacs Ch06 FrobeniusGroup:274) ⟹ |W₁|∣|H:W₂|−1 ⟹ |W₁|<|H:W₂|。
3. **W₂⊆Z(↥L)**: math-B `W₂⊆Z(H)` (`eq_bot_or_eq_of_le_of_card_prime`) + W cyclic ⟹ W₂ central in L。
- これら 3 つは全て **CertainTypeHypothesis / Hypothesis46 の field から導出** (capstone wiring 時)。

### 🟡 character-theoretic 残 (tractable, my work の χ-version):
- **(6.8.2.3)** (χ∈X 版 decomposition): `coeff_eq_neg_or_edge_of_frobenius` (χ∈X) の case-B 版。
  χ single irreducible (‖χ−aη₁‖²=1+a², Frobenius と同形) だが η₁^{τ₁} (6.7) は case-B (W₂)。
  my (6.8.2.2) ingredients の χ-version (cross-term/divisibility/norm) 要。

### ▶ 次の一手 (honest 優先順位):
**最 tractable = FPF bound (#2)** か **W₂⊆Z(↥L) (#3)** — どちらも certain-type field から比較的直接。
math-B X-irred (#1) と (6.8.2.3) は中規模。glue は全部揃ってから。
**honest 総括**: (6.8.2.2) ✅ milestone。残=構造 cluster (Hypothesis46 接続, deep) + (6.8.2.3) + glue。
X-coherence reuse で省力化判明。capstone は構造 cluster が gate の marathon。**正本=本 session 40 cont.¹¹。**

## 2026-06-14 (session 40 cont.¹², /loop): 🔓 構造 cluster 着手 — W₂⊆Z(↥L) discharge landed

**🔑 (4.2) Hypothesis 構造判明 (S06_DadeIsometryCertain:67)**: `centralizer_W2` (C_L(w)⊓K=W₂, w∈W₁#)
+ `commute_of_mem_W1_of_mem_W2` (W₂ commutes W₁, theorem 既存) + `isComplement` (L=K⋊W₁) が field/定理。
⟹ 構造 cluster は思ったより tractable (既存 (4.2) 定理を使う)。

**✅ landed (build-green + axiom-clean)**:
21. **`certainType_W2_le_center` (ef698712)** = **構造 discharge #3: W₂⊆Z(↥L)**。
    (4.2) Hypothesis + math-B (W₂ centralizes K = W₂⊆Z(H)) ⟹ W₂ central in L。
    complement 分解 g=k·w₁ + W₂↔K commute (math-B) + W₂↔W₁ commute (既存定理)。
    gotcha: `isComplement.surjective` は lambda-form hkw0 → `have hkw : ↑k*↑w₁=g := hkw0` で beta-reduce。
    **⟹ my (6.8.2.2) lemmas の `hW2cen` deferred hypothesis discharge 可 (capstone wiring 時)。**

### ⚠ 構造 cluster 残 (次 loop):
- **FPF bound (#2, hc2/hFPF)**: `centralizer_W2` (C_H(w)=W₂) ⟹ W₁ FPF on H/W₂ (C_{H/W₂}(w)=triv) ⟹
  IsFrobeniusAction/Frobenius group 化 → `card_kernel_modEq_one` (FrobeniusGroup:274, |W₁|∣|H:W₂|−1)
  ⟹ |W₁|<|H:W₂| ⟹ |L:W₂|<|H:W₂|² (hFPF), 2≤|H:W₂| (hc2)。**Frobenius action 構成が multi-step (要調査
  IsFrobeniusAction API + card_modEq)**。中規模。
- **math-B X-irreducibility (#1)**: `isIrreducibleCharacter_of_mem_Xset_caseA` の math-B 版 (centralizer
  条件 param)。inertia 計算。中規模。
### 🟡 character-theoretic 残: (6.8.2.3) (χ∈X, X-irred 要) + glue (generic, 全部揃ってから)。
**正本=本 session 40 cont.¹². 構造 cluster 着手 (W₂⊆Z(L) ✅)。残=FPF + X-irred + 6.8.2.3 + glue。**

## 2026-06-14 (session 40 cont.¹³, /loop): 🔓 構造 cluster #2 解除 — FPF index bounds (hc2/hFPF) landed

**開始時定型**: hub の S08_CoherenceCore 3-way split (issue 0066, b7e672de) を main から取込 (merge
`b47dfe78`, full build 3807 緑 + AxiomsCheck OK; b-peterfalvi の session-40 frontier とは disjoint)。

**✅ landed (build-green + axiom-clean, commit `9aa66fdd`, S08_CaseBCoherence2)**:
22. **`certainType_index_bounds` = 構造 discharge #2: FPF index bounds**。
    (4.2) Hypothesis + math-B (W₂⊆Z(K)) ⟹ **商 ↥L/W₂ が Frobenius 群** (kernel K/W₂, complement
    W₁W₂/W₂) ⟹ Isaacs Lemma 6.1 `card_kernel_modEq_one` で |K:W₂| ≡ 1 (mod |W₁|) ⟹ |W₁|<|K:W₂|。
    出力 = `exists_decomposition_caseB` の deferred 2 入力:
    - `hc2 : 2 ≤ (W₂.subgroupOf K).index` (W₂⊊K = ¬K≤W₂ から)
    - `hFPF : (W₂.index:ℤ) < ((W₂.subgroupOf K).index:ℤ)^2` (|L:W₂|=|K:W₂|·|W₁| via relIndex_mul_index
      + index_eq_card; |W₁|<|K:W₂|)。
    🔑 鍵 API (再調査不要): `OddOrder.BG.Ch1.S03.isFrobeniusGroup_iff_complement_centralizer_inf_kernel_eq_bot`
    (元群が Frobenius でなくても商上に直接構成可、IsFrobeniusGroup 不要)、`fixedPoint_lift_of_generator_quotient_fixed`
    (IsFrobeniusGroup 不要、hNK+coprime+solvable のみ; solvable は zpowers x cyclic で Or.inl 無料)、
    centralizer 条件は q̄∈K.map から y∈K 直得ゆえ W₁ abelian 不要。card 変換 = `quotientKerEquivRange`
    + `quotientBot` + `IsComplement'.symm.index_eq_card`。S08_CaseBCoherence2 は 193→344 行。

### ⚠ 構造 cluster 残 = #1 のみ:
- **math-B X-irreducibility (`isIrreducibleCharacter_of_mem_Xset_caseA` の math-B 版)**: case-A 版
  `isIrreducibleCharacter_of_mem_Xset_caseA` (S08_CoherenceCorePart2:1860) は FPF-generic (centralizer
  条件 param)。math-B (W₂⊆Z(H)) でこの generic に渡す centralizer 入力を作る。inertia 計算。中規模。
### 🟡 character-theoretic 残: (6.8.2.3) (χ∈X, X-irred #1 要) → τ₂ assembly (大) → §7 glue (generic) → capstone。
**正本=本 session 40 cont.¹³。構造 #3(W₂⊆Z)+#2(FPF bounds) ✅。残=#1 X-irred + (6.8.2.3) + τ₂ + glue。**

## 2026-06-14 (session 40 cont.¹⁴, /loop): 🚨 RECON 訂正 — 「#1 math-B X-irreducibility」は **case B で偽**

**この iteration = RECON (Lean brick なし、roadmap 訂正)**。cont.¹¹–¹³ が残してきた構造 cluster #1
「math-B X-irreducibility (`isIrreducibleCharacter_of_mem_Xset_caseA` の math-B 版, X⊆Irr L)」を
教科書 (6.8) 精読 (mmd 04.8 L136-224) で精査した結果、**case B では X⊄Irr L であり #1 は数学的に偽**。

### 🔑 教科書 (6.8) の case 構造 (L136-160):
- case (A): Z = Z(H)∩H′; case (B): **Z = W₂**。X = S − S(Z), Y = S(H′)。
- (6.8.1) の「X⊆Irr L」証明は **case-A 専用** (「Z∩W₂=1 ゆえ |C_H(x)|=|C_{H/Z}(x)|」を使う)。

### 🚨 case B で X⊄Irr L の証明 (厳密、私の `certainType_index_bounds` に依拠):
1. **L/W₂ は Frobenius 群** (kernel H/W₂) — `certainType_index_bounds` の `hFrob` で証明済み。
2. Frobenius 群の S-set (kernel から induce した非自明既約) は **全て既約** (Thm 6.34 = (c1) と同型)。
3. S(W₂) = {χ∈S | W₂⊆Ker χ} = L/W₂ の S-set ⟹ **S(W₂) は reducible 0 個**。
4. 一方 S は (4.5)/(c2) で **w₂−1 個の reducible μ_j** を持つ。
5. ∴ X = S − S(W₂) は w₂−1 個の reducible を**全て**含む ⟹ **X⊄Irr L**。
   (case A は Z∩W₂=1 ゆえ S(Z) も w₂−1 reducible を持ち X が reducible-free になる; case B は L/W₂ で
   W₂-defect が消え Frobenius 化するため S(W₂) が reducible 0 になり、対照的に X に全 reducible が残る。)
- ⚠ repo コメント `S08_CoherenceCorePart2:3346` 「X-irreducibility valid in case B」は**誤り** (旧 plan の残骸)。
  最近の `exists_decomposition_caseB` (cY witness + norm 経路 = (6.8.2.2) elementary) は X-irred を**使っていない**
  ので、#1 は実際の case-B 経路では不要 (古い「generic _caseA reuse」plan の遺物)。

### ✅ (4.9) は available — reducible μ_j を扱う機構は完成済:
- **`S06_CertainTypeCoherence.certainType_isCoherent` (:505) = (4.9)(b) coherent isometry (0-sorry)**、
  `S06_CertainTypeConjugation` (4.9a, μ̄_j=μ_{j′}) も 0-sorry。これが教科書 (6.8.2.3) の reducible χ_i=μ_j
  に対する **R(μ_j) certain-type reflection** ((5.3.b) 引用先) を供給する。session-29 RECON と一致。

### ▶▶ 訂正後の case-B 残作業 (構造 cluster は #2(FPF)+#3(W₂⊆Z) で **完了**、#1 は削除):
1. **(6.8.2.3)** (χ∈X 版 `(χ−aη₁)^τ = X₁ − aY`): 教科書 = [Is]2.27 で χ=Ind^L_Hθ を Ind^L_{W₂}φ に帰着
   (Z=W₂⊆Z(H))、`Ind^L_Zφ−|H:Z|η₁ = Σa_iα_i` (Σa_i²=|H:Z|)、各 α_i に R(χ_i) ((5.4.a) ‖X_i‖²≥‖χ_i‖²)。
   **irreducible χ_i = §7 R-producer; reducible χ_i=μ_j = (4.9) `certainType_isCoherent`。** 私の
   `exists_decomposition_caseB` ((6.8.2.2)) が aggregate side を供給。
2. **τ₂ assembly** ((6.8.2) proof, L224): Z-linear τ₂ on Z[X∪Y], τ on Z[X∪Y,L^#] と一致、η₁^{τ₂}=Y。
3. **§7 glue + capstone** (`sibleySetup_is_coherent` の case-B branch)。
**正本=本 session 40 cont.¹⁴。#1 は偽ゆえ削除。残=(6.8.2.3)[(4.9) available]+τ₂+glue。次手=(6.8.2.3)。**

## 2026-06-14 (session 40 cont.¹⁵, /loop): 🗺 (6.8.2.3)+τ₂ = case-B X∪Y coherence の concrete PLAN

cont.¹⁴ RECON で #1(X-irred) が偽と確定 ⟹ case-B の残り = **(6.8.2.3) + τ₂ assembly + glue** の大規模
assembly。教科書 (6.8.2.3) 完全証明 (mmd 04.8 L208-224) + Frobenius テンプレート
(`coherentXunionYset_centralCommutator_of_glued_of_frobenius` S08_CoherenceCore:1316,
§7 `coherentUnion_of_glued`) を精読して brick 分解を確定。

### 🔑 全体像 (Frobenius `..._of_frobenius` を mirror、ただし X に reducible μ_j):
case-B X∪Y coherence = **X-coherence ⊕ Y-coherence を §7 glue**。Frobenius と違い X が reducible を含む:
- **Y-coherence**: 済 (Y=S(H′), 全 deg|W₁|, (1.1)+(1.4))。
- **X-coherence (NEW, reducible 含む)**: X = S−S(W₂) = irreducible 部 ∪ reducible μ_j 部 (w₂−1 個)。
  - irreducible 部: (6.6) reuse (`Xset_..._isCoherent_of_irreducible_X` 系) — ただし X 全体が irreducible
    でないので、generic を **irreducible sub-family** に適用する形に要調整。
  - **reducible μ_j 部**: (4.9) `S06.certainType_isCoherent` (`certainTypeSet h k`, S06_CertainTypeCoherence:505)。
  - 両者を §7 `coherentUnion_of_glued` で glue。
- **(6.8.2.3) agreement** ((χ−aη₁)^τ = X₁−aY, χ∈X): 各 χ_i に R(χ_i) + (5.4.a)/(5.4.b) (S07_Coherence:1378/1447)
  + 集約 pinning (b_i=a_i, (6.8.2.2)=`exists_decomposition_caseB` を消費)。irreducible χ_i=§7 R-producer
  (`dadeOrthonormalCharacterImageFamilyOfDiff`); reducible μ_j=(4.9)。
- **X∪Y glue**: §7 `coherentUnion_of_glued_of_generator_mixed_inner_eq`、mixed-inner 入力 = (6.8.2.3)。

### 🔴 crux brick = (4.9)→§7 R/coherence bridge:
`certainType_isCoherent : S07.IsCoherent (dadeIntegralCharacterMap h.dade0 h.tau) (certainTypeSet h k) ...`
を、(a) case-B X-coherence の reducible 部 (`coherentUnion_of_glued` に渡す `IsCoherent`)、(b) (6.8.2.3) の
reducible χ_i の R(μ_j) (`OrthonormalCharacterImageFamily`) として接続。**dade0/tau の整合 (cert↔hyp bridge
`cert.K=H` S08_CoherenceCore:1261) と certainTypeSet↔Xset の対応が要精査** = 次の最大の未知。

### 📋 brick 順 (次イテレーションから build):
1. **集約関係** `Ind^L_{W₂}φ − |H:W₂|η₁ = Σ a_iα_i` + `Σa_i²=|H:W₂|` (= ‖Ind^H_{W₂}φ‖²; 中心部分群
   への Res∘Ind=|H:W₂|·φ + Frobenius 相互律)。non-wrapper character identity。最自己完結。
2. **(4.9)→R bridge** (crux): cert↔hyp + certainTypeSet↔(X の reducible μ_j) + dade0↔tau 整合。
3. **(6.8.2.3) per-χ**: (5.4.a/b) + R(χ_i) + pinning。
4. **X-coherence (reducible 込み)** + **X∪Y glue** → `sibleySetup_is_coherent` case-B branch。
**正本=本 cont.¹⁵。これは大規模 assembly (複数イテレーション); crux=(4.9)→§7 bridge。次=brick 1 (集約関係)。**

## 2026-06-14 (session 40 cont.¹⁶, /loop): 🗺 case-B coherence アーキテクチャ確定 (mirror-Frobenius) + crux feasible

cont.¹⁵ の PLAN を精査確定。case-B X∪Y coherence = **Frobenius assembly
`coherentXunionYset_centralCommutator_of_glued_of_frobenius` (S08_CoherenceCore:1316, ~30行) を mirror**。
本体は §7 `coherentUnion_of_glued_of_generator_mixed_inner_eq` への clean call:
X-coherence + Y-coherence (`coherentYset` 済) + ν (glue map, param) + hagreeX/Y + 直交性 + hmixed + hgen。

### 🔑 case-B が Frobenius と違う 4 点 (= 残 brick):
- **(A) Dade-data 一致 [crux, feasible]**: (4.9) `certainType_isCoherent` は `dadeIntegralCharacterMap
  h.dade0 h.tau` (Hypothesis46) で、`hyp.tau` (SibleyDade) と別 datum。だが **両者 H#-supported 上で一致**
  — `dadeIntegralCharacterMap_apply_of_support` で両方 dadeMap=Ind_L^G に帰着 (μ_j は `columnSum_support_subset`
  で H#∪{1} 上 support, `dade_H_eq_bot`)。⟹ feasible (both=Ind)。
- **(B) case-B X-coherence [substantive, 大]**: X = S−S(W₂) = X_irr ∪ {μ_j} (cont.¹⁴: μ_j は reducible で X に在)。
  X_irr=既約 (6.6 reuse), {μ_j}=`certainTypeSet`=(4.9) `certainType_isCoherent`。両者を §7 `coherentUnion_of_glued`
  で glue (要 (A) で hyp.tau へ transport)。**これが最大の新規ピース。**
- **(C) X⊥Y 直交 (reducible-aware)**: Frobenius は `inner_eq_zero_of_mem_span_of_disjoint_irreducible` (X 既約前提)。
  case-B は μ_j=Σ_i μ_{ij} (各既約∈X) ⊥ η_k (∈Y) を μ_{ij}∉Y から。要 reducible 対応版。
- **(D) hmixed (=(6.8.2.3)) + glue**: ν が ⟨x,y⟩ 保存 (x∈X[reducible 含む], y∈Y)。τ-isometry on supported + (A)(B)。

### ⚠ brick 1 (`inner_induce_self_eq_index_of_le_center`, Σaᵢ²=|H:Z|) の位置付け:
教科書 (6.8.2.3) の R(χ_i) pinning 用だったが、**mirror-glue 経路では off-path の可能性**。true lemma で害なし、
(6.8.2.3) を per-χ で行う場合は再利用可ゆえ残置。アーキテクチャ未確定で先に建てた反省。

### ▶ 次手 = brick (B) case-B X-coherence の構築開始 ((A) support-agreement を補題化 → (4.9) を hyp.tau へ
transport → X_irr と glue)。**正直な評価: case-B coherence は大規模 multi-session assembly。crux は全て
feasible と確認済 (構造的ブロッカー無し)、残りは intricate な interface 接続を brick ごとに積む段階。**
**正本=本 cont.¹⁶ (アーキテクチャ確定版; ¹⁵ の不確定を解消)。**

## 2026-06-14 (session 40 cont.¹⁷, /loop): ✅ feasibility 完成 — 全ツール確認、残=wiring assembly。機構 brick (A)(C) landed

cont.¹⁶ で残した crux「(4.9) は enlarged `h46.dade0` (A₀=A∪Vᴸ) の map で coherence、hyp.tau は base
`h46.dade`(=hyp.dade, A) の map」の解決法を確認:
- **§4 `Hypothesis.restrict` (S04:329) + `dadeMap_restrict` (S04:3641)** = enlargement 互換性ツール
  (A₁⊆A の datum 制限 + 制限 map は A₁-supported で原 map と一致)。`cases` は `h46.dade = dade` を与える
  (S08_CoherenceCorePart1:3324) ので、dade0 を A に restrict した map ↔ hyp.tau の橋は §4 restrict で。

### ✅ landed (iter 5-6, 機構 brick):
- **brick (A) `S07.IsCoherent.congrMap`** (commit 30c74961): coherence を supported 上一致する別 map へ transport。
- **brick (C) `inner_eq_zero_of_mem_span_of_pairwise_orthogonal`** (commit 10c99216): reducible-aware X⊥Y。
- (foundations: `exists_decomposition_caseB` (6.8.2.2)、`certainType_index_bounds` (FPF)、`certainType_W2_le_center`、
  brick 1 `inner_induce_self_eq_index`、(4.9) `certainType_isCoherent`、(6.6)、§7 `coherentUnion_of_glued`)。

### ✅ 構造的ブロッカー無しを最終確認。残 = wiring assembly (大、multi-level、要 full case-B context):
1. **map-agreement** (§4 restrict で dade0-map↔hyp.tau on A-supported) → congrMap で (4.9) {μ_j}-coh を hyp.tau へ。
2. **X-coherence glue**: X_irr-coh (6.6 reuse) + {μ_j}-coh (1.) を §7 coherentUnion で glue (要 X_irr⊥{μ_j} mixed-inner)。
3. **X∪Y glue**: X-coh + Y-coh (coherentYset) を coherentUnion_of_glued_of_generator_mixed_inner_eq で
   (brick C で reducible X⊥Y、ν=(6.8.2.3) mixed-inner)。
4. **CoherenceTarget 変換** → capstone `sibleySetup_is_coherent` の X-nonempty/CertainType 分岐。
**honest 状況: 基礎機構は完成、残りは full case-B hypothesis context での multi-level wiring assembly (大)。
unblocked だが per-iteration は wiring piece 単位で、capstone 完遂は distant。正本=本 cont.¹⁷。**

## 2026-06-14 (session 40 cont.¹⁸, /loop): ✅ 機構完成 (5 bricks) + 🛑 X-coherence route は要集中設計 (irreducible-X engine 非一般化)

### ✅ landed (iter 5,6,8): case-B coherence の reusable 機構 全完成 (全 axiom-clean):
- `IsCoherent.congrMap` (30c74961): coherence を supported 上一致 map へ transport。
- `inner_eq_zero_of_mem_span_of_pairwise_orthogonal` (10c99216): reducible-aware X⊥Y。
- `dadeIntegralCharacterMap_restrict_eq_of_support` (6cfa8c32): restrict-invariance = map-agreement 核。
- (+ foundations: exists_decomposition_caseB / certain_index_bounds(FPF) / W2_le_center / brick1 / (4.9) / §7 engine)。

### 🛑 残 X-coherence route の architectural 障害 (本 iter 判明):
- 既存 irreducible-X engine `Xset_isCoherent_from_adjoinSteps_of_irreducible_X` (S08_CoherenceCorePart2:4232) は
  **irreducibility に深く依存** (`χs:ℕ→IrreducibleCharacter`, `exists_conjugatePairCover`, conjugate-pair cover,
  xBaseBlock)。case-B X=S−S(W₂) は reducible μ_j を含む (cont.¹⁴) ので **この engine は再利用不可**。
- ∴ case-B X-coherence は新規設計が必要: (a) X_irr (既約部) を engine で + {μ_j} を (4.9) で別々に build し §7
  `coherentUnion_of_glued_withDiagonal` で glue (但し X_irr は clean な `Xset Z` でない問題), or (b) 教科書 uniform
  R(χ)/(5.4) route (全 χ∈X を R(χ) 経由; reducible μ_j は (4.9)=R(μ_j); §7 (5.4) machinery 接続要)。
- さらに残: X∪Y glue (withDiagonal, hDτ=(6.8.2.3)) + CoherenceTarget 変換 + dade0/dade wiring fact
  (Hypothesis46 は dade0↔dade 関係を abstract に持たない=top-level 構築事実、restrict-invariance で map-agreement 化)。

### 🔑 honest 総括: case-B coherence の clean reusable 機構は完成 (5 bricks)。残りは **full case-B context での
集中 architectural 設計+build** (X-coherence route 決定 + multi-level glue + CoherenceTarget)。60s loop brick 単位
でなく、full context を保持した dedicated session が適切。**正本=本 cont.¹⁸。次手 = X-coherence route 決定 (uniform R
vs glue) → 構築。**

## 2026-06-14 (session 40 cont.¹⁹, /loop): ✅ cX feasibility 解決 (xChainCoherent generic) + X∪Y shell landed

### ✅ landed (iter 9-10): X∪Y assembly shell + ユーザー裁可で継続
- **`coherentXunionYset_caseB_of_glued`** (8f451fd8): case-B X∪Y coherence (Frobenius 版の case-B mirror)。
  §7 `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` + **brick C** (reducible-aware 直交性)。
  hoisted = cX(X-coh) + ν(τ₂) + hmixed((6.8.2.3)) + D/hDτ(cross-diagonal) [全 capstone-wiring inputs]。

### ✅ cX (case-B X-coherence on Xset W₂, hard core) は feasible と確認:
- 最大の未解決 = 「Xset W₂ は reducible μ_j を含むので既存 irreducible-X engine 不可」だったが、
  **内部 engine `xChainCoherent` (S08_CoherenceCorePart1:2701) は generic な既約集合 X を取る** (Xset 専用でない;
  `{X S₀ : Set}` + conjugate-pair cover `pair/χs` + base coherence + per-step inputs)。
- X_irr (= Xset W₂ の既約部 = X−{μ_j}) は **conj-closed** (W₂ 中心ゆえ Xset W₂ conj-closed; μ̄_j=μ_{j'} (4.9a)
  ゆえ {μ_j} conj-closed; 差も conj-closed) + odd-order ゆえ no-real-char ⟹ **xChainCoherent 適用可**。
- ∴ **cX 構築プラン (feasible, 構造的ブロッカー無し)**:
  1. **X_irr-coh**: `xChainCoherent` on X_irr (conjugate-pair cover + base S₀ + per-step (5.6)/degree-div inputs
     = (6.6) machinery を X_irr へ適応; 既存は Xset 専用ゆえ adapt 要)。
  2. **{μ_j}-coh**: (4.9) `certainType_isCoherent` (h46) + `congrMap` (map-agreement = restrict-invariance +
     wiring fact dade0.restrict=hyp.dade)。instance plumbing 要 (NeZero/Fintype/Invertible ×6)。
  3. **Xset W₂ = X_irr ∪ {μ_j}** 集合分解 (要 columnSum=μ_j∈X + W₂⊄Ker; cert↔hyp bridge h46.K=H)。
  4. **glue** (1)+(2) via §7 `coherentUnion_of_glued` (mixed-inner X_irr↔μ_j) → cX。

### 🔑 honest 総括: scaffolding 完成 (6 bricks + X∪Y shell)。cX は **feasible な hard core** で、X_irr の
(6.6) machinery 適応 + {μ_j} の (4.9)接続 + 分解 + glue の集中 assembly。次手 = cX の piece を順次 build
({μ_j}-coh or X_irr-coh の adapt から)。**正本=本 cont.¹⁹。cX feasibility 確定が本 iter の主成果。**

## 2026-06-14 (session 40 cont.²⁰, /loop): cX reducible 側 ({μ_j}-coh) landed; 残 cX content = 深い §6 math (precise hooks)

### ✅ landed (iter 11): **`certainTypeSet_isCoherent_tau`** (94fa65e7) = cX の reducible 側。
(4.9) `certainType_isCoherent` + `congrMap` で {μ_j}-coh を hyp.tau へ (map-agreement は wiring 供給)。
S06_CertainTypeCoherence を S08 へ import (cX に必須)。

### 🔴 残 cX content = 3 つの深い §6-internal piece (各々 substantial, precise hooks):
1. **X_irr-coh** (cX irreducible 側): `xChainCoherent` (generic engine, S08_CoherenceCorePart1:2701) を
   X_irr := {χ∈Xset W₂ | irreducible} に適用。要 = conjugate-pair cover (`exists_conjugatePairCover`,
   X_irr は conj-closed+no-real-char で適用可) + base S₀ coherence ((1.1)(1.4)) + **per-step XAdjoinStepInput
   ((5.6) degree-div data; Xset 専用機構を X_irr へ adapt が hard core)**。
2. **{μ_j} = certainTypeSet ⊆ Xset W₂** (set 構造): `columnSum h46 χ₂ = induce h46.K (chiRestrict χ₂)`
   (S06_CertainTypeCoherence:253-255 hbridge) + `chiRestrict χ₂ : IrreducibleCharacter ↥h46.K`
   (S06_CertainTypeClifford:772) ⟹ columnSum∈S (要 **↥h46.K↔↥H bridge coercion** via h46.K=H) +
   **¬W₂⊆Ker columnSum** (kernel fact, 要発掘) → `mem_Xset` (Part2:803)。
3. **(6.8.2.3) ν / mixed-inner** (glue の ν): per-χ τ-decomposition `(χ−aη₁)^τ = X₁−aY` ([Is]2.27 +
   exists_decomposition_caseB を χ_i で集約)。glue の hmixed/hDτ/ν を供給。

### 🔑 honest 総括: reusable foundation (7 bricks: FPF/brick1/congrMap/pairwise-orth/restrict-invariance/
X∪Y shell/{μ_j}-coh) 完成。残り cX content (上記 1-3) は **深い (6.8.2) case-B math** で §6 internals に密結合;
shell の積み増しは scaffold-tower ゆえ避け、genuine content を順次 build (要集中, loop brick より大)。
次手 = (1) X_irr-coh の cover/base か (2) {μ_j}⊆X membership の bridge から着手。**正本=本 cont.²⁰。**

## 2026-06-14 (session 40 cont.²¹, /loop): item-2 membership 精密分解 — 真の infra-blocker = K↔H cross-group transport; (2b) Clifford-uniq 論法確定

cont.²⁰ item 2 ({μ_j}⊆Xset W₂ membership) を精査。S-membership 核入力を 1 本 landing + 残りの
構造を完全に確定 (次セッションが transport infra を 1 本建てれば組立可)。

### ✅ landed (iter 12): `chiRestrict_ne_trivialIrreducibleCharacter` (a372410b, S06_CertainTypeSupport, axiom-clean)
χ_j = Res_K μ_{0j} は χ₂≠1 で**非自明既約** (trivial なら ker=univ⊇H.subgroupOf K が
`not_subset_characterKernel_chiRestrict` に矛盾)。6 行。`not_subset_…` の直後に配置。

### 🔬 item 2 (`certainTypeSet h46 k ⊆ hyp.Xset h46.W2`) の精密分解:
`mem_Xset` (Part2:803): φ∈Xset W₂ ↔ φ∈S ∧ φ∉S(W₂)。各 μ_j=`columnSum h46 χ₂`:
- **(2a) columnSum ∈ hyp.S** (`S_eq`: ∃θ:Irr ↥H, θ≠triv ∧ columnSum=induce H θ):
  - hbridge (`S06_CertainTypeCoherence`:253): columnSum = induce h46.K (chiRestrict χ₂),
    `chiRestrict χ₂ : Irr ↥h46.K`。h46.K=H (cases c2)。
  - θ := chiRestrict χ₂ を **h46.K=H で ↥H へ transport** して供給。θ≠triv = 本 commit を transport。
- **(2b) columnSum ∉ hyp.SsubFiltration W₂**
  (¬∃θ:Irr ↥H, θ≠triv ∧ W₂.subgroupOf H⊆ker θ ∧ columnSum=induce H θ):
  - **Clifford-uniqueness 論法 (確定)**: columnSum=induce H θ ⟹ θ=chiRestrict。
    Res_H columnSum = ∑_i Res_H μ_{ij} = w₁•chiRestrict
    (`restrict_certainType_eq` χ₂ i: Res_K μ_{ij}=Res_K μ_{0j}=chiRestrict + columnSum=∑μ_{ij});
    Frobenius (`inner_induce_eq_inner_restrict`) ⟨θ,Res_H columnSum⟩=⟨induce θ,columnSum⟩
    =⟨columnSum,columnSum⟩≠0 (columnSum(1)=∑deg>0 ⟹ columnSum≠0 ⟹ ‖·‖²≠0);
    ⟨θ,w₁•chiRestrict⟩=w₁⟨θ,chiRestrict⟩≠0 ⟹ θ=chiRestrict (両既約)。
    すると W₂.subgroupOf H⊆ker chiRestrict が `not_subset_characterKernel_chiRestrict` に矛盾。

### 🔴 真の infra-blocker = **↥h46.K ≃ ↥H (`Subgroup.equivOfEq`) に沿った IrreducibleCharacter / induce / 既約性の cross-group transport が未整備**:
- 既存 transport は**同群内のみ** (`ClassFunction.conjByMulEquiv` = G→G 自己同型)。cross-group
  ↥K→↥H の ClassFunction precompose-along-MulEquiv + induce-invariance + irreducibility-invariance
  が repo/mathlib に無い (grep 確認済)。`induce_congr_of_subgroup_eq` (S04:1367) は induce **等式**
  は与えるが、∃θ:Irr ↥H の **θ 自体**を作れない。
- ⟹ 次セッションは **まず transport infra を 1 本建てる**:
  例 `IrreducibleCharacter.mapOfSubgroupEq (hKH:K=H) : IrreducibleCharacter ↥K ≃ IrreducibleCharacter ↥H`
  + `induce_mapOfSubgroupEq : induce H (mapOfSubgroupEq hKH θ) = induce K θ`
  + `mapOfSubgroupEq_ne_trivial`。これで (2a)θ構築 + (2b)θ=chiRestrict同定 + chiRestrict_ne_trivial
  transport が全部通る。
- **代替案 (要実験)**: θ:=`restrict H μ_{0j}` を直接構築し `rw [hHK]` で既約性 (`certainTypeRestrict_isIrreducible`)
  / 非自明性を ↥h46.K→↥H 移送。motive = `fun (S:Subgroup ↥L) => IsIrreducibleCharacter (restrict S μ_{0j})`
  は S が subgroup 引数のみで clean ゆえ dependent rewrite が通る可能性あり (試して可なら infra 不要で最速)。

### 次手 = transport infra (or 代替の rw 実験) → (2a)+(2b) 組立 (`certainTypeSet_subset_Xset` を
S08_CaseBCoherence2 に) → cX 残 (item 1 X_irr-coh の cover/base + item 3 (6.8.2.3) mixed-inner)。
**正本=本 cont.²¹。item 2 は構造完全確定、残るは transport infra 1 本の実装。**

## 2026-06-14 (session 40 cont.²², /loop): ✅ item 2a (μ_j∈S) landed — K↔H transport は infra 不要 (rw[hHK] で安価); 残 = 2b Clifford-uniq

cont.²¹ で「transport infra 1 本要」と判定したが、**実験で否定**: K↔H cross-group transport は
専用 infra 不要、既存ツールで安価に通った。

### ✅ landed (iter 13-14):
- `chiRestrict_ne_trivialIrreducibleCharacter` (a372410b, S06_CertainTypeSupport): χ_j 非自明 (=2a 核入力)。
- **`SibleyDadeHypothesis.columnSum_mem_S`** (56ef5f0c, S08_CaseBCoherence2): **μ_j ∈ hyp.S (item 2a 完了)**。

### 🔑 K↔H transport は安価 (cont.²¹ の infra-blocker 判定は誤り):
- **既約性**: `have h := h46.certainTypeRestrict_isIrreducible χ₂; rwa [hHK] at h` — `rw [hHK]` が
  `IsIrreducibleCharacter (restrict h46.K μ)` → `(restrict H μ)` を**そのまま通す** (motive=fun S↦Prop で OK)。
- **induction**: `induce_congr_of_subgroup_eq` (= `…S04.Hypothesis.induce_congr_of_subgroup_eq`,
  full name 注意) で `induce h46.K (restrict h46.K μ) = induce H (restrict H μ)` (値一致は
  `simp [restrict_apply]`)。
- **非自明性**: `rw [← hHK] at h1` は **motive 不成立で失敗** (equation 型 CF↥H が S 依存)。代わりに
  `ClassFunction.ext` + 各点 `congrArg (f ↦ f ⟨↑g,hg⟩) h1` + `simpa` で値レベル transport。
  membership transport は `hHK.le g.2` (`▸` は motive 曖昧で失敗)。
- θ:Irr ↥H は `⟨restrict H μ_{0j}, hirr⟩` を anonymous constructor で直接供給 (set 不要、.1 は rfl)。

### ▶▶ 残 item 2 = **2b `columnSum ∉ hyp.SsubFiltration W₂`** (Clifford-uniqueness):
φ∈S(W₂) ⟹ ∃θ:Irr↥H, θ≠triv ∧ W₂.subgroupOf H⊆ker θ ∧ columnSum=induce H θ。矛盾を:
1. **Res_H columnSum = w₁•(restrict H μ_{0j})**: columnSum=∑_i μ_{ij} ⟹ Res_H=∑_i restrict H μ_{ij};
   各 restrict H μ_{ij}=restrict H μ_{0j} (`restrict_certainType_eq` χ₂ i は K 版 → 各点 ext で H 版へ)。
2. **Frobenius** (`inner_induce_eq_inner_restrict`): ⟨θ,Res_H columnSum⟩=⟨induce H θ,columnSum⟩
   =⟨columnSum,columnSum⟩≠0 (columnSum(1)=∑deg>0 ⟹ inner_self≠0)。
3. ⟨θ,w₁•restrict H μ_{0j}⟩=w₁⟨θ,restrict H μ_{0j}⟩≠0 ⟹ θ=restrict-H-版 (両既約, `irreducibleCharacter_inner_eq_ite`)。
4. すると W₂.subgroupOf H⊆ker(restrict H μ_{0j}) を各点 ext で K 版へ transport ⟹
   W₂.subgroupOf h46.K⊆ker chiRestrict が `not_subset_characterKernel_chiRestrict` に矛盾。
→ 2b 完了で **`certainTypeSet_subset_Xset` assembly** (各 μ_j=columnSum を 2a∧2b で mem_Xset) →
cX の残 (item 1 X_irr-coh + item 3 mixed-inner)。
**正本=本 cont.²². item 2a 完了; 2b は上記 4 段 (中規模); transport 安価が判明し item 2 全体が現実的。**

## 2026-06-14 (session 40 cont.²³, /loop): ✅✅ item 2 COMPLETE (`certainTypeSet ⊆ Xset W₂`); 残 cX = item 1 (X_irr-coh) + item 3 (mixed-inner)

### ✅✅ landed (iter 15, commit e9252215, S08_CaseBCoherence2, 全 axiom-clean, full build 3807):
4 補題で **item 2 (𝒯 ⊆ X(W₂)) 完了**:
- `columnSum_eq_induce_H` — μ_j = Ind_H^L(Res_H μ_{0j}) (transported (4.5.a))。
- `restrict_H_certainType_eq` — Res_H μ_{ij}=Res_H μ_{0j} ((4.8)step1 の H 版)。
- **`columnSum_notMem_SsubFiltration`** (2b) — μ_j∉S(W₂), Clifford-uniqueness:
  **double-Frobenius** で ⟨μ_j,μ_j⟩ を相殺 (μ_j≠0/正定値 補題 不要が鍵)。各 inducing θ で
  w₁⟨θ,ψ⟩=⟨μ_j,μ_j⟩=w₁⟨ψ,ψ⟩ ⟹ ⟨θ,ψ⟩=⟨ψ,ψ⟩≠0 ⟹ θ=ψ ⟹ W₂⊆Ker ψ が (4.7) に矛盾。
- **`certainTypeSet_subset_Xset`** (assembly) — 𝒯⊆X(W₂), `mem_Xset ⟨2a,2b⟩`。

### 🔑 2b 実装の知見 (再利用):
- `classical` を proof 冒頭に (ite の `Decidable (θ=ψirr)` 用)。
- θ=ψirr は `if`-rw 連鎖でなく e0(⟨θ,ψirr⟩=0)/e1(⟨ψirr,ψirr⟩=1)+`rw[show ↑ψirr=ψ from rfl]`+
  `rw[hinner]`+`zero_ne_one` で (ψ vs ↑ψirr の syntactic mismatch 回避)。
- `inner_induce_eq_inner_restrict` (Frobenius) は `ClassFunction.` prefix。
- 最終 kernel transport: `Hypothesis.coe_chiRestrict`+`restrict_apply`+`OneMemClass.coe_one` を
  `simp only ... at hxker ⊢` で両辺正規化 → `exact hxker`。

### ▶▶ 残 cX content = 2 piece (cont.²⁰ item 1, 3; ともに深い §6 math):
1. **item 1 X_irr-coh** (cX irreducible 側, **最難**): `xChainCoherent` (generic engine,
   S08_CoherenceCorePart1:2701) を X_irr:={χ∈Xset W₂|irreducible} に適用。conjugate-pair cover
   (X_irr conj-closed+no-real-char で可) + base S₀ ((1.1)(1.4)) + **per-step XAdjoinStepInput
   ((5.6) degree-div; Xset 専用機構を X_irr へ adapt が hard core)**。
   + **Xset W₂ = X_irr ⊔ certainTypeSet 分解の reverse** (Xset の reducible 元は全て μ_j; (4.5b) exhaustion)。
2. **item 3 (6.8.2.3) mixed-inner**: per-χ τ-decomposition `(χ−aη₁)^τ=X₁−aY`。glue の hmixed/hDτ/ν 供給。
→ glue: X_irr-coh + {μ_j}-coh (`certainTypeSet_isCoherent_tau` cont.²⁰) を §7 coherentUnion →
cX → `coherentXunionYset_caseB_of_glued` (cont.¹⁹ shell) → capstone case-B branch。
**正本=本 cont.²³. item 2 完了 (2 iter); 残 item 1/3 は深く要集中。次=item 1 の set 分解 reverse
(`Xset W₂ ⊆ X_irr ∪ certainTypeSet`, (4.5b) exhaustion) から着手が自然 (item 1 の前段、tractable)。**

## 2026-06-14 (session 40 cont.²⁴, /loop): 🚨🚨 ARCHITECTURE RECON — 教科書 (6.8.2) は **直接 τ₂ 構成** (anchor η₁∈Y); 「standalone case-B X-coherence (cX) + glue」plan は教科書と乖離 → item 1 (X_irr-coh) は不要/誤方向

cont.²³ で「次=item 1 (X_irr-coh) の set 分解」と書いたが、着手前に **mmd 04.8 L178-224 ((6.8.2) 全証明) を精読**して
重大な方針乖離を発見。cont.¹⁴-²³ の glue route (cX を別途構築して §7 で glue) は**教科書の証明構造と異なる**。

### 🔑 教科書 (6.8.2) case-B の実際の証明構造 (mmd 04.8 L224 "Proof of (6.8.2)"):
> τ₂ := Z[X∪Y]→Z[Irr G] の Z-linear map で、Z[X∪Y,L^#] 上 τ と一致、かつ **η₁^{τ₂}=Y** (Y=η₁^{τ₁}, m=2 で −η₂^{τ₁})。
> (6.8.2.3) で ⟨(χ−aη₁)^τ, η₁^{τ₂}⟩=⟨χ−aη₁,η₁⟩ (χ∈X, a=χ(1)/η₁(1))。η∈Y も同様。
> ⟹ τ₂ は Z[X∪Y,L^#]∪{η₁} (= Z[X∪Y] を生成) 上で内積保存 ⟹ X∪Y coherent。

つまり: **τ₂ は X∪Y 全体に直接定義** (χ−aη₁ は supported ゆえ χ=(χ−aη₁)+aη₁ で生成; τ₂(χ)=τ(χ−aη₁)+aY=X₁)。
**standalone な「X だけの coherence (cX)」は構築しない** — (6.8.2.3) の χ-分解は **η₁∈Y を anchor**に使うので、
X-coherence は Y から切り離せない。case (A) は X⊂Irr L で X-内部 anchor の (6.6) が効く (L160) が、**case (B) は
X が reducible μ_j を含み X-内部 chain が崩れるため、教科書は Y-anchor の直接 τ₂ に切り替えている**。

### 🛑 ⟹ cont.¹⁹/²⁰ の plan (cX = X_irr-coh ∪ {μ_j}-coh を §7 glue) は誤方向:
- `coherentXunionYset_caseB_of_glued` (cont.¹⁹ shell) は **cX (standalone X-coherence) を入力に要求**するが、
  case-B では cX は教科書の対象でなく、構築には Y-anchor η₁ が要る (循環)。cont.¹⁸ が「irreducible-X engine
  再利用不可」「case-B X-coherence は新規設計が必要」で詰まったのは**この乖離が原因** (square peg/round hole)。
- item 1 (X_irr-coh via xChainCoherent) は **不要**。xChainCoherent は IrreducibleCharacter pair を足すので
  reducible μ_j を足せず、かつ X-内部 base を要求 (Y-anchor でない)。
- 副次: certainTypeSet の degree 条件 (equal-degree のみ) も問題で、Xset∖certainTypeSet は all-irreducible でない
  (異 degree の reducible μ_j が残る) — これも glue route が破綻する別証左。

### ✅ 正しい route = **直接 τ₂** (教科書通り):
1. **(6.8.2.1)** η^{τ₁} が Z^# 上定数 — 要確認 (landed?)。
2. **(6.8.2.2)** `Ind_Z^L φ − |H:Z|η₁ = X − |H:Z|Y` の aggregate — `exists_decomposition_caseB`
   (S08_CaseBCoherence2:126) で landed (cont.¹⁴)。
3. **(6.8.2.3)** per-χ: χ=Ind_H θ (Z⊄Ker θ), [Is]2.27 で Res_Z θ=aφ, Ind_H^Z φ=∑aᵢθᵢ, 各 χᵢ=Ind_H θᵢ
   (**irreducible**) に R(χᵢ) ((5.3)(5.4.a)(5.4.b)(5.5), §7 R-producer `dadeOrthonormalCharacterImageFamily`),
   (6.8.2.2) で bᵢ=aᵢ pin ⟹ αᵢ^τ=Xᵢ−aᵢY ⟹ (χ−aη₁)^τ=X₁−aY。**これが本丸 (item 3 相当だが主役)**。
4. **Proof of (6.8.2)**: τ₂ を Z[X∪Y] に直接定義 (supported=τ, η₁↦Y) + (6.8.2.3) で isometry 検証。
   §7 ツール候補 = `retarget_isCoherent_of_decomposition*` (S07:3737+; S₁-coherence + per-χ
   `himg: τ(χ−a·chi1)=D.X−a·extension chi1` で {χ,χ̄} を追加) を **base=Y-coherence** から X 上反復、
   または whole-lattice τ₂ を `coherentUnion_of_glued` 系へ ν=τ₂ で渡す (cX 不要の variant 要精査)。

### ⚠ 未確定 (next iteration / 要ユーザー判断):
- `coherentXunionYset_caseB_of_glued` shell (cX 要求) は **置換** すべきか、cX を retarget で構築して延命するか。
- reducible μ_j を τ₂ で扱う具体 (retarget は irreducible 単位; μ_j は whole-lattice τ₂ で一括 or certainTypeSet
  block で別処理)。**certainTypeSet machinery (item 2, {μ_j}-coh) は直接 route では off-path の可能性大**
  (true facts ではある)。
**正本=本 cont.²⁴ (ARCHITECTURE 再評価)。次=直接 τ₂ route ((6.8.2.3) per-χ R(χ) 分解) へ pivot。
item 1 は build しない。要ユーザー確認: glue shell 廃棄 vs 延命。**

## 2026-06-14 (session 40 cont.²⁵, /loop): ✅ 直接-τ₂ route の building blocks 全確認 + Z=W₂ 確定 + (6.8.2.3) entry landed

cont.²⁴ pivot を受け、直接-τ₂ route の前提を全検証。**全 building block が repo に存在** ⟹ route は実行可能で、
foundational pieces は **brick-friendly** (dedicated session 不要、loop で steady に積める)。

### ✅ 確定事実 (mmd 04.8 L150-160 精読):
- **case (B): Z = W₂** (textbook "Set Z=W₂ in case (B)")。⟹ **item 2 (`Xset h46.W2`) は正しい Z を target 済**
  (cont.²³ の懸念は杞憂)。X=S−S(W₂), Y=S(H′)=S(⁅H,H⁆) (m 個, 各 deg|W₁|, 既約)。
- capstone は `Xset ⁅H,H⁆` で split (Z=H′); (6.8.2) は Z=W₂ ⟹ Xset W₂⊆Xset H′ (W₂⊆H′)。両者の差は
  (6.8.3) layer (S coherent への拡張) ⟹ capstone wiring は (6.8.2) の downstream (後続課題)。

### ✅ building blocks (全 landed/available):
- **[Is]2.27** = `OddOrder.RepresentationTheory.IsIrreducibleCharacter.exists_central_linear_restriction`
  (Res_Z θ = θ(1)·φ, φ linear, Z≤Z(G); AxiomsCheck:2025 登録済)。
- **(6.8.2.2)** = `exists_decomposition_caseB` (S08_CaseBCoherence2:126, landed): `(Ind_Z^L φ−|H:Z|η₁)^τ
  = X−|H:Z|·cY.ext(η₁)`, X⊥cY(Y), X∈ZIrr。
- **(6.8.2.1)** = `IsCoherent.extension_constant_on_sharp_of_prime` (AxiomsCheck:2018 付近, landed)。
- **R(χ) machinery** = §7 `dadeOrthonormalCharacterImageFamily` (S07:5387) + (5.4.a/b) (S07:1378/1447)。
- **IsCoherent 直接 constructor** = structure (S07:1557): `extension`(ν=τ₂) + `extension_inner_eq`(isometry)
  + `extends_on_supported`(=τ on Z[S,A]) + `extension_mem_ZIrr`。⟹ τ₂ を明示構成して 4 fields を埋める。

### 📋 (6.8.2.3) per-χ 分解の sub-DAG (`(χ−aη₁)^τ = X₁−aY`, χ∈Xset W₂):
1. ✅ **entry** `mem_Xset_exists_inducing` (ce87acc0, landed): χ=Ind_H θ, θ≠1, W₂⊄Ker θ。
2. **[Is]2.27 適用**: Res_{W₂} θ = a·φ (φ∈Irr W₂, φ≠1, a=θ(1))。`exists_central_linear_restriction`
   (W₂⊆Z(H) は case-B; `certainType_W2_le_center`/`W2_le_center` 系)。← 次の brick。
3. **Ind_H^{W₂} φ = ∑aᵢθᵢ** (θᵢ∈Irr H distinct, Res θᵢ=aᵢφ, θᵢ(1)=aᵢ, θ=θ₁): Clifford/character。
4. **αᵢ=χᵢ−aᵢη₁ (χᵢ=Ind_H θᵢ), Supp αᵢ⊆H^#, ∑aᵢαᵢ=Ind_{W₂}^L φ−|H:W₂|η₁, ∑aᵢ²=|H:W₂|**: (6.8.2.2) と接続。
5. **R(χᵢ)⊥Y^{τ₁}** ((5.3)(5.5))。
6. **αᵢ^τ=Xᵢ−bᵢY+Zᵢ** (Xᵢ∈Z[R(χᵢ)]) + **(5.4.a) ‖Xᵢ‖²≥‖χᵢ‖² ⟹ bᵢ≤aᵢ**。
7. **pin bᵢ=aᵢ** ((6.8.2.2): ∑aᵢbᵢ=|H:W₂|=∑aᵢ²)。
8. **(5.4.b) αᵢ^τ=Xᵢ−aᵢY** ⟹ χ=χ₁ で `(χ−aη₁)^τ=X₁−aY`。【本丸 = steps 5-8 の R(χ) 統合】
### 📋 τ₂ assembly: `IsCoherent τ (Xset W₂ ∪ Yset) (supportInSubgroup H^# L)` を直接 constructor で:
ν=τ₂ (supported=τ, η₁↦Y=cY.ext η₁, χ↦X₁(χ) [(6.8.2.3)]) + isometry (generator 上, (6.8.2.3)+cY) +
ZIrr (X₁,Y∈ZIrr)。reducible μ_j も χ∈X として (6.8.2.3) で一律処理 (whole-lattice, 反復 retarget 不要)。

**正本=本 cont.²⁵。route 実行可能・brick-friendly 確認。entry landed。次 brick = step 2 ([Is]2.27 で
Res_{W₂} θ = a·φ)。item 1 (X_irr-coh) は廃棄確定 (教科書非対応)。glue shell は (6.8.2.3) 完成後に
置換判断 (cX 不要ゆえ最終的に未使用化見込み)。**

## 2026-06-14 (session 40 cont.²⁶, /loop): (6.8.2.3) clean-brick phase 完了 (steps 1-2 + 2 infra); 残=rep-theory infra 一から + R(χ) core ⟹ work の性質が変化、ユーザーに判断仰ぐ

### ✅ landed (clean bricks, 全 axiom-clean・full build 3807):
- step 1 `mem_Xset_exists_inducing` (ce87acc0)。
- `subgroupOf_le_center_of_le_center` (W₂.subgroupOf H ⊆ Z(↥H), ecdcef2f)。
- step 2 `certainType_central_restriction` (Res^H_{W₂} θ = θ(1)·φ, [Is]2.27, ecdcef2f)。
- `restrict_induce_eq_index_smul_of_le_center` (Res_Z(Ind_Z φ)=|Γ:Z|•φ central, 6fa6daf2; ∑aᵢ²=|H:Z| 入力)。

### 🛑 残 (6.8.2.3) は work の性質が変化 — clean brick でなく一から rep-theory infra:
- **step 3 残: induction transitivity `Ind_H(Ind_{Z}^H ψ) = Ind_Z^L φ`** — repo に無し。custom `induce`
  (= ⅟|H|•∑ induceTerm, InducedCharacter:262) の **二重和 coset 論法を一から** + Z.subgroupOf H ≅ Z
  transport。mathlib 級 infra。
- **step 3 残: character 分解 `Ind_Z^H φ = ∑aᵢθᵢ` (aᵢ=θᵢ(1))** — constituent 構造 (Clifford.lean の
  liesOver/restrictionMultiplicity 利用可だが、"character=∑⟨·,θ⟩θ" 分解 + aᵢ=θᵢ(1) 計算の組立は中規模)。
- **steps 5-8: R(χ) 統合** (本丸, 未着手) — §7 R-producer + (5.4.a/b) + bᵢ=aᵢ pinning。intricate。
- φ-presentation seams (W₂.subgroupOf H ↔ ↥W2, (6.8.2.2) の Ind_W2 接続) も複数。

### 🔑 honest 評価: clean-brick phase (steps 1-2 + 2 infra) は完了。残りは **一から rep-theory infra
構築 (induction transitivity 等) + R(χ) intricate 統合**の大規模 focused effort で、60s loop brick より
**dedicated session 向き**。FT 最短経路外 (full-Pf scope)。⟹ ユーザーに継続 vs 保留を判断仰ぐ (cont.²⁶)。
**正本=本 cont.²⁶。**

## 2026-06-14 (session 40 cont.²⁷, /loop): 🔧 訂正 — (6.8.2.3) norm/setup は既存; 私が重複構築→削除; genuine gap = decomposition+R(χ)+assembly。+ FT 接続の位置づけ確認 (ユーザー)

### ⚠ survey-before-build 失敗の訂正:
- **(6.8.2.1)+(6.8.2.2) は完成済** (S08_CaseBCoherence.lean: η^{τ₁}定数, 全 norm/cross-term/divisibility/
  trichotomy; `exists_decomposition_caseB` = (6.8.2.2) capstone)。
- **(6.8.2.3) の `∑aᵢ²=|H:Z|` norm も既存** = `inner_induce_self_eq_index_of_le_center` (S08_CaseBCoherence2:353,
  Mackey+conjBy-central+Frobenius, M=↥H/N=W₂.subgroupOf H)。
- 私は cont.²⁵-²⁶ でこの norm を**重複構築**してしまった (既存 case-B ファイル精査不足) → 重複 2本削除 (cb308e77)。
- **genuine 新規 (keep)**: entry `mem_Xset_exists_inducing` (ce87acc0) + central-in-H
  `subgroupOf_le_center_of_le_center` + step 2 `certainType_central_restriction` (ecdcef2f)。
  (central-in-H は line-353 norm の `hN:N≤center` を `certainType_W2_le_center` から供給する bridge ゆえ有用。)

### ▶ genuine な残 (6.8.2.3) gap (既存に無し, grep 確認):
1. **character 分解** `Ind_Z^H φ = ∑aᵢθᵢ` (θᵢ∈Irr H, aᵢ=θᵢ(1)=mult, θ=θ₁): Clifford constituent
   (`Clifford.lean` liesOver/restrictionMultiplicity 利用) + [Is]2.27 per θᵢ。
2. **induction transitivity** `Ind_H(Ind_Z^H φ) = Ind_Z^L φ`: custom induce の二重和 (未整備)。
3. **αᵢ aggregate** `∑aᵢαᵢ = Ind_Z^L φ − |H:Z|η₁` (αᵢ=χᵢ−aᵢη₁, χᵢ=Ind_H θᵢ): 1.+2.+norm(353) で。
4. **R(χᵢ) 統合 + bᵢ=aᵢ pinning** (steps 5-8, §7 R-producer + (5.4.a/b))。本丸。
5. **per-χ statement** `(χ−aη₁)^τ=X₁−aY` + **τ₂ direct assembly** (IsCoherent 直接 constructor S07:1557)。

### 📌 FT 接続 (ユーザー確認, 2026-06-14): case-B (6.8) は **FT 並行スパイン** (Pf §11 が将来 §7 coherence
API を使う) で FT の一部だが、**FTにつながる Pf §10-16 は BG §16 gate で着手不能**、実 FT ボトルネックは
**BG §13-16** (Lane F/G)。ユーザーは状況理解の上で **Pf §6-§8 coherence API 継続**を選択 (FT sorry は当面
減らないが Pf 完成に必要)。⟹ Lane B は case-B (6.8.2.3) genuine gap (上記 1-5) を継続。
**正本=本 cont.²⁷。次=既存 infra 精査の上 genuine gap (character 分解 from 1.) を構築。重複回避必須。**

## 2026-06-14 (session 40 cont.²⁸, /loop): 🔄 re-calibration — (6.8.2.3) infra は大半既存 (cont.²⁶ の「from-scratch mathlib infra」は悲観過ぎ); 分解 lemma landed

### 精査で判明 (cont.²⁶ の評価訂正): (6.8.2.3) の building block は**大半既存**:
- **Fourier 展開** `classFunction_eq_sum_inner_smul` (S08_CoherenceCorePart1:87) = `χ=∑_θ⟨χ,θ⟩•θ`。
- **∑aᵢ²=|H:Z| norm** `inner_induce_self_eq_index_of_le_center` (S08_CaseBCoherence2:353)。
- **Clifford** `restrictionMultiplicity`/`liesOver`/`IsRestrictionConstituent` (Clifford.lean)。
- **§7 R(χ)** `OrthonormalCharacterImageFamily` (S07:766) + (5.4) `inner_self_of_mem`/`Orthogonal`。
- **(6.8.2.2) 一式** (norm/cross-term/divisibility/trichotomy, exists_decomposition_caseB)。
⟹ (6.8.2.3) は「from-scratch infra」でなく**既存機構の assembly + induction transitivity 1本**。

### ✅ landed (iter, 6b3aede9): **`induce_eq_sum_inner_restrict_smul`** = `Ind^M_N φ = ∑_θ⟨φ,Res_N θ⟩•θ`
(Fourier + Frobenius)。新規確認済 (重複なし)。(6.8.2.3) の `Ind^H_Z φ=∑aᵢθᵢ` 分解 (coeff=mult)。

### ▶ 残 (6.8.2.3) genuine gap (assembly 主体):
1. **coeff→degree**: `⟨φ,Res_N θ⟩ = θ(1)·[θ over φ]` ([Is]2.27 per θ; θ over central linear φ ⟹ Res=θ(1)φ)。← 次, 最 tractable。
2. **induction transitivity** `Ind_H(Ind_{W₂.subgroupOf H}^H φ) = Ind_{W₂}^L φ` (custom induce 二重和, 唯一の from-scratch infra)。
3. **αᵢ aggregate** `∑aᵢαᵢ = Ind_{W₂}^L φ − |H:Z|η₁` (1+2+norm)。
4. **R(χᵢ) 統合 + bᵢ=aᵢ pinning** (§7 OrthonormalCharacterImageFamily + (5.4))。本丸。
5. **per-χ statement + τ₂ direct assembly**。
**正本=本 cont.²⁸。(6.8.2.3) は再評価で tractable 化 (infra 大半既存)。次=coeff→degree (1.)。重複回避に survey 必須 (本 session で 3 回 duplicate 回避)。**

## 2026-06-14 (session 40 cont.²⁹, /loop): ✅✅ (6.8.2.3) infra 完成 — induction transitivity landed (Frobenius 経路で clean); 残=aggregate + R(χ)

### ✅ landed (2 iter, 全 axiom-clean, full build 3807):
- **`inner_compHom_of_mulEquiv`** (97a73357): 群同型 e に沿った inner 保存 `⟨a∘e,b∘e⟩=⟨a,b⟩` (transport 部品)。
- **`induce_induce_subgroupOf`** (1e93c83e): **induction transitivity** `Ind^M_H(Ind^H_{K.subgroupOf H} ψ∘e)=Ind^M_K ψ`
  (K≤H≤M)。**Frobenius 経路で ~25 行**: `classFunction_eq_zero_of_orthogonal` + double Frobenius +
  restriction-transport (`Res_{K.subgroupOf H}(Res_H χ)=(Res_K χ)∘e`, M-value defeq で `congr 1`) +
  inner_compHom。⚠ cont.²⁶ の「from-scratch mathlib 二重和 infra」は**過大評価**だった (raw 二重和 不要)。

### 🎉 (6.8.2.3) infra 完成 — 残りは assembly のみ:
| piece | status |
|---|---|
| 分解 `Ind_Z^H φ=∑_θ⟨φ,Res_Z θ⟩•θ` | ✅ `induce_eq_sum_inner_restrict_smul` (6b3aede9) |
| transitivity `Ind_H∘Ind_Z=Ind_Z` | ✅ `induce_induce_subgroupOf` (1e93c83e) |
| ∑aᵢ²=\|H:Z\| norm | ✅ `inner_induce_self_eq_index_of_le_center` (:353, 既存) |
| Frobenius/completeness/R(χ) | ✅ 既存 |
| linearity `induce_add/smul` | ✅ 既存 |

### ▶ 残 (6.8.2.3) = assembly (infra 出揃い):
1. **αᵢ aggregate** `∑aᵢαᵢ = Ind_{W₂}^L φ − |H:Z|η₁`: 分解 → Ind_H linearity (induce_add/smul) →
   transitivity → `∑aᵢχᵢ=Ind_{W₂}^L φ`; ∑aᵢ²=|H:Z| (norm+Parseval `inner_self_eq_sum_sq_of_repr`)。
2. **R(χᵢ) 統合 + bᵢ=aᵢ pinning** (§7 OrthonormalCharacterImageFamily + (5.4.a/b))。本丸。
3. **per-χ statement + τ₂ direct assembly** (IsCoherent 直接 constructor)。
**正本=本 cont.²⁹。infra 完成は重要マイルストン。次=αᵢ aggregate (1.)。FT 並行スパイン (sorry 当面不変)。**

## 2026-06-14 (session 40 cont.³⁰, /loop): ✅ αᵢ aggregate 両半 landed; 残 = combination + R(χ) 統合 (本丸)

### ✅ landed (3 iter, 全 axiom-clean, full build 3807):
- `induce_finset_sum_smul` (Ind_H Finset 線形性) + **`sum_inner_restrict_smul_induce_eq_induce`**
  (f281ba5c, aggregate 前半 `∑aᵢχᵢ=Ind^M_K φ` = 分解+線形性+transitivity, 2 行)。
- **`inner_self_induce_eq_sum_mul_star`** (cde453e1, Parseval `‖Ind φ‖²=∑aθ·conj aθ`)。
- **`sum_inner_restrict_sq_eq_index`** (83ec0b32, aggregate η₁係数 `∑aᵢ²=|M:N|` = reality(aθ∈ℤ via
  inner_mem_ZIrr_int)+Parseval+norm)。

### 🎉 αᵢ aggregate 両半完成 (∑aᵢχᵢ=Ind_K φ + ∑aᵢ²=|M:N|):
残 aggregate = **combination** `∑aᵢαᵢ = ∑aᵢχᵢ − (∑aᵢ²)η₁ = Ind^L_{W₂}φ − |H:Z|η₁` (両半を機械的に結合)。

### ▶ 残 (6.8.2.3) = R(χ) 統合 (steps 4-8, **本丸・未着手**):
4. **R(χᵢ)⊥Y** ((5.3)(5.5)) + αᵢ^τ=Xᵢ−bᵢY+Zᵢ (Xᵢ∈Z[R(χᵢ)])。§7 `OrthonormalCharacterImageFamily`。
5. **(5.4.a) ‖Xᵢ‖²≥‖χᵢ‖² ⟹ bᵢ≤aᵢ**。
6. **pinning** ((6.8.2.2) `exists_decomposition_caseB` で ∑aᵢαᵢ^τ=X−|H:Z|Y; ∑aᵢbᵢ=|H:Z|=∑aᵢ² ⟹ bᵢ=aᵢ)。
7. **(5.4.b) αᵢ^τ=Xᵢ−aᵢY** ⟹ χ=χ₁ で per-χ `(χ−aη₁)^τ=X₁−aY`。
8. **τ₂ direct assembly** (IsCoherent 直接 constructor)。
**正本=本 cont.³⁰。aggregate 両半完成。次=combination (機械的) → R(χ) 統合 (本丸, §7 R-producer 精査要)。
infra 出揃いで assembly は steady だが R(χ) 統合は intricate。FT 並行スパイン。**

## 2026-06-14 (session 40 cont.³¹, /loop): ✅ αᵢ aggregate 完成 (combination landed); R(χ) 統合 = 本丸の §7 interface 精査

### ✅ landed (95d1bee1): **`sum_smul_constituent_diff_eq`** = full αᵢ aggregate
`∑aᵢαᵢ = Ind^L_{W₂}φ − |H:Z|η₁` (両半の機械的結合 smul_sub+sum_sub_distrib, one-shot)。
⟹ **(6.8.2.3) の infra + αᵢ aggregate 完全完成** (cont.²⁶〜³¹ で ~12 lemma landed, 全 axiom-clean)。

### 🔬 R(χ) 統合 (steps 4-8, 本丸) の §7 interface 精査:
- **R(χ) = `OrthonormalCharacterImageFamily τ χ`** (S07:766): orthonormal ⊂ ZIrr, `τ(χ−χ̄)=∑R(χ)`。
  producer = `dadeOrthonormalCharacterImageFamily` (S07:5387, irreducible χ から)。
- **(5.4) = `CharacterPsiDecomposition τ χ ψ`** (S07:1356-1469): X−bY+Z 分解 + bounds。
  - (5.4.a) `inner_self_chi_re_le_inner_self_X` (:1382): ‖χ‖²_re ≤ ‖X‖²。
  - (5.4.b) `norm_eq_and_X_eq_sum_of_norm_Y_ge` (:1469): ‖Y‖²≥‖ψ‖² ⟹ 等号 + X=∑R(χ)。
- **🔑 `retarget_isCoherent_of_decomposition` (S07:3737)**: CharacterPsiDecomposition + himg
  (`τ(χ−a•chi1)=D.X−a•ext chi1` = (6.8.2.3) 形) で **{χ,χ̄} を coherent set に追加** — **(5.4)+pinning を
  内部化**。⟹ 直接-τ₂ は Y-coherence base から **retarget を X 共役対で反復**が筋。

### 🛑 R(χ) 統合の難所 (本丸):
1. **reducible μ_j**: retarget は irreducible 対のみ ⟹ μ_j=∑μ_{ij} は直接追加不可。whole-lattice τ₂ で
   一括 or μ_j を constituent (6.8.2.3) 経由で別処理 (cont.¹⁴ の reducible-aware)。
2. **himg per χ** = (6.8.2.3) `(χ−aη₁)^τ=X₁−aY`: αᵢ aggregate (済) + R(χᵢ) per-constituent + pinning
   ((6.8.2.2) `exists_decomposition_caseB` で ∑aᵢαᵢ^τ=X−|H:Z|Y; ∑aᵢbᵢ=∑aᵢ²=|H:Z| ⟹ bᵢ=aᵢ)。
3. **αᵢ の ψ=η₁ (Y-anchor)** と §7 CharacterPsiDecomposition (χ,ψ pair) の interface 整合。
**honest: R(χ) 統合は §7 (5.4)/retarget 機構との深い integration で intricate な本丸。aggregate まで
の準備は完了。次=retarget interface の himg 供給 (αᵢ^τ decomposition) の構築。要集中。**
**正本=本 cont.³¹。aggregate 完成 (重要マイルストン)。R(χ) 統合 = 深い §7-integration の本丸が残る。**

### 🔑 R(χ) 統合の具体 producer path (cont.³¹ 末, 精査結果):
- **`CharacterPsiDecomposition.ofProjection`** (S07:1185): R(χ) (imageFamily) + τ₁ + (htau1_inner_eq /
  htau1_agrees / htau1_mem `τ₁(χ−ψ)∈ZIrr` / 3 orthogonalities) から **X/Y/coeff/X_eq/Y_orthogonal を
  projection で自動構築** (`exists_intProjection_of_orthonormal_ZIrr`)。残 primitive = R(χ) extractor + τ₁。
- **`CharacterPsiDecomposition.decompositionPair`** (S07:1237): 同 χ・同 τ₁ で (D₀, Da) pair を構築
  (retarget_isCoherent_of_decompositions の τ₁-agreement が rfl)。ψ=0 と ψ=a•chi1。
- **`retarget_isCoherent_of_extensionImage`** (S08_CoherenceCorePart1:1980): case-A/(6.6) engine、
  これが {χ,χ̄} を coherent set に追加 ((5.4)+pinning 内部化)。
- **R(χ) producer** = `dadeOrthonormalCharacterImageFamily` (S07:5387) / `…OfDiff` (S08:1681)。
⟹ (6.8.2.3) R(χ) 統合 = per-constituent χᵢ で decompositionPair (R(χᵢ)+τ₁+facts) → retarget。
**残 deep 作業**: (a) χᵢ=Ind_H θᵢ が irreducible か (R(χᵢ) producer の前提) の精査, (b) τ₁=Y-coherence
isometry の供給, (c) reducible μ_j の whole-lattice 処理, (d) aggregate→pinning 接続。
**= 深い §7 assembly の本丸; machinery は出揃い (ofProjection/decompositionPair/retarget/R-producer),
per-constituent 組立 + 接続が残る。要集中。次=per-constituent decompositionPair の inputs 供給。**

## 2026-06-14 (session 40 cont.³², /loop): ✅ pinning (item d 算術核) landed + 🔬 item (a) 精査結果 = (5.4) は χ 既約性不要

### ✅ landed (7409f2e9, axiom-clean 標準3, leaf build 3625):
**`eq_of_sum_mul_eq_sum_sq`** (S08_CaseBCoherence2, aggregate 直後) = (6.8.2.3) pinning の算術核:
`(∀i∈s, 0≤aᵢ) ∧ (∀i∈s, bᵢ≤aᵢ) ∧ ∑aᵢbᵢ=∑aᵢ² ⟹ ∀i∈s, 0<aᵢ→bᵢ=aᵢ`。証明 = slackness
`∑aᵢ(aᵢ−bᵢ)=0` (各項≥0) → `Finset.sum_eq_zero_iff_of_nonneg` で per-term `aᵢ(aᵢ−bᵢ)=0`
→ `mul_eq_zero`+`aᵢ>0` で `bᵢ=aᵢ`。**純粋ℤ算術で R(χ) machinery から完全 decoupled** ⟹ steps 5-8
の中で唯一独立に landable な load-bearing brick を先取り (item d / step 7 算術部)。caller は
ℂ→ℤ 抽出 (`inner_mem_ZIrr_int`) 後にこれを適用する。

### 🔬 item (a) 精査結果 (原文 04.8 L208-224 + §7 machinery 精読): **(5.4) は χ 既約性を要求しない**
- Peterfalvi (6.8.2.3) は χᵢ=Ind_H θᵢ の**既約性を明示しない** (case-A (6.8.1) L76 は "χ∈Irr L" 明示だが
  case-B (6.8.2) は X が reducible μ_j を含むので χᵢ も reducible でありうる)。不等式
  `bᵢ²≤‖χᵢ‖²+aᵢ²−‖Xᵢ‖²≤aᵢ²` は (5.4.a) `‖Xᵢ‖²≥‖χᵢ‖²` だけで動き、‖χᵢ‖²=1 (既約) は**不要**。
- §7 `CharacterPsiDecomposition`/(5.4.a)`inner_self_chi_re_le_inner_self_X`/(5.4.b)
  `norm_eq_and_X_eq_sum_of_norm_Y_ge` は**抽象 `OrthonormalCharacterImageFamily τ χ` 上で動く**
  (keystone `inner_self_chi_eq_sum_coeff` は image family の `image_eq`+τ₁ のみ使用、既約性 unused)。
- ⟹ **唯一既約性が入るのは producer `dadeOrthonormalCharacterImageFamilyOfDiff` (S07:5472) の
  `χ:IrreducibleCharacter` 型付け** (conjPairFamily+`(fam i).mem_ZIrr` 経由)。だが `mem_ZIrr` は
  **任意の指標で成立** (character ∈ ℤ≥0·Irr ⊂ ZIrr) ゆえ、構成 (Dade isometry on supported diff
  `χ̄ᵢ−χᵢ`) は reducible χᵢ でも通る。obstruction は型 (conjPairFamily/keystone が IrreducibleCharacter
  入力) のみ。diff-supportedness (`χ̄ᵢ−χᵢ` が 1 で消え H^# 上 supported) は χᵢ=Ind_H θᵢ なら無条件成立。

### ▶ R(χ) 統合 残ステップ (依存順、cont.³¹ items を精査後に再構成):
1. **R(χᵢ) producer の決着 (item a)**: 二択 — (a1) case-B で χᵢ=Ind_H θᵢ が既約と証明 (Clifford
   I_L(θᵢ)=H; reducible μ_j との整合要確認) / (a2) **ZIrr-character 版 R-producer を新設**
   (`dadeOrthonormalCharacterImageFamilyOfDiff` の χ を IrreducibleCharacter→「χ∈ZIrr かつ character」
   へ一般化; conjPairFamily を char-pair 版に, keystone は mem_ZIrr で OK)。**(a2) が筋が良い** (既約性を
   証明する迂回が不要; 構成は同一)。← **次の本丸 brick**。
2. **τ₁ 供給 (item b)** = Y-coherence isometry。
3. per-constituent `CharacterPsiDecomposition` (R(χᵢ)+τ₁) → (5.4.a) `bᵢ≤aᵢ`。
4. **pinning ✅ (本 cont.³²)** ∑aᵢbᵢ=∑aᵢ²=|H:Z| ⟹ bᵢ=aᵢ。
5. (5.4.b) `αᵢ^τ=Xᵢ−aᵢY` → per-χ `(χ−aη₁)^τ=X₁−aY` → τ₂ direct assembly。
**正本=本 cont.³²。pinning 算術核 landed; item (a) は (a2) ZIrr-char R-producer 一般化が次の本丸 brick
(既約性証明を回避でき構成同一)。要集中。**

## 2026-06-14 (session 40 cont.³³, /loop): 🚨 cont.³² 訂正 — R(χ) は §5 (5.2.d) で **χ 既約⟺2-element / χ=μ_j⟺(4.9)族** の 2 ケース; (a2) 一般化は誤り

cont.³² の「(a2) ZIrr-char 一般化」は **原文 §5 精読で誤りと判明**。R(χ) は ‖(χ−χ̄)^τ‖²=|R(χ)| ゆえ
χ の既約性で本質的に形が変わる (任意 ZIrr-char へ一様一般化は不可)。原文 (5.2.d)/(5.3) の正確な構造:

### 🔑 原文 §5 (04.7) の決定的構造:
- **(5.2.d)** = R(χ) は仮説 (χ∈S に対し (χ−χ̄)^τ=∑_{α∈R(χ)}α, R(χ) orthonormal ⊂ ℤ[Irr G])。
  ‖(χ−χ̄)^τ‖²=‖χ−χ̄‖²=2‖χ‖² ゆえ |R(χ)|=2‖χ‖²。
- **(5.3.a)**: S⊆Irr L ⟹ Hyp (5.2) 成立 (各 χ 既約 ⟹ ‖χ‖²=1 ⟹ |R(χ)|=2)。
- **(5.3.b)** [case-B の鍵]: Hyp (4.6) 下、S⊆{Ind_K θ : H⊄Ker θ} ⟹ Hyp (5.2) 成立。R(χ) は
  **χ 既約なら 2-element (as in a)、χ reducible なら χ=μ_j (0<j<w₂) で R(μ_j)=
  {δ_j ω_{ij}^σ, −δ_j ω_{ik}^σ | 0≤i<w₁}** (μ̄_j=μ_k, **Theorem (4.9)** より)。
- ⟹ **case-B の S は既約 χ と reducible μ_j 両方を含む** (X⊂Irr L は **case-A のみ**; cont.²⁴/前ノートの
  「X が reducible μ_j を含む」は case-B では**正しい**, 私の cont.³² の「X⊂Irr L」断定が誤りだった)。
- `isIrreducibleCharacter_of_mem_Xset_caseA` (S08CCP2:1860) は FPF (`W₁ FPF on Z`) を要するが
  **case-B は W₂⊆Z(L) (`certainType_W2_le_center`) ゆえ W₁ は W₂ を中心化 (FPF 不成立)** ⟹ case-B X に
  は適用不可 (case-A 専用)。∴ case-B X-member は既約とは限らない (μ_j を含む)。

### ✅ 既存資産 (survey 済):
- **抽象 R(χ)** = `OrthonormalCharacterImageFamily τ χ` (任意 χ:ClassFunction; S07:766)。
- **既約 χ 用 producer** = `dadeOrthonormalCharacterImageFamilyOfDiff` (S07:5472) +
  per-step `decompositionDaFromDadeOfDiff` (S07:5542, `CharacterPsiDecomposition τ χ (a•chi1)` を直接生成)。
- **reducible μ_j coherence** = `certainType_isCoherent` (S06_CertainTypeCoherence:505, (4.9)(b) を
  `IsCoherent τ certainTypeSet A` として完成) → `certainTypeSet_isCoherent_tau` (S08CB2:719, hyp.tau へ転送)。
- **R(μ_j) image_eq** = **`certainType_diff_dade_sum_eq`** (S06CTI:936, landed): (μ_j−μ_k)^τ=δ_j∑_i(ω_ij^σ−ω_ik^σ)。
- μ̄_j=μ_{j'}: `certainType_columnSum_conj` (S06CTC); ω^σ conj: `certainTypeOmegaSigma_conj` (S06CTConj:64)。
- **🛑 未実装 = reducible R(μ_j) を `OrthonormalCharacterImageFamily τ μ_j` として package** (item c)。

### ▶ 次の具体 brick (確定, cont.³⁴ で BUILD): **reducible R(μ_j) producer**
`OrthonormalCharacterImageFamily (certainType τ) μ_j` を (4.9) データから構成:
- imageSet = {δ_j•ω_{ij}^σ, −δ_j•ω_{ik}^σ | 0≤i<w₁} (Finset, k: μ̄_j=μ_k)。
- mem_ZIrr: 各 ±σ-image ∈ ZIrr (`certainTypeOmegaSigma_mem_ZIrr` S06CTC:146)。
- orthonormal: σ-image Gram (`columnFamily_mu_sum_inner` 系) + δ_j²=1。
- image_eq: (μ_j−μ_j.conj)^τ=∑α ⟸ `certainType_diff_dade_sum_eq` + `certainType_columnSum_conj`。
**⚠ アーキ判断 (cont.³⁴ 冒頭で決定)**: (6.8.2.3) per-χ (χ−aη₁)^τ=X₁−aY を、χ 既約は Dade-R(χ)、
χ=μ_j は R(μ_j) or **`certainType_isCoherent` 直結**のどちらで処理するか。後者なら R(μ_j) package 不要かも
(certainType coherence が既に μ_j 側を担う)。**この判断を先にしてから R(μ_j) を build する/しないを決める。**

### ⚠ R(μ_j) package を build する場合の seam (cont.³³ で精査、要対処):
- `certainType_diff_dade_sum_eq` の LHS は **`h.tau.toDadeMap (∑ certainTypeDiffSupported h … i)`**
  (IntegralCharacterMap でなく toDadeMap; 引数も column-difference family `certainTypeDiffSupported`)。
  `OrthonormalCharacterImageFamily.image_eq` の `τ (μ_j − μ_j.conj)` 形へ橋渡しが要 (∑certainTypeDiffSupported
  = μ_j − μ_k? + toDadeMap↔IntegralCharacterMap 接続)。
- RHS = `(columnFamily χ₂).sign • ∑_i (ω_{χ₂,i}^σ − ω_{χ₂',i}^σ)` (sign=δ_j, χ₂'=共役列 k)。
- μ_j.conj=μ_{χ₂⁻¹}: `certainType_columnSum_conj`; ω^σ conj=`certainTypeOmegaSigma_conj_eq` (χ₂⁻¹,rowInv i)。
- orthonormal: `certainTypeOmegaSigma_inner` (⟨ω_{χ₂,i}^σ,ω_{χ₂',i'}^σ⟩=[χ₂=χ₂'∧i=i'])。
**⟹ seam が複数。`certainType_isCoherent` 直結の方が seam 少ない可能性 → cont.³⁴ で両者比較してから決定。**

### 📝 honest 進捗評価 (2 ターン RECON):
cont.³² (pinning landed) 後、本 cont.³³ は **コード未 land の RECON ターン**。だが §5 原文精読で
cont.³² の (a2) 誤推奨を訂正し、R(χ) 統合の正確な map (既約/μ_j 2 ケース + 既存資産 + 未実装 = R(μ_j)
package) を確定 = 必要な是正。**次ターンはアーキ判断 1 つ → BUILD (RECON ループを断つ)。**
**正本=本 cont.³³。(a2) は廃棄。次=アーキ判断 (R(μ_j) package vs certainType_isCoherent 直結) → build。**

## 2026-06-14 (session 40 cont.³⁴, /loop): ✅ reducible R(μ_j) の orthonormal core landed (BUILD)

### アーキ判断 (確定): **R(μ_j) package を build する**
(6.8.2.3) per-χ `(χ−aη₁)^τ=X₁−aY` は X₁⊥Y を要し、`certainType_isCoherent` (μ_j 内部 coherence、Y 非言及)
単独では出ない。τ₂ 直接 assembly は per-constituent R(χᵢ) 分解 (irreducible: Dade R / reducible: R(μ_j))
を要し、R(μ_j) は `OrthonormalCharacterImageFamily` として必要。⟹ build。

### ✅ landed (f5c38fe3, axiom-clean 標準3, full build 3813/8.4s):
**`certainTypeRImage` + `certainTypeRImage_inner`** (S06_CertainTypeCoherence 末尾):
- `certainTypeRImage h χ₂ χ₂' : Bool × Fin w₁ → CF G` = R(μ_j) member family
  (`(false,i)↦δ_j ω_{ij}^σ`, `(true,i)↦−δ_j ω_{ik}^σ`; match-def)。
- `certainTypeRImage_inner` (χ₂≠χ₂'): `⟨R p, R q⟩ = [p=q]` (orthonormality)。証明 = `certainTypeOmegaSigma_inner`
  (grid 直交) + sign=±1 (`sign_eq` ⟹ δ·δ̄=1, δ²=1) + 4-case (対角 ←mul_assoc+hδsq, 非対角 χ₂≠χ₂'⟹0)。
- **R(μ_j) の orthonormal core (全 seam から decoupled な reusable piece)**。gotchas: `inner_smul_right`
  は `RepresentationTheory.` 修飾必須 (mathlib `_root_.inner_smul_right` と曖昧); `↓reduceIte` で
  `if False` を RHS 簡約; match-def で `cases bp` の ite 簡約が clean。

### ▶ 残 R(μ_j) producer (`OrthonormalCharacterImageFamily (dadeICM h.dade0 h.tau) μ_j`):
1. **imageSet** = `Finset.univ.image (certainTypeRImage h χ₂ χ₂')` (Bool×Fin w₁ 上)。injective は
   orthonormality の系 (f p=f q ⟹ ⟨f p,f q⟩=1≠0 ⟹ p=q)。`orthonormal` field = `certainTypeRImage_inner`
   + Finset.image membership (α=β ↔ index 一致)。`mem_ZIrr` = `certainTypeOmegaSigma_mem_ZIrr` + neg。
2. **image_eq** (seam): `dadeICM h.dade0 h.tau (μ_j − μ_j.conj) = ∑_{α∈imageSet} α`。bridge =
   (a) μ_j−μ_j.conj supported ⟹ dadeICM=toDadeMap (`dadeIntegralCharacterMap_apply_of_support`),
   (b) `certainType_diff_dade_sum_eq` (toDadeMap (∑certainTypeDiffSupported)=sign•∑(ω−ω')),
   (c) ∑certainTypeDiffSupported = μ_j−μ_k (Finset, columnSum=∑_i μ_{ij}),
   (d) μ_k=μ_j.conj (`certainType_columnSum_conj`), (e) sign•∑(ω−ω')=∑_{α}α (imageSet 展開)。
3. ⟹ R(μ_j) producer 完成 → per-constituent decomposition (irreducible は `decompositionDaFromDadeOfDiff`
   既存; reducible は R(μ_j) + `ofProjection`) → (5.4.a)+pinning[済]+(5.4.b) → τ₂。
**正本=本 cont.³⁴。orthonormal core landed (BUILD でループ脱出)。次=imageSet packaging (1.) → image_eq bridge (2.)。**

## 2026-06-14 (session 40 cont.³⁵, /loop 再開): ✅ R(μ_j) producer の infra + image_eq 数学内容 全 landed

### ✅ landed (a7634003 + e75ded15, axiom-clean 標準3, leaf 3601):
- **`certainTypeRImage_injective`** (a7634003): 署名族は単射 (orthonormality の系)。imageSet=Finset.image
  の orthonormal field + sum_image に必要。
- **`certainTypeRImage_sum`** (a7634003): `∑_p R(μ_j) p = δ_j ∑_i(ω_{ij}^σ−ω_{ik}^σ)`
  (= certainType_diff_dade_sum_eq の RHS)。Fintype.sum_prod_type+sum_bool+smul_sum+abel。
- **`dadeICM_columnDiff_eq_sum`** (e75ded15, image_eq 数学内容): `dadeICM(μ_j−μ_k)=∑_p R(μ_j) p`。
  🔑 **既存 `certainTypeExtension_columnDiff_eq_dade` (S06:335) が dade-seam (dadeICM↔toDadeMap) を
  既に解決済み**だったのを利用 (dadeIntegralCharacterMap_apply_of_support+IsDadeMap.unique+
  certainType_diff_dade_sum_eq)。+ certainTypeExtension_columnSum + certainTypeRImage_sum +
  ℤ/ℂ-smul 橋渡し `Int.cast_smul_eq_zsmul`。**⟹ image_eq の hard seam は全消化。**

### ▶ 残 = R(μ_j) producer struct (`OrthonormalCharacterImageFamily (dadeICM h.dade0 h.tau) (columnSum χ₂)`):
パラメータ χ₂, χ₂' (+ χ₂≠1, χ₂'≠1, hdeg, **conj 同定 `(columnSum χ₂).conj = columnSum χ₂'`**)。
- `imageSet := Finset.univ.image (certainTypeRImage h χ₂ χ₂')`。
- `mem_ZIrr`: α=±δ•ω ∈ ZIrr (`Int.cast_smul_eq_zsmul`+`Submodule.zsmul_mem`+`certainTypeOmegaSigma_mem_ZIrr`)。
- `orthonormal`: `certainTypeRImage_inner` + `certainTypeRImage_injective` (Finset.mem_image 抽出 → α=β↔p=q)。
- `image_eq`: `rw[conj同定]; rw[Finset.sum_image injective]; exact dadeICM_columnDiff_eq_sum`。
- **conj 同定** = `(columnSum χ₂).conj = columnSum χ₂'`: `certainType_columnSum_conj` (χ₂'=χ₂⁻¹) +
  `ClassFunction.conj` vs `mapRingEquiv conjAe` の一致確認 (要精査; これが最後の seam)。
→ producer 完成後: per-constituent (irreducible=`decompositionDaFromDadeOfDiff` / reducible=R(μ_j)+`ofProjection`)
→ (5.4.a)+pinning[済]+(5.4.b) → τ₂ assembly。
**正本=本 cont.³⁵。image_eq 数学内容 完成。次=producer struct 4-field 組立 (conj 同定が最後の seam)。**

## 2026-06-14 (session 40 cont.³⁶, /loop): ✅✅✅ reducible R(μ_j) producer COMPLETE (item c 解決)

### ✅ landed (72798461, axiom-clean 標準3, leaf 3601):
- **`columnSum_conj_eq`**: `(μ_j)‾ = μ_{j⁻¹}` (`ClassFunction.conj` 形の (4.9)(a))。
  🔑 **star = conjAe は defeq** (`rfl` で閉じる; certainType_columnSum_conj の mapRingEquiv 形と接続)。
- **`certainTypeR`** = **reducible R(μ_j) `OrthonormalCharacterImageFamily`** 完成 (全 4-field):
  imageSet=Finset.image certainTypeRImage / mem_ZIrr (Int.cast_smul_eq_zsmul+Submodule.smul_mem+neg_mem) /
  orthonormal (certainTypeRImage_inner+_injective, by_cases on indices で if-instance 不一致回避) /
  image_eq (columnSum_conj_eq+Finset.sum_image+dadeICM_columnDiff_eq_sum)。
  パラメータ = χ₂≠1 + hdeg (`∑μ_{χ₂,i}(1)=∑μ_{χ₂⁻¹,i}(1)`)。
- **gotchas**: `open scoped Classical in` は **docstring の前**に置く (DecidableEq (ClassFunction G ℂ) を
  Finset.image に供給; docstring と def の間に置くと "unexpected token open")。orthonormal の if-instance
  不一致 (Classical vs Prod.decEq) は `.eq_iff` rw でなく `by_cases hpq` で回避。

### 🎉 マイルストン: R(χ) 統合の両 producer 完備:
- **既約 χ ∈ X**: `dadeOrthonormalCharacterImageFamilyOfDiff` (S07:5472, 既存) + per-step
  `decompositionDaFromDadeOfDiff` (S07:5542)。
- **reducible μ_j ∈ X**: `certainTypeR` (本日完成) + `ofProjection`。
- **(5.4.a)** `inner_self_chi_re_le_inner_self_X` (済) / **pinning** `eq_of_sum_mul_eq_sum_sq` (cont.³²) /
  **(5.4.b)** `norm_eq_and_X_eq_sum_of_norm_Y_ge` (済)。

### ▶ 残 R(χ) 統合 = S08 case-B 側の per-constituent assembly (S06→S08 接続):
1. per-constituent χᵢ (Ind_H θᵢ, θᵢ=Ind_Z^H φ 構成子) を irreducible/μ_j 判定 → R(χᵢ) 供給
   (既約=dade producer / reducible=certainTypeR) → CharacterPsiDecomposition (decompositionDaFromDadeOfDiff
   or ofProjection)。
2. αᵢ^τ=Xᵢ−bᵢY+Zᵢ + (5.4.a) bᵢ≤aᵢ → pinning (∑aᵢbᵢ=∑aᵢ²=|H:Z|, eq_of_sum_mul_eq_sum_sq) → bᵢ=aᵢ。
3. (5.4.b) αᵢ^τ=Xᵢ−aᵢY → per-χ `(χ−aη₁)^τ=X₁−aY` (6.8.2.3 本体) → τ₂ direct assembly (S08)。
**正本=本 cont.³⁶。R(μ_j) producer 完成 (重要マイルストン)。次=S08 case-B per-constituent assembly
(S06 R-producer 群を (6.8.2.3) で組む; τ vs hyp.tau の整合 + Y-coherence τ₁ 供給が次の seam)。**

## 2026-06-14 (session 40 cont.³⁷, /loop): ✅ τ-seam の核心解決 — generic inner-preservation landed

### 精査 (τ-seam の正体): per-constituent CharacterPsiDecomposition (`ofProjection`) は
{χ−χ̄, χ−aη₁} 上の inner-preservation を要するが、η₁∉certainTypeSet ゆえ `certainTypeExtension_inner_eq`
(certainTypeSet 内部) では不足。**汎用 `dadeIntegralCharacterMap_inner_eq_on_supported_span` は
`hconj` を要求**し、certain-type τ=`dadeICM h.dade0 h.tau` の `h.tau` は **generic FullDadeIsometryData
(hconj 無し, Hypothesis46 の field)** ゆえ直接適用不可。← これが τ-seam の核心。

### ✅ landed (5fee74e5, axiom-clean 標準3, **full build 3813/108s** ← S07 touch で全 Pf 鎖再 elab):
**`dadeIntegralCharacterMap_inner_eq_on_supported_span_of_data`** (S07, 既存 lemma 直後):
任意 `dade : FullDadeIsometryData hyp` で inner-preservation 成立 (hconj 不要)。証明 =
`apply_of_support` (lift=hyp.dadeMap) + `IsDadeMap.unique hyp.isDadeMap_dadeMap dade.toDadeIsometryData.isDadeMap`
(hyp.dadeMap=dade.toDadeMap) + `FullDadeIsometryData.inner_eq` (dade 自身の isometry, S04:3821 hconj 不要)。
**⟹ certain-type τ で ofProjection が使える。** ⚠ **S07 (upstream) touch は ~108s**; 以後 S06/S08 は ~8s。

### ▶ 残 per-constituent assembly (S06/S08, この inner-preservation を使う):
1. **μ_j 用 CharacterPsiDecomposition** = `certainTypeR` (R(μ_j)) + `ofProjection` (τ=dadeICM h.dade0 h.tau,
   inner-preservation=本 cont.³⁷ generic 版, htau1_mema=τ(μ_j−aη₁)∈ZIrr, orthogonalities
   ⟨μ_j,η₁⟩=0 [X⊥Y] / ⟨μ_k,η₁⟩=0 / ⟨μ_j,μ_k⟩=0 [columnFamily_mu_sum_inner])。
   irreducible χ 用は `decompositionDaFromDadeOfDiff` 既存。
2. αᵢ^τ=Xᵢ−bᵢY+Zᵢ + (5.4.a) bᵢ≤aᵢ → pinning (eq_of_sum_mul_eq_sum_sq) → bᵢ=aᵢ → (5.4.b)。
3. per-χ `(χ−aη₁)^τ=X₁−aY` → τ₂ direct assembly (S08, hyp.tau↔certain-type τ は supported 上 map-agreement)。
**正本=本 cont.³⁷。τ-seam 核心解決。次=μ_j CharacterPsiDecomposition (ofProjection 組立、orthogonality
inputs + ZIrr membership 供給; S08 で η₁ context)。**

## 2026-06-14 (session 40 cont.³⁸, /loop): ✅ μ_j CharacterPsiDecomposition landed → R(χ) 統合の building blocks 全完備

### ✅ landed (0987d047, axiom-clean 標準3, leaf 3601, **一発 build**):
**`certainTypeDecompositionDa`** (S06_CertainTypeCoherence): reducible μ_j 用 per-constituent
`CharacterPsiDecomposition τ (columnSum χ₂) (a•η₁)` (decompositionDaFromDadeOfDiff の reducible 版)。
`certainTypeR` + `ofProjection` + 前 cont.³⁷ の generic inner-preservation。⟨μ_j,μ̄_j⟩=0 は
columnSum_conj_eq+columnFamily_mu_sum_inner で内部導出; Y-anchor inputs (μ_j−a•η₁ supported/∈ZIrr,
μ_j,μ̄_j⊥a•η₁) は parameter (S08 assembly site で供給)。

### 🎉🎉 マイルストン: R(χ) 統合の building blocks 全完備:
| piece | status |
|---|---|
| 既約 χ R(χ) + Da | ✅ dadeOrthonormalCharacterImageFamilyOfDiff + decompositionDaFromDadeOfDiff (既存) |
| reducible μ_j R(μ_j) + Da | ✅ certainTypeR (cont.³⁶) + certainTypeDecompositionDa (本 cont.³⁸) |
| τ-seam (generic inner-preservation) | ✅ ..._of_data (cont.³⁷) |
| (5.4.a) ‖X‖²≥‖χ‖² | ✅ inner_self_chi_re_le_inner_self_X (既存) |
| pinning ∑aᵢbᵢ=∑aᵢ²⟹bᵢ=aᵢ | ✅ eq_of_sum_mul_eq_sum_sq (cont.³²) |
| (5.4.b) ‖Y‖²≥‖ψ‖²⟹X=∑E | ✅ norm_eq_and_X_eq_sum_of_norm_Y_ge (既存) |
| αᵢ aggregate ∑aᵢαᵢ=Ind−\|H:Z\|η₁ | ✅ sum_smul_constituent_diff_eq (cont.³¹) |

### ▶ 残 = (6.8.2.3) per-χ assembly (S08, building blocks の組立):
⚠ retarget engine (`retarget_isCoherent_of_decomposition*`) は **`⟨χ,χ⟩=1` (既約) 要求** ⟹ reducible μ_j
不適。reducible per-χ は **手動 (5.4.a)+pinning+(5.4.b)** で:
1. per-constituent χᵢ で Da (既約/reducible 振り分け) → αᵢ^τ=Xᵢ−Yᵢ (Da.X/Da.Y) → Yᵢ を Y 方向に分解
   (bᵢ=⟨Yᵢ的, Y⟩, Zᵢ⊥Y) → (5.4.a) で bᵢ²≤aᵢ² ⟹ bᵢ≤aᵢ。
2. pinning (∑aᵢbᵢ=|H:Z|=∑aᵢ², eq_of_sum_mul_eq_sum_sq) ⟹ bᵢ=aᵢ。
3. (5.4.b) ⟹ αᵢ^τ=Xᵢ−aᵢY → χ=χ₁ で per-χ `(χ−aη₁)^τ=X₁−aY`。
4. τ₂ direct assembly (S08; hyp.tau↔certain-type τ は supported map-agreement)。
**hard seam 残**: Yᵢ の Y 方向分解 (bᵢ 抽出) + (6.8.2.2) の Y 同定 + τ₂ 構成。intricate な S08 統合。
**正本=本 cont.³⁸。building blocks 全完備 (大マイルストン)。次=(6.8.2.3) per-χ assembly (5.4.a/b+pinning
を Da から組む; Yᵢ の Y-成分 bᵢ 抽出が次の seam)。**

## 2026-06-14 (session 40 cont.³⁹, /loop すぐ再開): ✅ per-constituent bound の核心 (CS-via-Pythagoras) landed

### 精査: per-χ assembly の bᵢ bound は CS が要だが ClassFunction.inner に CS/正定値は未整備 →
正定値 `inner_self_re_nonneg` (ZIrrFourier:177) は**有**。⟹ bᵢ²≤‖Da.Y‖² を **explicit Pythagoras**
(Da.Y=bᵢ•Y+W, Y⊥W) で証明可 (一般 CS 不要)。

### ✅ landed (52257101, axiom-clean 標準3, leaf 3625):
**`inner_Y_coeff_sq_le`** (S08_CaseBCoherence2): `b=⟨D.Y,Y⟩` (整数, norm-1 Y) ⟹ `(b:ℝ)²≤‖D.Y‖².re`。
Pythagoras: D.Y=b•Y+W, ⟨Y,W⟩=⟨W,Y⟩=0 (b 実数 ∵ inner_conj_symm+star_intCast), ‖D.Y‖²=b²+‖W‖²≥b²
(inner_self_re_nonneg)。gotcha: **`inner_conj_symm φ ψ` の subject は第2引数** (`inner_conj_symm D.Y Y :
Y.inner D.Y = star (D.Y.inner Y)`)。`inner_smul_right` は `RepresentationTheory.` 修飾要。

### ▶ 残 per-constituent bound + per-χ assembly:
1. **bᵢ≤aᵢ** (follow-up, 易): inner_Y_coeff_sq_le + (5.6.2)`inner_self_Y_re_le_inner_self_psi`
   (‖Da.Y‖²≤‖ψ‖²=a², ψ=a•η₁) ⟹ bᵢ²≤aᵢ² → 整数 bᵢ≤aᵢ (b²≤a² ∧ a≥0 ⟹ b≤a の整数 tail)。
2. per-χ assembly: 各構成子で Da (既約=decompositionDaFromDadeOfDiff / reducible=certainTypeDecompositionDa)
   → αᵢ^τ=Da.X−Da.Y, bᵢ=⟨Da.Y,Y⟩, (1.) で bᵢ≤aᵢ → pinning (eq_of_sum_mul_eq_sum_sq, ∑aᵢbᵢ=|H:Z|=∑aᵢ²)
   ⟹ bᵢ=aᵢ → (5.4.b)`norm_eq_and_X_eq_sum_of_norm_Y_ge` ⟹ αᵢ^τ=Xᵢ−aᵢY → per-χ `(χ−aη₁)^τ=X₁−aY`。
3. τ₂ direct assembly (S08)。
**hard seam 残**: bᵢ=⟨Da.Y,Y⟩ と Da.Y の関係 (Da.X⊥Y? Da.Y=αᵢ^τ−Da.X), pinning への ∑ 接続, (5.4.b)
適用, τ₂。intricate な S08 統合だが building blocks + CS core 揃い。
**正本=本 cont.³⁹。CS core landed。次=bᵢ≤aᵢ follow-up (整数 tail) → per-χ assembly (pinning 接続)。**

## 2026-06-14 (session 40 cont.⁴⁰, /loop): ✅✅ (6.8.2.2)→(6.8.2.3) **代数 toolkit 完備** (4 commits)

### ✅ landed (S08_CaseBCoherence2, 全 axiom-clean 標準3, leaf 3625):
| commit | lemma | 内容 |
|---|---|---|
| `dffa9e35` | `inner_Y_coeff_le_of_psi_nsmul` | per-step bound **bᵢ≤aᵢ** = CS core `inner_Y_coeff_sq_le` (b²≤‖Da.Y‖²) + (5.6.2)`inner_self_Y_re_le_inner_self_psi` (‖Da.Y‖²≤‖a•η‖²=a²) + 整数 tail (by_contra+nlinarith, ψ=`a•η` nsmul a:ℕ, η norm-1) |
| `f350e063` | `sum_coeff_eq_of_aggregate` | pinning 入力 **∑aᵢbᵢ=n**: 集約恒等式 `Xagg−n•Y=∑aᵢ•(Xᵢ−Yᵢ)` に ⟨·,Y⟩ (全 X⊥Y, bᵢ=⟨Yᵢ,Y⟩) ⟹ −n=−∑aᵢbᵢ。`inner_sum_left`+`Finset.sum_neg_distrib`+`neg_injective`+exact_mod_cast |
| `671b4555` | `eq_smul_of_inner_self_eq` | **Yᵢ=aᵢ•Y bridge** (CS-equality⟹parallel): ⟨v,w⟩=a ∧ ‖v‖²=a² ∧ ‖w‖²=1 ⟹ v=a•w (‖v−aw‖²=0 を simp[inner lemmas]+ring → `eq_zero_of_inner_self_re_eq_zero`) |
| `bc436213` | `tau_sum_smul_image` | 集約 τ-image **τ(∑aᵢαᵢ)=∑aᵢ(Xᵢ−Yᵢ)** (純 ℤ-線形, `IntegralCharacterMap=→ₗ[ℤ]`): map_sum+map_zsmul, ℂ-smul を Int.cast_smul_eq_zsmul で ℤ-action 化 |
| `ef18ae2a` | **`per_constituent_Y_eq_smul`** | 🎯 **capstone**: 上記 4 brick + (5.4.b) + CS realness を一本化。per-constituent `Dᵢ:CharacterPsiDecomposition τ χᵢ (aᵢ•η)` + hagg + ∑aᵢ²=n + ⟨Dᵢ.X,Y⟩=0/⟨Xagg,Y⟩=0/⟨Dᵢ.Y,Y⟩=bᵢ∈ℤ ⟹ pinning bᵢ=aᵢ ⟹ ‖Dᵢ.Y‖²=aᵢ² ⟹ **Dᵢ.Y=aᵢ•Y**。concrete 側は named 仮説を discharge するだけ (代数再導出不要) |
| `7ed268cb` | `inner_X_Y_eq_zero_of_orthogonal` | seam-1 **⟨Dᵢ.X,Y⟩=0** wrapper: `∀α∈R(χᵢ),⟨Y,α⟩=0` (= (5.3)/(5.5) disjointness, e.g. Y=ε·ξ∧ξ∉R) ⟹ via `inner_X_eq_zero_of_orthogonal_imageSet`+conj-symm。capstone の `hXorth` 入力そのもの |

### ✅ 原文 (6.8.2.3) 精読確定 (本 session, 04.8 mmd:208-222): **私の framing は原文と完全一致**
- 原文 `αᵢ^τ=Xᵢ−bᵢY+Zᵢ` (Xᵢ∈ℤ[R(χᵢ)], Zᵢ⊥R(χᵢ)∧⊥Y) ⟺ 私の `Dᵢ.X=Xᵢ`, **`Dᵢ.Y=bᵢY−Zᵢ`**。
  `⟨Dᵢ.Y,Y⟩=bᵢ` (∵ Zᵢ⊥Y, ‖Y‖²=1) = capstone の bᵢ。capstone 結論 `Dᵢ.Y=aᵢ•Y` = 原文「Zᵢ=0 ⟹ αᵢ^τ=Xᵢ−aᵢY」。
- 構成子 index = `θᵢ∈Irr H` (Ind^H_Z φ=∑aᵢθᵢ, χᵢ=Ind^L_H θᵢ, aᵢ=θᵢ(1)=⟨φ,Res θᵢ⟩); χ=χ₁=Ind^L_H θ。
- 集約 `Ind^L_Z φ−|H:Z|η₁=∑aᵢαᵢ` ∧ `∑aᵢ²=|H:Z|` = `sum_smul_constituent_diff_eq` 既存 (θ:Irr H 全体, 非構成子 aθ=0)。
- seam-1「R(χᵢ)⊥Y^τ₁」= **(5.3)+(5.5)** の帰結 (原文明記)。

### 🎉🎉 マイルストン: (6.8.2.3) **pinning→image の代数 layer 全完備**。連鎖:
```
tau_sum_smul_image + sum_smul_constituent_diff_eq(∑aᵢαᵢ=Indφ−n•η₁) + exists_decomposition_caseB(τ(…)=Xagg−n•Y)
   → hagg : Xagg−n•Y = ∑aᵢ(Xᵢ−Yᵢ)
sum_coeff_eq_of_aggregate(hagg + ⟨Xᵢ,Y⟩=0 + bᵢ=⟨Yᵢ,Y⟩ + ⟨Xagg,Y⟩=0 + ‖Y‖²=1) → ∑aᵢbᵢ=n
sum_inner_restrict_sq_eq_index → ∑aᵢ²=n;  inner_Y_coeff_le_of_psi_nsmul → bᵢ≤aᵢ
eq_of_sum_mul_eq_sum_sq → bᵢ=aᵢ
(5.4.b)norm_eq_and_X_eq_sum_of_norm_Y_ge(‖Yᵢ‖²=aᵢ²) + eq_smul_of_inner_self_eq → Yᵢ=aᵢ•Y ∧ Xᵢ=∑_E α
   → per-i αᵢ^τ=Xᵢ−aᵢ•Y → per-χ (χ−a•η₁)^τ=X₁−a•Y
```

### 🔑 RECON 確定 (本 session の構造把握):
- **(6.8.2.3) = `hmixed` obligation** (`coherentXunionYset_caseB_of_glued` の field): `⟨ν μ_j, ν η⟩=⟨μ_j,η⟩`
  (=0 ∵ μ_j⊥η)。per-χ image `(χ−a•η₁)^τ=X₁−a•Y` (X₁⊥Y) が `⟨(μ_j)^{τ₂},Y⟩` 計算の核。
- **seam 1「⟨Da_i.X,Y⟩=0」は新 hard math 不要** = 既存**抽象** `inner_decomposition_X_extension_member_eq_zero`
  (S08_CoherenceCorePart1:1546, `{τ:IntegralCharacterMap L G}` 汎用) で discharge 可能。要 input =
  η₁ の **member 分解 D'** (ψ=0, `D'.tau1 η₁=cY.extension η₁`) + **R(η₁)⊥R(μ_j)** (imageFamily.Orthogonal)。
- **per-constituent framing が正**: i = `Ind^H_{W₂}φ` の既約構成子 θᵢ (一部 reducible μ_j)。各 χᵢ に Da_i
  (既約=decompositionDaFromDadeOfDiff / reducible=certainTypeDecompositionDa)。pinning が i を束ねる。
- **τ=Da_i.tau1 は certain-type で literally 同一** (htau1_agrees:=rfl) ⟹ `Da_i.tau1_image` がそのまま `τ(αᵢ)=Xᵢ−Yᵢ`。

### ▶ 残 = **concrete S08 instantiation** (代数 layer は capstone まで完備; 残りは case-B データへの wiring):
capstone `per_constituent_Y_eq_smul` が要求する named 仮説を case-B で discharge するだけ:
1. **構成子 index s + per-i Da family** 構築 (multiplicities aᵢ=⟨φ∘e,Res θᵢ⟩, χᵢ=Ind^L_H θᵢ;
   既約=`decompositionDaFromDadeOfDiff` / reducible μ_j=`certainTypeDecompositionDa`)。
2. **hagg 集約恒等式** = `tau_sum_smul_image` (per-i `τ(αᵢ)=Da_i.X−Da_i.Y` from `Da_i.tau1_image`,
   tau1=τ literally) + `sum_smul_constituent_diff_eq` (∑aᵢαᵢ=Indφ−|H:Z|η₁) +
   `exists_decomposition_caseB` (τ(Indφ−|H:Z|η₁)=Xagg−|H:Z|•Y)。
3. **seam-1「⟨Da_i.X, Y⟩=0」** — 🔑 **大幅単純化** (本 cont.⁴⁰ RECON):
   `coherentYset_extension_eq_zsmul_irreducible` (S08_CaseBCoherence:450) ⟹ **Y=cY.extension η₁=ε•ξ**
   (ξ = **単一既約** ∈ Irr G, ε=±1)。∴ `⟨Da_i.X, Y⟩ = ε̄·⟨Da_i.X, ξ⟩`、Da_i.X∈ℤ[R(χᵢ)] ⟹
   **ξ∉R(χᵢ) (image family 非所属) なら distinct-irreducible 直交で 0**。要 = ξ∉R(χᵢ) の disjointness
   (Y 側 image ξ と X 側 R(χᵢ) は別ソース ⟹ 別既約)。member 分解ルート (`inner_decomposition_X_extension_member_eq_zero`)
   も可だが zsmul-irreducible 経由が直接的。⟨Xagg,Y⟩=0 は exists_decomposition_caseB が直接供給。
4. **integrality `⟨Da_i.Y, Y⟩=bᵢ∈ℤ`** = Da_i.Y∈ZIrr (Da_i.X∈ℤ[R]⊆ZIrr ∧ τ-image∈ZIrr) ∧ Y=ε•ξ∈ZIrr
   ⟹ `inner_mem_ZIrr_int`。
5. capstone ⟹ per-i `Da_i.Y=aᵢ•Y`。→ per-χ image `(μ_j−a•η₁)^τ=X₁−a•Y` (X₁=Da_{j}.X⊥Y) →
   **hmixed** `⟨(μ_j)^{τ₂}, Y⟩=⟨μ_j,η⟩=0` → `coherentXunionYset_caseB_of_glued`。
**hard 寄り = 3 の disjointness ξ∉R(χᵢ) (要 Y-image vs X-R-family 別既約の論証) と 5 の hmixed 最終 wiring。**

### ▶▶ 抽象 toolkit 出尽くし (7 lemma: 5 pinning + tau_sum_smul_image + seam-1 wrapper, 全 axiom-clean)。
残りは**全て case-B concrete instantiation** (S06/S08, capstone の named 仮説を discharge):
- **次の concrete brick = per-θ Da family** (各 θ:Irr H, aθ>0 で χθ=Ind^L_H θ の `Dθ:CharacterPsiDecomposition τ (χθ) (aθ•η₁)`)。
  χθ が既約=`decompositionDaFromDadeOfDiff` / reducible(column μ_j)=`certainTypeDecompositionDa`。要 = ZIrr membership +
  support 条件 + orthogonality inputs の per-θ 供給 (case-B hypothesis 構造の精査が必要)。
- 並行 = **disjointness R(χθ)⊥Y** ((5.3)+(5.5); Y=ε·ξ ⟹ ξ∉R(χθ); irreducible 版 `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`
  の case-B/certain-type 類似が要るか精査)。
**正本=本 cont.⁴⁰。代数 layer 完備。次 tick=per-θ Da family の case-B 構造精査 → 構築。組立は capstone で機械的。**

## 2026-06-14 (session 40 cont.⁴¹, /loop): 🔎 concrete instantiation の gap 精査 — disjointness が本丸

### 確認した既存資産 (S06):
- `certainTypeR` = R(μ_j) OrthonormalCharacterImageFamily (S06:639, χ₂≠1, hdeg)。imageSet=`certainTypeRImage` の像
  (`±δ_j•certainTypeOmegaSigma`)、`(μ_j−μ̄_j)^τ=∑R(μ_j)` = `dadeICM_columnDiff_eq_sum`。
- `certainTypeRImage_inner` = R(μ_j) **内部**の orthonormality のみ。
- `certainTypeDecompositionDa` (S06:684) = μ_j 用 Da、Y-anchor inputs (η₁,a,support,ZIrr,⊥) は parameter。

### 🛑 gap 確定: **disjointness `R(μ_j) ⊥ Y^τ₁` の既存サポート無し**
- (6.8.2.3) 原文「R(χᵢ)⊥Y^τ₁ by (5.3),(5.5)」を分解: Y^τ₁=η₁^τ₁∈ℤ[R(η₁)] ((5.5)) ∧ **R(χᵢ)⊥R(η₁)** ((5.3),
  source χᵢ⊥η₁ からの image-family 直交) ⟹ R(χᵢ)⊥Y。
- irreducible 版 = `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal` (source⊥ ⟹ R⊥R)。
- **case-B では R(μ_j)=certainTypeR が σ-image 経由の別構成**ゆえ、`⟨certainTypeOmegaSigma h χ₂ i, ξ⟩=0`
  (ξ=Y-anchor image) を与える既存 lemma 無し (grep 済: certainTypeOmegaSigma_inner は族内部のみ)。
  ⟹ **certain-type R(μ_j) ⊥ R(η₁) (or ⊥ Y-side ξ) を新規に確立する必要** = concrete instantiation の本丸 gap。

### ▶ 残 concrete instantiation の構造 (capstone は全部 ready, 以下が plumbing):
1. **disjointness `R(μ_j)⊥Y`** [本丸 gap]: certainType σ-image vs Y-side の直交。source μ_j⊥η₁ (既: hpair) +
   Dade/σ の直交保存。要新規 infra (certainType 版 (5.3))。**次の主作業**。
2. per-θ Da family + character setup (Ind^H_Z φ=∑aᵢθᵢ; χθ 既約/reducible 振分)。
3. aggregate (6.8.2.2) wiring + capstone 適用 → per-χ image → hmixed。
**評価: 代数 layer (7 lemma+capstone) は完全完成・全 axiom-clean = 本 session の主成果。残りは case-B 固有の
plumbing で、本丸 = disjointness の新規 infra。これは focused な dedicated 作業 (quick brick でない)。**
**正本=本 cont.⁴¹。次 tick=disjointness `R(μ_j)⊥Y` の新規 infra 着手 (certainType σ-image vs Y-side 直交)。**

## 2026-06-14 (session 40 cont.⁴², /loop): 🛑 disjointness の機構精査 — 2-element machinery 不適、深い gap 確定

### irreducible 版機構 (`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`, S08p1:1681) の精読:
`R(x).Orthogonal R(χ)` を source 直交から導く経路 =
`toOrthonormalImage_orthogonal` ∘ `orthogonal_of_signedDifference_inner_eq_zero`
((5.2.e): `⟨τ(x−x̄),τ(χ−χ̄)⟩=0` ⟹ per-member 直交) ∘ `inner_dadeDiff_conjDifference_eq_zero`
(Dade 等長: source `⟨x−x̄,χ−χ̄⟩=0` ⟹ image 直交)。

### 🛑 certainType への非適用性 (確定):
- `orthogonal_of_signedDifference_inner_eq_zero` は **2-element `CharacterDifferenceImage` {μ,ν} 専用**
  (signed difference が ±符号で 2 member を encode、norm-1 + 差の直交で per-member を pin)。
- **certainTypeR は `Bool × Fin w₁` = 2w₁-member 族** (σ-image 経由) ⟹ この 2-element 機構が**直接適用不可**。
  per-member `⟨certainTypeOmegaSigma h χ₂ i, ξ⟩=0` (ξ=Y-anchor 既約) は `∑α=(μ_j−μ̄_j)^τ` の sum-level
  からは出ない (per-member ≠ sum)。
- ⟹ **σ-construction の大域直交性** (σ-image 既約 と Y-coherence 既約 が別既約) を新規に要する。
  これは §5 σ の image 特徴付け (chiFam の source/support) に踏み込む深い infra。

### 📊 honest 評価 (要判断ブロッカー):
- **本 session の主成果 = (6.8.2.3) 抽象 toolkit (7 lemma + capstone) 完全完成・全 axiom-clean** (大マイルストン)。
- concrete instantiation の残り 3 piece (character setup / disjointness / hmixed) は**いずれも §5/§6 の
  sustained な深い作業**で、quick brick でない。特に **disjointness が本丸 deep gap** (上記)。
- ここ ~3 tick RECON が続き concrete brick が land していない ⟹ 60s loop tick (context reload) は
  この深い infra 作業に非効率。**dedicated focused session が適切**。
**正本=本 cont.⁴²。次の主作業 = disjointness の σ-construction 大域直交 infra (深い、§5 chiFam 特徴付け要)
or character setup ([Is]2.27 + Ind 分解)。abstract layer は完成済みゆえ、これら infra が揃えば組立は capstone で機械的。**

## 2026-06-14 (session 40 cont.⁴³, /loop「ChatGPT 想起」): ✅✅ 訂正 — disjointness は深い gap で**なかった** (reconstruction gap 誤判定)

### 🔑 cont.⁴² の「深い σ infra 要」verdict は **誤判定** (BG 13.4 と同じ reconstruction-gap 誤認)。
ユーザーの「ChatGPT に聞ける」想起に促され (5.3.b) の**証明本体**を読みに行き、再構成を発見 (ChatGPT 不要、原文に証明あり)。

### (5.3.b) 証明 (04.7 mmd:29) = disjointness の正しい論法:
> φ∈S∩Irr(L) ⟹ (4.7) で Supp(φ−φ̄)⊆A ⟹ **(φ−φ̄)^τ は V 上で消える** (τ 定義, A∩V=∅) ⟹
> NC((φ−φ̄)^τ)≤‖φ−φ̄‖²=2 ⟹ **(3.8)** で R(φ)⊥ω^σ (∀ω∈Irr W)、特に ⊥R(μ_j)。

### ✅ 全ツール既存 (新規 infra 不要):
| piece | lemma | 場所 |
|---|---|---|
| (3.8) trichotomy | `sigmaCoeff_trichotomy` / `grid_trichotomy` | S05_SigmaTrichotomy / S05_GridTrichotomy |
| **NC<min⟹全係数0** (今回はこれで足る) | **`grid_eq_zero_of_ncard_support_lt`** (session 18 landed) | S05_SigmaIsometry:101 |
| vanish-on-V ⟹ ⊥σ-image | `inner_sigma_eq_zero_of_vanishOnV` | S05_SigmaIsometry:1354 |
| ⊥chiFam ⟹ vanish-on-V | `eq_zero_of_mem_V_of_inner_chiFam_eq_zero` / `vanishOnV_of_inner_alphaCF` | S05:1234/1144 |
| R(μ_j)⊆σ-images | `certainTypeRImage` (式27: {±δ ω_{ij}^σ}) | S06 |

### 🔑 簡略化: **full (3.8) trichotomy すら不要**。NC((η₁−η̄₁)^τ)≤2、min(w₁,w₂)≥3 (奇位数, w₁,w₂ は奇素数 Hall)
⟹ `grid_eq_zero_of_ncard_support_lt` (NC<min⟹全 σ-係数 0) で R(η₁)⊥σ-images が出る。

### ▶ disjointness 形式化レシピ (capstone hXorth `⟨Da_i.X,Y⟩=0` 向け):
`⟨Y, certainTypeOmegaSigma h χ₂ i⟩=0` (Y=cY.extension η₁, certainTypeOmegaSigma=ω^σ):
1. η₁∈Yset ⟹ 既約 (`isIrreducibleCharacter_of_mem_Yset`)。
2. (η₁−η̄₁)^τ が V 上消失 (η₁ A-supported difference, (4.7)+τ 定義)。
3. NC((η₁−η̄₁)^τ)≤2<min(w₁,w₂) ⟹ `grid_eq_zero_of_ncard_support_lt` ⟹ (η₁−η̄₁)^τ⊥σ-images。
4. R(η₁) members = (η₁−η̄₁)^τ の既約構成子 ⟹ ω^σ∉R(η₁) ⟹ ω^σ⊥R(η₁) members ⟹ ω^σ⊥η₁^τ₁=Y。
   (or 直接 Y vanishes on V → `inner_sigma_eq_zero_of_vanishOnV`)。
**正本=本 cont.⁴³。disjointness は tractable な多段再構成と確定 (深い infra 不要)。option 1 = 正解。次=形式化着手。**

## 2026-06-14 (session 40 cont.⁴⁴, /loop): ✅ route を大幅 clean 化 (zsmul-irreducible で R(η₁) 構成回避) + ピース確認

### 🔧 訂正 (cont.⁴³ の細部): `omega(χ)` は W の**既約指標** (linearIrreducibleCharacter, NOT V-supported)
⟹ `certainTypeOmegaSigma = sigma(omega)` は **V^G-supported でない** ⟹ disjoint-support 経由 (inner_sigma_eq_zero_of_vanishOnV) は**不可**。**(3.8)/grid_eq_zero 経由が必須**。

### ✅✅ clean route 確定 (R(η₁) 構成不要):
`coherentYset_extension_eq_zsmul_irreducible` (S08:450) で **Y=cY.extension η₁ = ε·ξ** (ξ 単一既約)、
同様 cY.extension η̄₁ = ε'·ξ' (ξ' 既約)。η₁ 非実 (5.2.a) ⟹ ξ≠ξ'。
1. (η₁−η̄₁)^τ = ε·ξ − ε'·ξ' (cY.extends_on_supported + 線形; η̄₁∈Yset は共役閉)。
2. **anchor**: (η₁−η̄₁)^τ が V 上消失 (η₁−η̄₁ A-supported [(4.7)], τ=Dade map, A^G∩V=∅)。【要 Dade-support ピース確認】
3. NC((η₁−η̄₁)^τ)≤2 (= ε·ξ−ε'·ξ' の σ-係数は ξ=chiFam or ξ'=chiFam の高々2点)。min(w₁,w₂)≥3 (奇素数 Hall)。
4. `grid_eq_zero_of_ncard_support_lt` (a:=sigmaCoeff, hadd:=`sigmaCoeff_add_eq`[要 anchor の vanishOnV], hlt:=NC<min)
   ⟹ ∀pq, ⟨(η₁−η̄₁)^τ, chiFam pq⟩=0。
5. **整数性抽出**: ε·⟨ξ,chiFam⟩−ε'·⟨ξ',chiFam⟩=0、⟨ξ,chiFam⟩,⟨ξ',chiFam⟩∈ℤ (ZIrr) ∧ |·|≤1 (norm-1, Pythagoras
   = `inner_Y_coeff_sq_le` 流) ∧ ξ≠ξ' ⟹ ⟨ξ,chiFam⟩=0。
6. ⟹ ⟨Y, certainTypeOmegaSigma⟩ = ⟨ε·ξ, chiFam⟩ = ε̄·0 = 0 = seam-1 hXorth。

### ✅ ピース status:
| piece | lemma | status |
|---|---|---|
| Y=ε·ξ 単一既約 | `coherentYset_extension_eq_zsmul_irreducible` (S08:450) | ✅ 既存 |
| (3.7) σ-coeff 加法恒等式 | `sigmaCoeff_add_eq` (要 vanishOnV) | ✅ 既存 (S05) |
| grid≡0 (NC<min) | `grid_eq_zero_of_ncard_support_lt` (S05:101) | ✅ session 18 landed |
| 整数性 ⟨ZIrr,ZIrr⟩∈ℤ | `inner_mem_ZIrr_int` | ✅ 既存 |
| |⟨·,·⟩|≤1 (norm-1) | `inner_Y_coeff_sq_le` 流 (Pythagoras) | ✅ 本 session landed |
| anchor: A-supported→vanish on V | 【要確認: certain-type Dade の V-support; fourCornerDade_eq_zero_of_not_mem_conjugatesV 周辺】 | ⚠ 未確認 |

### ▶▶ 次 tick の具体ターゲット (堂々巡り回避):
**sub-lemma 1 = anchor**「η₁∈Yset ⟹ (η₁−η̄₁) の cY/Dade 像が (ticVdiff h).V 上で消失」。
まず `fourCornerDade_eq_zero_of_not_mem_conjugatesV` + `dadeIntegralCharacterMap_apply_of_support` +
A^G∩V=∅ で certain-type Dade 像の V-vanishing を確立。これが取れれば残り (NC/grid/整数抽出) は機械的。
anchor が重い場合は先に sub-lemma 5 (整数性抽出, 純 abstract, certain-type 非依存) を landさせて momentum 維持。
**正本=本 cont.⁴⁴。clean route 確定。次=anchor (sub-lemma 1) 形式化。**

## 2026-06-14 (session 40 cont.⁴⁵, /loop): ✅✅ disjointness の "downstream" 2 brick landed (building 転換)

### ✅ landed (S08_CaseBCoherence2, 全 axiom-clean 標準3, leaf 3625):
| commit | lemma | 役割 |
|---|---|---|
| `547a14b1` | `inner_intCast_sq_le` | `inner_Y_coeff_sq_le` を一般化 (任意 u,w): ⟨u,w⟩=b∈ℤ ∧ ‖w‖²=1 ⟹ b²≤‖u‖²。整数性 |b|≤1 の基盤。呼び出し2箇所更新 (no-wrapper) |
| `05650497` | **`inner_eq_zero_of_smul_sub_smul_orthogonal`** | **sub-lemma 5 (extraction core)**: ξ,ξ' 正規直交 + θ norm-1 + ⟨ξ,θ⟩∈ℤ + c·ξ−c'·ξ'⊥θ (c≠0) ⟹ ⟨ξ,θ⟩=0。`inner_intCast_sq_le`(|·|≤1) + `eq_smul_of_inner_self_eq`(±1⟹ξ=±θ) で。純・certain-type 非依存 |

### ▶ disjointness 残ピース (downstream 完成、残り upstream):
- ✅ **sub-lemma 5 (extraction)** = 上記。「(η₁−η̄₁)^τ=ε·ξ−ε'·ξ' ⊥ chiFam」⟹「⟨ξ,chiFam⟩=0」を変換。
- ⚠ **sub-lemma 1 (anchor)** = 「(η₁−η̄₁)^τ が (ticVdiff h).V 上消失」: Sibley tau 像 (A-supported) vs ticVdiff V の
  構造的 disjointness。**未確認の残ハード piece** (cont.⁴⁴ 確認: 既存 lemma 直接無し)。
- ⚠ **assembly**: Y=ε·ξ (coherentYset_extension_eq_zsmul_irreducible) + ξ≠ξ' (η₁ 非実) +
  (η₁−η̄₁)^τ=ε·ξ−ε'·ξ' (extends_on_supported) + NC≤2 + grid_eq_zero(要 anchor) + extraction → ⟨Y,certainTypeOmegaSigma⟩=0
  → seam-1 hXorth。さらに **map-juggling** (capstone τ=certain-type dade0/h.tau vs Y=Sibley cY.ext;
  hXorth は ⟨(D i).X, Y⟩ で D i.X∈ℤ[σ-images]、Y は抽象 G-function ゆえ map 差は OK だが sigmaCoeff 接続に注意)。
**正本=本 cont.⁴⁵。extraction core landed。次=anchor (sub-lemma 1) の Sibley-V disjointness 構造調査 → 形式化。
anchor が deep なら assembly の other pieces (Y=ε·ξ setup, NC≤2) を先に land。**

## 2026-06-14 (session 40 cont.⁴⁶, /loop): ✅ grid driver landed (3rd disjointness brick) + anchor の深さ確認

### ✅ landed (`6e223bc4`, axiom-clean, leaf 3625):
**`sigmaCoeff_eq_zero_of_vanishOnV_of_ncard_lt`** (S08): ψ vanishOnV + NC<min(w₁,w₂) ⟹ ∀pq sigmaCoeff=0。
`grid_eq_zero_of_ncard_support_lt` + `sigmaCoeff_add_eq`(3.7) + `card_charGroup_subgroupOf`。
full trichotomy 不要 (corollary で足る)。**gotcha**: `FullDadeApplication` = `S05.TICyclicHypothesis.FullDadeApplication`,
`grid_eq_zero_of_ncard_support_lt` = `S05.` 直下 (TICyclicHypothesis 名前空間でない)。

### disjointness ピース status:
| piece | lemma | status |
|---|---|---|
| extraction core | `inner_eq_zero_of_smul_sub_smul_orthogonal` | ✅ `05650497` |
| CS bound \|inner\|≤1 | `inner_intCast_sq_le` | ✅ `547a14b1` |
| **grid driver** (vanishOnV+NC<min⟹全0) | `sigmaCoeff_eq_zero_of_vanishOnV_of_ncard_lt` | ✅ `6e223bc4` |
| NC≤2 (2-irreducible) | — | ⚠ tractable (sigmaCoeff≠0 のみ ξ or ξ'=±chiFam ⟹ ≤2 点) |
| **anchor** (η₁−η̄₁)^τ vanishOnV | — | 🛑 deep 構造: (ticVdiff h).V ∩ conjugatesOfSet(sharpImage H)=∅ (V=W-exceptional vs H^#-conj) 既存無し |
| assembly (sigmaCoeff↔certainTypeOmegaSigma + Y=ε·ξ + 上記) | — | ⚠ multi-step |

### 🛑 anchor 確認 (cont.⁴⁶): V^L⊆A₀=A∪V^L (`coe_mem_A0_of_mem_conjugatesOfSet_toTICV`), V は A と別成分。
anchor「hyp.tau(A-supported) が V 上消失」= V∩conjugatesOfSet(H^#)=∅ (構造的, V=Hall W-exceptional は H-conj と
別素数構造で交わらない)。`centralizer_le_L_of_mem_ticVdiffV` (v∈V⟹C_G(v)⊆L, H(a)=⊥ on V) が基盤候補だが
"A-supported→vanishOnV" 直接 lemma 無し。**anchor = 残る本丸 deep 構造 piece**。
**正本=本 cont.⁴⁶。grid driver landed。次=NC≤2 (tractable, land) → anchor 構造 (deep, V∩H^#-conj=∅) → assembly。**

## 2026-06-15 (session 41, /loop): ✅✅✅ anchor COMPLETE (本丸 deep 構造 piece 解除) — disjointness machine + NC≤2 + anchor 全 landed

### ✅ landed (S08_CaseBCoherence2, 全 axiom-clean 標準3, leaf 3625 / full 3813):
| commit | lemma | 役割 |
|---|---|---|
| `7a62c601`(前session) | `sigmaNC_le_two_of_inner_chiFam` | NC≤2 (2-irreducible difference) — disjointness brick 4 |
| `357558c1` | `inner_smul_chiFam_eq_zero_of_diff_vanishOnV` | **disjointness machine** (anchor 以外の 4 brick 連結): orthonormal ξ,ξ'∈±Irr(G), c≠0, c·ξ−c'·ξ' が V 上消失 ⟹ ⟨c·ξ, chiFam pq⟩=0 |
| `efbfd6af` | **`ticVdiffV_not_mem_conjugatesOfSet_K`** | **anchor group-theoretic core**: v∈(ticVdiff h).V ⟹ v∉conjugatesOfSet(K.map L.subtype)。位数論法 (v=↑(x·y)∈W₁×W₂, v∉W₂⟹x≠1, x=w^n⟹orderOf x∣orderOf v, v~↑k⟹orderOf v=orderOf k∣\|K\|, orderOf x∣gcd(\|K\|,\|W₁\|)=1 [card_coprime] ⟹ x=1 矛盾)。鍵 API: `SemiconjBy.orderOf_eq`, `exists_zpow_proj`, `exists_mul_of_mem_sup`, `Nat.eq_one_of_dvd_coprimes`, `Subgroup.orderOf_mk/coe` |
| `5157bb9d` | **`tau_apply_eq_zero_of_mem_ticVdiffV`** | **anchor 本体**: α supported on H^#=sharpImage H ⟹ hyp.tau α が (ticVdiff h46).V 上消失。`dadeIntegralCharacterMap_apply_of_support`→`map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot` (dade_H_eq_bot) + core lemma + `conjugatesOfSet_mono` (sharpImage H=（K.map)\{1}⊆K.map, via h46.K=H)。α=η₁−η̄₁ で (η₁−η̄₁)^τ が V 上消失 = machine の hvanish |

### 🔑 anchor の構造的洞察 (cont.⁴⁶ の「直接 lemma 無し」を解決):
anchor = V∩conjugatesOfSet(H^#)=∅ は **TI 還元不要**。位数論法が clean: K=H ゆえ orderOf(a∈H^#)∣\|K\|、v∈V は W₁-成分非自明ゆえ orderOf(W₁-part)∣gcd(\|K\|,\|W₁\|)=1 で矛盾。`card_coprime` (Hypothesis46 固有) が効く。`centralizer_le_L_of_mem_ticVdiffV` は不要だった。

### ▶▶ 次 = **assembly** (seam-1 hXorth = ⟨Y, certainTypeOmegaSigma⟩=0)。ルート全特定:
1. Y = coherentYset.extension η₁ = ε•ξ (`coherentYset_extension_eq_zsmul_irreducible`, ε=±1, ξ∈Irr G)。同様 η̄₁↦ε'•ξ'。
2. (η₁−η̄₁)^τ = ε•ξ−ε'•ξ' via `coherentYset.extends_on_supported` (η₁−η̄₁∈ℤ[Yset,H^#])。
3. Supp(η₁−η̄₁)⊆H^#: `support_sub_induce_subset_sharpImage_of_apply_one_eq` (η₁=Ind θ, η̄₁=Ind θ̄ 両 degree \|W₁\|)。
4. ξ≠ξ': η₁ 非実 (5.2.a ⟹ η₁≠η̄₁) ⟹ extension 経由 ξ≠ξ' [要 lemma 発掘]。
5. anchor (`tau_apply_eq_zero_of_mem_ticVdiffV`, α=η₁−η̄₁): ε•ξ−ε'•ξ' が (ticVdiff h46).V 上消失。
6. machine (`inner_smul_chiFam_eq_zero_of_diff_vanishOnV`, hyp=ticVdiff h46, hVeq=rfl, app=ticVdiffFullDadeApplication, hmin: 2<min(w₁,w₂)): ⟨ε•ξ, chiFam pq⟩=0。
7. `certainTypeOmegaSigma_eq_chiFam`: certainTypeOmegaSigma=chiFam(omegaProdEquiv.symm…) ⟹ ⟨Y, certainTypeOmegaSigma⟩=⟨ε•ξ, chiFam⟩=0。
→ hXorth → `per_constituent_Y_eq_smul` → case-B X-coherence (`coherentXunionYset_caseB_of_glued`) → capstone `sibleySetup_is_coherent` X-nonempty branch (S08_CoherenceTheorems:59 sorry)。
**要発掘: (4) ξ≠ξ' (η非実→image distinct)、(3) η₁=Ind θ 抽出、hmin (奇素数 Hall ⟹ w₁,w₂≥3 だが 2<min 要確認)。**
**正本=本 session 41。anchor 完成。次=assembly seam-1。Opus 継続。**

### ✅✅✅ session 41 cont. (/loop): seam-1 完成 — (6.8.2.3) disjointness/直交性の全数学内容 DONE
| commit | lemma | 役割 |
|---|---|---|
| `4d182ec9` | `coherentYset_extension_diff_apply_eq_zero_of_mem_ticVdiffV` | anchor Y-image 形: η,η'∈Y で extension η − extension η' が V 上消失 (extends_on_supported + anchor)。全 Y 元 degree=|W₁| ゆえ Supp(η−η')⊆H^# (`sMember_diffSupport_of_charValue_eq`) |
| `66362a01` | **`inner_coherentYset_extension_certainTypeOmegaSigma_eq_zero`** | **seam-1 直交性**: η≠η'∈Y で ⟨extension η, certainTypeOmegaSigma h46 χ₂ i⟩=0。η^{τ₁}=ε•ξ/η'^{τ₁}=ε'•ξ' (`coherentYset_extension_eq_zsmul_irreducible`)、⟨ξ,ξ'⟩=0 (isometry+⟨η,η'⟩=0 [`irreducibleCharacter_inner_eq_ite`])、ε•ξ−ε'•ξ' V上消失 (Y-image anchor)、machine + `certainTypeOmegaSigma_eq_chiFam`。**🔑 (4) ξ≠ξ' 別証不要 — ⟨ξ,ξ'⟩=0 を isometry+共役で直接抽出 (zsmul→ℂ-smul: `Int.cast_smul_eq_zsmul`, `inner_smul_left/right`, `star_intCast`)** |
| `70841fe0` | **`inner_coherentYset_extension_certainTypeRImage_eq_zero`** | **seam-1 R(μ_j) 形**: ⟨extension η, certainTypeRImage h46 χ₂ χ₂' p⟩=0。R(μ_j)各元=符号付き certainTypeOmegaSigma ⟹ seam-1×2 (χ₂/χ₂', cases Bool)。これが hXorth の全材料 |

### 🎯 (6.8.2.3) disjointness COMPLETE。次 = per_constituent 適用 + case-B X-coherence + capstone glue
**hXorth (`⟨Da.X, Y⟩=0`) は capstone で one-liner 化可能 (確認済)**:
`(certainTypeDecompositionDa …).imageFamily = certainTypeR h hχ₂ hdeg` (`ofProjection` が imageFamily 保存, S07:1199) ⟹ `.imageFamily.imageSet = univ.image (certainTypeRImage h χ₂ χ₂⁻¹)`。
```
inner_X_Y_eq_zero_of_orthogonal Da (fun α hα => by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hα
  exact inner_coherentYset_extension_certainTypeRImage_eq_zero hyp h46 hHK hη hη' hne χ₂ χ₂⁻¹ p)
```
**▶▶ 次の大ステップ (capstone X-nonempty branch, S08_CoherenceTheorems:59 sorry)**:
1. **per_constituent 適用**: `per_constituent_Y_eq_smul` に D(family)/hagg((6.8.2.2) aggregate, cont.³⁰-³¹ 済?)/hsq(∑aᵢ²=n)/hXorth(上記)/hbi/hYY を供給 ⟹ Dᵢ.Y=aᵢ•Y ⟹ (6.8.2.3) 結論 `(χ−aη₁)^τ=X₁−aY`。
2. **case-B X-coherence** (`coherentXunionYset_caseB_of_glued`): cX (= certainTypeSet_isCoherent_tau + X_irr glue)/ν/hagree/hpair/hmixed/D/hgen 供給。
3. **capstone glue**: hyp.cases (Frobenius/CertainType 分割) + ν 構成 + Y-coherence と glue。
**要: η̄₁∈Y 共役閉包 (capstone で η'=η̄₁ 用; `induce_linearIrreducibleCharacter_mem_Yset` + 共役 linear χ⁻¹≠1)。または \|Y\|≥2 で任意の η'≠η₁。**
**正本=本 session 41 cont。(6.8.2.3) 全直交性 DONE (7 commits)。次=per_constituent 適用。full build 3813 green。Opus 継続。**

### ✅ session 41 cont.² (/loop): hXorth が capstone-ready 形に完成 (2 commits)
| commit | lemma | 役割 |
|---|---|---|
| `a88c3a5f` | `inner_decomposition_X_coherentYset_extension_eq_zero` | hXorth (generic D + coverage himg): `⟨D.X, η^{τ₁}⟩=0` (η≠η')。coverage 形 `∀ α∈imageSet, ∃ p, certainTypeRImage…p=α` で DecidableEq 回避 |
| `ca7f5fe8` | **`inner_decomposition_X_coherentYset_extension_eq_zero_of_mem_Yset`** | **hXorth capstone 形 (η₁∈Y のみ)**: distinct η'=η̄₁ を内部化。`Yset_closedUnderConjugate` (η̄₁∈Y) + `Yset_hasNoRealCharacters` (η₁≠η̄₁, (5.2.a))。**enabler 全既存確認** |

### 🔑 distinct η' の enabler は全既存 (再調査不要):
- `Yset_closedUnderConjugate : ClosedUnderConjugate hyp.Yset` (S08_CoherenceCorePart2:1447) — η.conj∈Y
- `Yset_hasNoRealCharacters` (:1421) + `HasNoRealCharacters.not_mem_of_isReal` (S03:82) — η≠η.conj
- `two_le_Yset_ncard` (:1478) — |Y|≥2 も既存
⟹ **hXorth は η₁∈Y だけで供給可能。capstone は他の per_constituent 入力 (family/aggregate) のみ残す。**

### ▶▶ 次 = per_constituent 適用 ((6.8.2.3) 結論 `(μ_j−aη₁)^τ=X₁−aY`):
`per_constituent_Y_eq_smul` の入力:
- **D (family)**: constituent θ∈Irr H で χθ=induce H θ、Dθ=各 (5.4) 分解 (`certainTypeDecompositionDa` は columnSum 用; θ-family は要精査 — μ_j 列 vs 一般 θ の対応)。
- **hagg**: `tau_sum_smul_image` + `sum_smul_constituent_diff_eq` (∑aθαθ=Ind φ−|H:Z|η₁, S08:566 証明済) + `exists_decomposition_caseB` (S08:126, τ(Ind φ−|H:Z|η₁)=Xagg−|H:Z|Y)。
- **hsq**: ∑aθ²=n=|H:Z| (`sum_inner_restrict_sq_eq_index`, S08:537)。
- **hXorth**: ✅ 上記 capstone 形。
- **hbi/hYY/hXaggorth**: 整数性 + norm-1 + Xagg⊥Y (exists_decomposition_caseB の horth)。
**🔬 要精査: constituent family の θ-indexing (induce H θ が X(μ_j) か Y か, 各 Dθ の構成)。これが per_constituent assembly の核。**
**正本=本 session 41 cont.²。hXorth 完成 (capstone-ready)。次=per_constituent family/aggregate 集約。full build 3813。Opus 継続。**

## 2026-06-15 (session 41 cont.³, /loop): ✅ certainType_per_constituent 特化 landed + 🔬 family 構築 RECON

### ✅ landed (`3c324961`, axiom-clean):
`certainType_per_constituent_Y_eq_smul` — `per_constituent_Y_eq_smul` の certain-type 特化。
**3 構造入力 (hXorth/hηnorm/hYY) を内部 discharge**: hXorth=`inner_decomposition_X_coherentYset_extension_eq_zero_of_mem_Yset` (η₁∈Y のみ)、hηnorm=η₁ 既約、hYY=`extension_inner_eq`。残入力 = family D + (6.8.2.2) aggregate (hagg/hsq/hbi/hXaggorth)。

### 🔬 per_constituent family 構築 RECON (次の核・大ピース):
**per_constituent inputs 状態**:
| 入力 | 状態 |
|---|---|
| hXorth (`⟨Dθ.X, η₁^{τ₁}⟩=0`) | ✅ certainType_per_constituent 内で discharge |
| hηnorm / hYY | ✅ 同上 |
| hsq (∑aθ²=n=\|H:Z\|) | ✅ `sum_inner_restrict_sq_eq_index` (S08:537) |
| **family D** | 🔬 下記 (核) |
| **hagg** (Xagg−n·Y=∑aθ(Dθ.X−Dθ.Y)) | 🔬 下記 |
| hbi (⟨Dθ.Y, η₁^{τ₁}⟩∈ℤ) | ⚠ Dθ.Y∈ZIrr 要 (派生; X_mem_ZIrr は別構造) |

**🔑 family D 構造解析**:
1. **constituents = X-characters (μ_j 列) のみ**: induce W₂ φ (φ∈Irr W₂, φ≠1) の構成要素 χ は ⟨Res_{W₂} χ, φ⟩≠0。Y=S(H') は W₂⊆[H,H]=H' 上自明 ⟹ Res_{W₂}(Y元)=自明 ⟹ φ≠1 は現れない。**∴ Y-char は constituent でない、X(μ_j)のみ**。
2. **family member = certainTypeDecompositionDa** (S06:684): μ_j=columnSum χ₂、`columnSum_eq_induce_H` (S08:1168) で =induce H (Res_H μ_{0j})。**tau1=τ** (ofProjection に `dadeIntegralCharacterMap h.dade0 h.tau` を tau1 として渡す S06:713 ⟹ `tau1_image : τ(αθ)=Dθ.X−Dθ.Y` が aggregate-ready)。imageFamily=certainTypeR ⟹ himg coverage OK。
3. **hagg 組立**: `sum_smul_constituent_diff_eq` (S08:566, ∑aθαθ=induce W₂ φ−|H:Z|η₁) に τ 適用 → `tau_sum_smul_image` (τ(∑aθαθ)=∑aθ(Xθ−Yθ), 要 τ(αθ)=Xθ−Yθ=tau1_image) → LHS=`exists_decomposition_caseB` (τ(induce W₂ φ−|H:Z|η₁)=Xagg−|H:Z|Y)。⟹ Xagg−|H:Z|Y=∑aθ(Dθ.X−Dθ.Y)。
4. **🛑 2 つの構築課題**:
   - **(A) total family**: per_constituent の D は ι 上 total。ι=Irr H なら aθ=0 の θ にも Dθ 要 (項は drop するが型上要)。**対策案**: ι を constituent subtype `{θ // aθ>0}` に絞る (sum_smul_constituent_diff_eq は univ 上ゆえ `Finset.sum_subset` で aθ=0 除外要)、または aθ=0 用 dummy decomposition。
   - **(B) 重み型**: per_constituent は a:ι→ℕ、sum_smul_constituent_diff_eq の重みは ℂ-inner ⟨φ∘e,Res θ⟩ (=mult, 自然数)。`(aθ:ℂ)`=inner の cast 整合要。
5. **θ↔χ₂ 対応**: induce H θ=columnSum χ₂ の θ↔χ₂ 写像。Clifford 対応 (φ∈Irr W₂ ↔ 列 χ₂)。

**▶▶ 次 (推奨手順)**: (i) family member 単体 = certainTypeDecompositionDa を induce H θ 形に rw する補題 (`columnSum_eq_induce_H` 経由) → (ii) hagg 組立 (3 ピース連結, 重み cast) → (iii) total-family の指数化 (subtype or dummy) → (iv) certainType_per_constituent 適用で (6.8.2.3) 結論 `(μ_j−aη₁)^τ=Dθ.X−aη₁^{τ₁}`。**(A)(B) が hard、Clifford 対応 (θ↔χ₂) が要精査。**
**正本=本 session 41 cont.³。per_constituent 特化 landed。family 構築 = 大ピース (total-family/重み/Clifford対応)。full build 3813。**
**🚩 状況: (6.8.2.3) 直交性・hXorth・pinning は完成。残 per_constituent family + cX + capstone glue は大規模 assembly。Opus 継続中だが family 構築は dedicated focus 向き。**

## 2026-06-15 (session 41 cont.⁴, /loop→ChatGPT 相談): 🚨 family 構造の重要訂正 — constituents は「列+既約」の混合

ChatGPT (odd-order project chat) に Clifford 対応を相談 → **検証 OK** (教科書 mmd 04.6/04.7/04.8 引用 + repo 既存補題と整合)。**私の「constituents = 全て列 μ_j」仮定は誤りだった。**

### 🔑 訂正された family 構造 (ChatGPT, 検証済):
`Ind_{W₂}^L φ` (φ∈Irr W₂, φ≠1) の構成要素 = **列 μ_j (可約) と既約誘導指標 Ind_H^L θ の混合**:
- **(4.5) dichotomy** (repo: (4.5.b) exhaustion `Irr(L)={μ_{ij}}∪{Ind_H^L θ}`, S06_CertainTypeClifford:18 で言及):
  - θ = X_j (=Res_H μ_{0j}, 列源) ⟹ I_L(θ)⊋H ⟹ Ind_H^L θ = μ_j (**可約列**, =∑_i μ_{ij})。
  - θ ≠ 全 X_j ⟹ I_L(θ)=H ⟹ Ind_H^L θ ∈ **Irr L** (既約誘導)。
- ∴ X = S−S(Z) は **列 μ_j と既約 Ind_H^L θ の両方**を含む。
- 重み: a_θ=θ(1) (over φ; `inner_central_restrict_eq_apply_one` 済), ∑_{θ over φ} a_θ²=|H:Z| (`sum_inner_restrict_sq_eq_index` 済、= Ind_Z^H φ(1)=|H:Z|)。

### 🔧 corrected family 構築 = **per-θ dispatch**:
| θ の種別 | decomposition | hXorth (⟨D.X, η₁^{τ₁}⟩=0) |
|---|---|---|
| 列 (θ=X_j) | `certainTypeDecompositionDa` (R(μ_j)=σ-images) | **私の disjointness 機構** (hard, 完成: `inner_decomposition_X_coherentYset_extension_eq_zero_of_mem_Yset`) |
| 既約 (θ≠X_j) | `decompositionDaFromDadeOfDiff` (S07:5567, R(χ)={χ^{τ₁},χ̄^{τ₁}}) | **isometry で容易**: ⟨η₁^{τ₁},χ^{τ₁}⟩=⟨η₁,χ⟩=0 (X⊥Y 既約直交) |

**∴ 私の `certainType_per_constituent_Y_eq_smul` (himg=全 R(μ_j) 前提) は列-only 部分問題用で、混合 family には直接適用不可。** 正しくは **汎用 `per_constituent_Y_eq_smul` に per-member dispatch で hXorth を供給**。

### ▶▶ corrected 次手順:
1. **既約 hXorth** (容易): irreducible χ=Ind_H^L θ∈X で ⟨D.X, coherentYset.extension η₁⟩=0 を isometry (extension_inner_eq + X⊥Y irreducibleCharacter_inner_eq_ite) で。`dadeOrthonormalCharacterImageFamilyOfDiff` の imageSet={χ^{τ₁},χ̄^{τ₁}} に対し。
2. **per-θ dispatch family**: index = subtype I_φ={θ∈Irr H: Res_Z θ=θ(1)φ} (zero-support 排除); per θ で (4.5.b) により列/既約を場合分けし decomposition+hXorth を供給。
3. **aggregate**: `sum_smul_constituent_diff_eq` (Irr H 上) を I_φ に制限 (a_θ=0 drop) → `aggregate_eq_sum_of_constituent` で hagg。
4. **per_constituent_Y_eq_smul** (汎用) で pin → (6.8.2.3) per-χ 結論。
**🔑 私の session の disjointness/anchor 機構は「列の hard case」用で正しく必要。既約は容易。dispatch + I_φ subtype indexing が残り。**
**正本=本 session 41 cont.⁴。ChatGPT 相談で family 構造訂正 (混合 dispatch)。Opus 継続。**

### ✅ 既約 hXorth は **既存** (cont.⁴ 追補, 検証済):
`inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero` (S08_CoherenceCorePart1:1721) =
`⟨(decompositionDaFromDadeOfDiff hyp hconj χ …).X, hS₁.extension chi1⟩ = 0` for 既約 χ (X-member),
S₁-member chi1。`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal` (family 直交 producer,
S08CP1:~1683) + `memberExtensionDecomposition` + `inner_decomposition_X_extension_member_eq_zero`。
**⟹ certain-type 既約 member は S₁=Yset, chi1=η₁ で instantiate するだけ (hypothesis-discharge は要るが新証明不要)。**

### 🎯 両 hXorth ケース完備:
| member | decomposition | hXorth | status |
|---|---|---|---|
| 列 μ_j | `certainTypeDecompositionDa` | `inner_decomposition_X_coherentYset_extension_eq_zero_of_mem_Yset` | ✅ 本 session (hard, disjointness) |
| 既約 Ind_H^L θ | `decompositionDaFromDadeOfDiff` | `inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero` | ✅ 既存 (case-A 機構) |

### ▶▶ 残り = **dispatch + glue assembly** (新規構造作業):
1. **per-θ dispatch family** over I_φ={θ∈Irr H over φ}: (4.5.b) で θ=X_j (列) / θ≠X_j (既約) を場合分け、各々 decomposition+hXorth 供給。
2. **aggregate** restriction to I_φ (sum_smul_constituent_diff_eq from Irr H) + ∑a²=|H:Z| → hagg。
3. **per_constituent_Y_eq_smul** (汎用) で pin → (6.8.2.3) per-χ。
4. → cX (case-B X-coherence: 列-coherence `certainTypeSet_isCoherent_tau` + 既約-X-coherence を §7 engine で glue) → `coherentXunionYset_caseB_of_glued` → capstone。
**残作業の本体 = dispatch family の構築 + case-B X-coherence glue (大規模だが hXorth/decomposition 部品は全て揃った)。**
**正本=本 session 41 cont.⁴ 追補。既約 hXorth 既存確認。次=dispatch family 構築。**

## 2026-06-15 (session 41 cont.⁵, /loop): 🎯🎯 重大簡略化 — 列-Y hmixed は seam-1 直接 (per_constituent family 迂回!)

### ✅ landed (`2ee06edf`, axiom-clean):
**`inner_certainTypeExtension_columnSum_coherentYset_extension_eq_zero`**: `⟨ν(μ_j), η^{τ₁}⟩=0`
(η∈Yset, ν=(4.9) certain-type 拡張)。**鍵 = `certainTypeExtension_columnSum` (S06:117): ν(μ_j)=δ_j ∑_i ω_{ij}^σ** (= certainTypeOmegaSigma の ℤ-結合)。⟹ seam-1 (`inner_coherentYset_extension_certainTypeOmegaSigma_eq_zero`, anchor η'=η̄) を inner_sum_left + inner_conj_symm で持ち上げるだけ。

### 🎯 これが意味すること (per_constituent family は列 hmixed に不要):
case-B X-coherence の `coherentXunionYset_caseB_of_glued` が要求する **hmixed (列-Y: ⟨ν μ_j, ν η⟩=⟨μ_j,η⟩=0)** は、cX が μ_j を `certainTypeExtension` で拡張する限り、**上記 lemma で直接 discharge**。**per_constituent_Y_eq_smul / certainType_per_constituent / aggregate-builder / weight / Clifford 対応 / dispatch family は全て不要だった** (これらは (6.8.2.3) の literal pinning route 用; Lean の subset-glue route では seam-1 で十分)。

### ▶▶ 残り case-B assembly (simpler route 確定):
1. **case-B X-coherence cX** = glue 列-coherence (`certainTypeSet_isCoherent_tau`, 列 μ_j, ✅) + 既約-X-coherence (`_of_irreducible_X` の non-column part)。
   - 要: 列↔既約 cross-orthogonality (列の σ-image ⊥ 既約の Dade-image)。← seam-1 類似で easy か要確認 (次の核)。
   - X = certainTypeSet ∪ X_irr の §7 union glue。
2. **X∪Y hmixed**: 列-Y=上記 lemma ✅; 既約-Y=`inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero` (既存) ✅。
3. `coherentXunionYset_caseB_of_glued` で X∪Y → capstone。
**🔑 per_constituent saga は不要と判明。seam-1 が列-Y の鍵。残り = X-internal glue (列∪既約 cross-orth) + §7 union 配線。**
**正本=本 session 41 cont.⁵。列-Y hmixed seam-1 直接 landed。次=列↔既約 cross-orth + X-coherence glue。**

## 2026-06-15 (session 41 cont.⁶, /loop): ✅✅ mixed-inner toolkit 完成 (generic 化, 列-Y/列-既約 統一)

### ✅ landed (3 commits, axiom-clean, full build 3813):
| commit | lemma | 役割 |
|---|---|---|
| `a20ec426` | `coherent_extension_eq_zsmul_irreducible` | 任意 coherence cS の既約 member 像 = ε·ξ (Y版の一般化) |
| `4cfe81d5` | **`inner_coherent_extension_certainTypeOmegaSigma_eq_zero`** | **generic seam-1**: 任意 cS + 既約 η,η' (⟨η,η'⟩=0, η−η' H^#-supp) で cS.extension η ⊥ certainTypeOmegaSigma。Y seam-1 は特殊化に refactor |
| `b224ba0f` | **`inner_certainTypeExtension_columnSum_coherent_extension_eq_zero`** | **generic 列 mixed-inner**: ⟨ν(μ_j), cS.extension χ⟩=0 for 任意 cS + 既約 χ。列-Y と列-既約 両方の hmixed 入力を統一。column-Y は特殊化に refactor |

### 🎯 mixed-inner toolkit 完成 — case-B X∪Y glue の直交性入力は全て揃った:
- **列-Y / 列-既約 mixed inner**: ✅ `inner_certainTypeExtension_columnSum_coherent_extension_eq_zero` (cS=coherentYset or cX_irr)。
- **既約-Y mixed inner**: ✅ `inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero` (既存)。
- **既約-既約 (X_irr 内部)**: 既存 §5/§7 (distinct irreducible images orthogonal)。

### ▶▶ 残り = **§7 coherence-engine 配線** (bulk, 数学は済・engineering):
1. **cX_irr**: 非列 X-member (既約 Ind_H^L θ) の coherence (`Xset_centralCommutator_isCoherent_of_irreducible_X` 流を X_irr 部分に)。
2. **cX = cX_col ∪ cX_irr** glue: §7 union engine (`coherentUnion_of_glued...`) に ν/agreements/mixed-inner(上記 toolkit)/diagonal/generation 供給。
3. **X∪Y glue**: `coherentXunionYset_caseB_of_glued` (定義済) に cX + ν + hmixed(toolkit)+ hgen + D。
4. **capstone** (`sibleySetup_is_coherent` X-nonempty branch, S08_CoherenceTheorems:59): hyp.cases 場合分け (Frobenius=既存 / CertainType=case-B 上記) + 全 glue。
**🔑 直交性/mixed-inner は全完成。残りは §7 union engine の ν/diagonal/generation 配線 (大規模 engineering, case-A `_of_frobenius` をミラー)。**
**正本=本 session 41 cont.⁶。mixed-inner toolkit 完成。次=cX_irr + §7 union glue 配線。**

## 2026-06-15 (session 41 cont.⁷, /loop): 🎯🎯🎯 ARCHITECTURE 確定 = Route B (direct anchored τ₂)

### ChatGPT architecture 相談 (思考 9m40s, 検証済) の verdict:
教科書 (6.8.2) は **単一 Z-線形写像 τ₂ : Z[X∪Y] → Z[Irr G] を η₁ anchor で直接定義** (τ₂=τ on supported lattice, η₁^{τ₂}=Y₀)。standalone X-coherence を先に作って glue する Route A では**ない**。anchor η₁ = 各 χ∈X を degree-zero supported 元 `χ − a_χ·η₁` (a_χ=χ(1)/η₁(1)) に変換し Dade 等長の定義域へ落とす device。

### 🔑 Lean レベルでも Route B が厳密に軽いと確認 (cont.⁶ Route A 計画を撤回):
- `coherentXunionYset_caseB_of_glued` (S08:1526) は §7 union engine 呼び出しの **Route A 型 shell** で **完全な `cX : IsCoherent hyp.tau (Xset W2)` を要求**。
- その glue は ν が supported lattice 上 τ と一致 (`D`/`hDτ`/`hgen`) を要求 → `μ_j − a_j η₁` 型 supported 元での一致 = **まさに per-χ anchored 公式 `(μ_j−a_jη₁)^τ = X_j−a_jY₀`**。
- ⟹ **anchored 公式は Route A でも回避不能** (ChatGPT「orthogonality ν(μ_j)⊥Y^{τ₁} は pinning を代替しない」が的中)。Route A は per-χ 公式に加え **cX 構築 + X-internal glue を純オーバーヘッドで上乗せ**。
- ⟹ **Route B (cX を作らない) が厳密に軽い。** mixed-inner toolkit (cont.⁶) は無駄でなく、anchored 公式の `X_χ ⊥ Y^{τ₁}` 部分の入力として活きる (必要だが不十分)。

### cont.²⁴ の「異次数 reducible column」懸念は case B では杞憂 (ChatGPT 訂正):
w₂=|W₂| が素数 → W₂ 非自明線形指標は全 Galois 共役 → 非零列 μ_j (j≠0) は**全て同次数の単一 certain-type 族** (type II/III/IV で「reducible μ_j は p−1 個・全て次数 qu」と本が記録、と整合)。raw (4.9) を w₂-prime 外で使う時だけの問題だった。

### Route B の clean な top-level target (= ChatGPT §5 skeleton):
> **anchored bridge extension lemma**: X, Y_set 互いに直交; Y_set coherent (ext τ₁); η₁∈Y_set (Y₀=η₁^{τ₁}); 各 χ∈X に `(χ−a_χη₁)^τ = X_χ − a_χY₀` (a_χ=χ(1)/η₁(1)) かつ `X_χ ⊥ Y_set^{τ₁}` ⟹ τ₂(η)=τ₁(η), τ₂(χ)=X_χ で **X∪Y_set coherent**。

per-χ 公式は per-φ aggregate pinning から: φ∈Irr(W₂),φ≠1 に `I_φ={θ∈IrrH:Res_{W₂}θ=θ(1)φ}`、`a_θ=θ(1)`、`α_θ=Ind_H^Lθ − a_θη₁`。`∑_θ a_θα_θ = Ind^L_{W₂}φ − |H:W₂|η₁` (aggregate=`exists_decomposition_caseB`) + `∑_θ a_θ²=|H:W₂|` で pinning `b_θ=a_θ` (consult 1 の `per_constituent_Y_eq_smul` 機構)。family は column (θ=X_j→μ_j) と irreducible (θ→Ind_H^Lθ∈IrrL) の**両方を含む** (dispatch)。

### ▶▶ Route B 実装計画 (consult 1 の pinning 機構 + cont.⁶ toolkit を再利用):
1. **per-φ family**: `I_φ`-indexed、column/irreducible dispatch の `(i:ι)→CharacterPsiDecomposition τ (χ i) (a i•η₁)`。reducible→`certainTypeDecompositionDa`、irreducible→既約 machinery。
2. **pinning → per-χ 公式**: `per_constituent_Y_eq_smul` + `aggregate_eq_sum_of_constituent` (両既存) で `(χ−a_χη₁)^τ = X_χ−a_χY₀`。`X_χ⊥Y^{τ₁}` は mixed-inner toolkit。
3. **direct extension lemma**: §7 に「単一 cY + anchored images で X∪Y へ adjoin」直接拡張があるか調査中 (無ければ新規構築; union engine は 2 coherence 要なので Route B 不適)。
4. **capstone** (`sibleySetup_is_coherent` X-nonempty, S08_CoherenceTheorems:59): hyp.cases (Frobenius=既存 / CertainType=上記 Route B)。
**🔑 Route A (cX+§7 union glue) 撤回。Route B (direct anchored τ₂) 確定。per-χ 公式は不可避ゆえ cX オーバーヘッドを切る。次=§7 direct-extension 補題の有無調査 + per-φ family。**
**正本=本 session 41 cont.⁷。architecture=Route B 確定 (ChatGPT 相談 + Lean 署名突合)。**

### ⚠️ cont.⁷ 訂正 (§7 adjoin 補題の署名精査後): pure Route B は不可、**HYBRID が正**
§7 の adjoin 一族 (`retarget_isCoherent_of_supportedDecomposition` S07:4031, `..._and_memberFamily` 4126, `retarget_isCoherent_fromDade_X` 6177, `DadeChainStep` 6262) は**全て `⟨χ,χ⟩=1` (norm-1, 既約型 {χ,χ̄} 正規直交) を要求**。**reducible column μ_j は `⟨μ_j,μ_j⟩ = w₁ ≠ 1` ゆえ chain で cY に直接 adjoin できない。** ⟹ columns は certain-type σ (`certainTypeSet_isCoherent_tau` = cX_col、μ_j↦∑ω^σ) で**別 coherence object として**拡張するしかなく、**cX_col と既約側の union は Lean 上不可避**。pure「単一 τ₂ 直接」は全 inner-product (列-列含む) を一から再証明する重作業ゆえ非現実的。

**∴ 正しい Lean topology = HYBRID** (ChatGPT の per-φ pinning と equal-degree 訂正を活かしつつ union を残す):
- **cX_col** = `certainTypeSet_isCoherent_tau` (columns, 既存)。equal-degree 訂正で全 reducible X-member を被覆。
- **cX_irr** = X_irr (非列既約 member) の coherence。chain (`retarget_isCoherent_fromDade_X` ミラー) を seed または cY base で。← 要構築。
- **union**: cX_col と (cY + X_irr) を §7 union engine で結合 (`coherentXunionYset_caseB_of_glued` shell 流用可)。cross-orth = mixed-inner toolkit (cont.⁶)。
- **diagonal/hgen の anchored data**: 列の `μ_j − a_jη₁` supported 元で `ν(μ_j−a_jη₁)=τ(...)` を要求 = **per-χ anchored 公式 `(μ_j−a_jη₁)^τ = (列σ像) − a_jY₀`**。これが (6.8.2.3) の核で **全 route 共通・不可避**。per-φ pinning (`per_constituent_Y_eq_smul` 既存) + per-φ family (要構築) で得る。

### 🎯 route 非依存の不可避コア (ここから着手):
1. **per-φ family + pinning → anchored 公式** `(μ_j−a_jη₁)^τ = X_j−a_jY₀` (列) & 既約版。← (6.8.2.3) の核、全 route 共通。
2. **equal-degree split fact**: case B (w₂ 素数) で X_red = certainTypeSet ∧ X_irr 全既約 (column/irr 分割が clean)。
3. **cX_irr** (X_irr coherence, chain ミラー)。
これらは A/B どの union topology でも要る。**まず (1) per-φ family を組む** (機構は consult 1 で完成、family 供給のみ)。
**正本=本 session 41 cont.⁷ 訂正。pure Route B 不可 (列 norm≠1)、HYBRID 確定。不可避コア = per-φ anchored 公式。次=per-φ family 構築。**

### cont.⁷ 続: per-φ family 構築マップ (engine/aggregate 完成済を確認、残り = family instantiation)
**完成済 (consult 1)**: pinning engine `per_constituent_Y_eq_smul` (S08:781, 汎用 — hXorth を per-i で取る) + 列ラッパー `certainType_per_constituent_Y_eq_smul` (S08:1395, himg=certainTypeRImage の **column-only**) + anchored 像 `image_eq_of_decomposition` (Y-collapse → `(χ−aη₁)^τ=X−aY₀`) + aggregate source: `sum_smul_constituent_diff_eq` (S08:566, ∑_{θ:Irr H} aθ•(Ind θ−aθη₁)=Ind_K^M φ−|K:H|η₁) / `sum_inner_restrict_sq_eq_index` (S08:537, ∑aθ²=index) / `tau_sum_smul_image`+`aggregate_eq_sum_of_constituent` (S08:737/754) / `exists_decomposition_caseB` (S08:126)。
**family building blocks**: 列 = `certainTypeDecompositionDa` (S06:684, `CharacterPsiDecomposition (dadeMap h.dade0 h.tau) (columnSum χ₂) (a•η₁)`; 注: τ は enlarged certain-type Dade map ⟹ `IsCoherent.congrMap` S08:1441 で hyp.tau へ retarget) / 既約 = `decompositionDaFromDadeOfDiff` (S07:5567) / dichotomy = `exists_eq_certainType_or_induce` (S06_Clifford:938, θ=χ_j→Ind=μ_j 列 / else 既約)。

**🔑 mixed family 確定 + 部分型 index (2 つの非自明点)**:
1. **mixed 確定**: 固定 φ に対し I_φ={θ:Irr H | aθ=⟨φ,Res θ⟩>0} は χ_j (→列 μ_j reducible) と non-χ_j (→既約 Ind θ) を**両方含む** (dichotomy より)。⟹ column-only `certainType_per_constituent_Y_eq_smul` では不足、汎用 `per_constituent_Y_eq_smul` を **dispatch hXorth** (列=seam-1 列 orth / 既約=`inner_decompositionDaFromDadeOfDiff_X_…`) で直接呼ぶ。
2. **部分型 index**: `Ind θ` は degree≠0 で **non-supported** ⟹ aθ=0 の θ に `CharacterPsiDecomposition τ (Ind θ) 0` は**存在しない**。∴ family の index は全 Irr H 不可、**ι = 部分型 `{θ:Irr H // aθ>0}`** (全 aθ>0、2-way dispatch)。aggregate/∑aθ² は aθ=0 項脱落で univ:Irr H → 部分型へ再添字 (`Finset.sum_subset`/`sum_attach`)。

### ▶▶ 次の具体ステップ (順に landable):
1. **部分型 aggregate**: `sum_smul_constituent_diff_eq`+`sum_inner_restrict_sq_eq_index` を ι={θ//aθ>0} へ再添字 (hagg/hsq の部分型版)。← 自己完結 brick、まずこれ。
2. **dispatched family** `D : (θ:ι) → CharacterPsiDecomposition hyp.tau (Ind θ) (aθ•η₁)`: θ=χ_j → certainTypeDecompositionDa (congrMap で hyp.tau 化) / else → decompositionDaFromDadeOfDiff。
3. **per-χ anchored 公式**: `per_constituent_Y_eq_smul` (dispatch hXorth) + `image_eq_of_decomposition` で `(μ_j−a_jη₁)^τ=X_j−a_jY₀` & 既約版。
4. → HYBRID union (cX_col ∪ (cY+X_irr)) の diagonal data に投入。
**正本=本 session 41 cont.⁷ 続。family 構築マップ確定 (mixed + 部分型 index)。次=部分型 aggregate brick。**

### cont.⁷ 続²: 🔑 map-reconciliation 確定 (family が単一 τ=hyp.tau を満たす方法) + index 基盤 landed
**landed (build-green, axiom-clean)**: `sum_eq_sum_pos_weight_subtype` (a02144a5, 部分型再添字) + `exists_inner_restrict_natCast`/`constituentWeight`/`_spec`/`_pos_iff` (74aee2fb, ℕ-weight 基盤; weight=⟨φ,Res θ⟩ via Clifford `restrictionMultiplicity_natCast`)。

**🔑 map-reconciliation**: `hyp.tau = dadeIntegralCharacterMap hyp.dade (hyp.dade.fullDadeIsometryData hyp.hconj)` (abbrev, S08_CoherenceCorePart2:31)。
- **irreducible branch = `decompositionDaFromDadeOfDiff hyp.dade hyp.hconj`** が `CharacterPsiDecomposition hyp.tau (Ind θ) (a•η₁)` を**直接**生成 (retarget 不要!)。per-θ 仮説 (non-real/diff-supports/ZIrr/orthog) は case-A 機構 (`Xset_..._isCoherent_of_irreducible_X`/`DadeChainStep` field 構成) を再利用。
- **column branch**: `certainTypeDecompositionDa` は enlarged map `dadeIntegralCharacterMap h.dade0 h.tau` 用。hyp.tau 版は `CharacterPsiDecomposition.ofProjection (certainTypeR h46 χ₂ hdeg) hyp.tau (inner-preservation = dadeIntegralCharacterMap_inner_eq_on_supported_span hyp.dade hyp.hconj) …` で再構成。⚠ 要検証: column diff (μ_j−μ̄_j, μ_j−aη₁) が **H^#-supported** (hyp.tau の定義域) か。case c2 (hHK: h46.K=H) なら μ_j=Ind_H^L χ_j で H-supported のはず (certainTypeDecompositionDa の A₀=A∪V は K⊊H 一般版ゆえの保守)。

### ▶▶ 精緻化した brick 順 (column/irreducible 両分解 → dispatch → aggregate → pinning):
1. **column decomp (hyp.tau 版)**: ofProjection 再構成。← 次。⚠ H^#-support 検証。
2. **irreducible decomp**: `decompositionDaFromDadeOfDiff hyp.dade hyp.hconj` 直接 (新 lemma 不要、per-θ 仮説 discharge を case-B 文脈で)。
3. **dispatch family** `(i:{θ//0<aθ}) → CharacterPsiDecomposition hyp.tau (Ind i.val) (aθ•η₁)`: `by_cases ∃χ₂, chiRestrict χ₂=θ` (dichotomy `exists_eq_certainType_or_induce`) で column/irreducible 分岐。aθ=constituentWeight 整合。
4. **subtype aggregate** hagg/hsq: `sum_smul_constituent_diff_eq`+`sum_inner_restrict_sq_eq_index` を `sum_eq_sum_pos_weight_subtype` で部分型へ、weight を constituentWeight_spec で整合、`aggregate_eq_sum_of_constituent` で hagg。
5. **pinning → anchored 公式**: `per_constituent_Y_eq_smul` (dispatch hXorth) + `image_eq_of_decomposition`。
6. **HYBRID union**: cX_col ∪ (cY+X_irr)、diagonal に anchored 公式投入。
**正本=本 session 41 cont.⁷ 続²。map-reconciliation 確定 (irred 直接/column ofProjection)。index 基盤 2 brick landed。次=column decomp (hyp.tau) brick。**

### cont.⁷ 続³: 🎯🎯 map 問題 DISSOLVED — `dadeIntegralCharacterMap` は data 引数無視 ⟹ family は τ_enl で統一
**🔑 決定的発見**: `dadeIntegralCharacterMap (hyp) (_dade : FullDadeIsometryData)` の **data 引数は body で未使用** (`_dade`、定義は `Classical.choose (LinearMap.exists_extend hyp.dadeLinearMap)` で hyp のみ依存; S07:5233-5236)。⟹ **`dadeIntegralCharacterMap h46.dade0 h46.tau = dadeIntegralCharacterMap h46.dade0 (任意 data)` が defeq**。

**∴ 続² の「column を hyp.tau 版へ retarget」は不要** (certainTypeR の image family が τ_enl=`dadeIntegralCharacterMap h46.dade0 h46.tau` に型付けゆえ retarget 不能だったが、data 無視で問題消滅)。`certainTypeColumnDecompositionTau` 試作は revert。正しい構図:
- **family の単一 τ = τ_enl = `dadeIntegralCharacterMap h46.dade0 h46.tau`** (enlarged certain-type map)。
- **columns = `certainTypeDecompositionDa`** (τ_enl、**既存**! 新規不要)。
- **irreducibles = `decompositionDaFromDadeOfDiff h46.dade0 h46.dade0.hconj`** (data 無視ゆえ `CharacterPsiDecomposition τ_enl` を生成、defeq; **既存**!)。両 branch の image family が同一 τ_enl に型付け。
- **aggregate transfer**: `exists_decomposition_caseB` は hyp.tau(Ind_{W₂}φ−nη₁)=X−nY₀。pinning は τ_enl 版を要する ⟹ τ_enl(Ind_{W₂}φ−nη₁)=hyp.tau(同) を **H^# 一致** (両 map とも H^#-supported 上 Dade map に一致; `dadeIntegralCharacterMap_apply_of_support` + h46.dade=hyp.dade) で transfer。Ind_{W₂}φ−nη₁ は H^#-supported。
- **source aggregate** (`sum_smul_constituent_diff_pos_weight_subtype`, landed) は char-level (τ 非依存) ゆえそのまま。
- seam-1 orthogonality / Y₀=coherentYset.ext η₁ は ZIrr 元の inner ゆえ map 非依存、`certainType_per_constituent_Y_eq_smul` の generic τ にそのまま。

### ▶▶ 残り brick (map 問題消滅で大幅単純化):
1. **aggregate transfer** hyp.tau→τ_enl (H^# 一致)。← 自己完結 brick。
2. **dispatch family** `(i:{θ//0<aθ}) → CharacterPsiDecomposition τ_enl (Ind i.val) (aθ•η₁)`: `by_cases ∃χ₂, chiRestrict χ₂=θ` で certainTypeDecompositionDa / decompositionDaFromDadeOfDiff 分岐。両既存ゆえ各 branch は instantiate のみ (per-θ 仮説 discharge)。
3. **hagg** (`aggregate_eq_sum_of_constituent` + family + transferred aggregate + source aggregate) + **hbi** (⟨Dᵢ.Y,Y₀⟩=bᵢ∈ℤ via inner_mem_ZIrr_int)。
4. **pinning** (`per_constituent_Y_eq_smul`) + `image_eq_of_decomposition` → anchored 公式。
5. **HYBRID union**。
**正本=本 session 41 cont.⁷ 続³。map 問題 dissolved (data 無視→τ_enl 統一)。両分解とも既存。次=aggregate transfer + dispatch family。**

### cont.⁷ 続⁴ 訂正: τ_enl 統一は不可 → **hyp.tau 統一が forced** (irreducible R-family は hconj 必須)
續³ の「τ_enl で両分解既存」は誤り。検証: **h46.dade0 は HConjInvariant を持たない** (`h46.dade0.H a = ⊥` は V-共役 a でのみ成立 [`H_eq_bot_of_centralizer_le`+条件]、uniform でなく `of_forall_H_eq_bot` 不可)。一方 irreducible R-family `dadeOrthonormalCharacterImageFamilyOfDiff` は **hconj 必須** (`_of_data` 変種なし) ⟹ **τ_enl では irreducible 分解を作れない**。columnConstituentDecomposition (b046f41f, τ_enl) は dead-end (harmless・committed、後で supersede)。

**∴ approach (b): 全分解を τ = hyp.tau に統一** (hyp.dade は hyp.hconj あり):
- **irreducibles** = `decompositionDaFromDadeOfDiff hyp.dade hyp.hconj` (自然に hyp.tau)。
- **columns** = R-family を hyp.tau 用に **rebuild**: certainTypeR の `imageSet`/`mem_ZIrr`/`orthonormal` (全 map 非依存) を再利用 + `image_eq` を hmapagree で transfer (`(μ_j−μ̄_j)^{hyp.tau} = (μ_j−μ̄_j)^{τ_enl}`、μ_j−μ̄_j は K=H で H^#-supported、両 map H^# 一致)。→ ofProjection で column 分解 (hyp.tau)。hmapagree は capstone 供給 (certainTypeSet_isCoherent_tau と同様)。
- aggregate (exists_decomposition_caseB) は元々 hyp.tau ゆえ transfer 不要 (續³ の transfer も不要に)。

### ▶▶ 残り brick (approach b 確定):
1. **columnRFamilyTau**: `OrthonormalCharacterImageFamily hyp.tau (columnSum χ₂)` (certainTypeR 3 field 再利用 + image_eq via hmapagree)。← 次。
2. **column 分解 (hyp.tau)**: ofProjection columnRFamilyTau。
3. **irreducible 分解 (hyp.tau)**: decompositionDaFromDadeOfDiff hyp.dade hyp.hconj 薄ラッパー。
4. dispatch family + hagg/hbi + pinning + HYBRID union。
**正本=本 session 41 cont.⁷ 続⁴。τ_enl 不可 (irreducible は hconj 必須)、hyp.tau 統一 forced。column は R-family rebuild。次=columnRFamilyTau。**

### cont.⁷ 続⁵: per-φ family foundation 完成 + 全体組立 scope 確定 (HYBRID, standalone cX 不要)
**landed (build-green, all axiom-clean)**: `sum_eq_sum_pos_weight_subtype`/`constituentWeight`(一式)/`sum_smul_constituent_diff_pos_weight_subtype` (index/weight/source-aggregate) + `columnRFamilyTau`+`columnDecompositionTau` (column branch hyp.tau) + `irreducibleDecompositionTau` (irreducible branch hyp.tau) + **`per_phi_anchored_image`** (anchored 公式 assembly skeleton: family D 仮説化で `(χᵢ−aᵢη₁)^{hyp.tau}=(D i).X−aᵢY₀` を pinning+tau1_image で sorry-free)。⟹ **(6.8.2.3) core は family 仮説化で完成**、残 gap = family 構築 (D)。

**🎯 全体組立 scope 確定 (HYBRID; standalone cX 不要)**: shell `coherentXunionYset_caseB_of_glued` は cX (full X-coherence) を要すが、それは作らず Route-B 寄りの HYBRID:
1. **dispatch family D** (capstone 級): `{θ:Irr H//0<aθ}` で column (`columnSum_eq_induce_H ▸ columnDecompositionTau`) / irreducible (`irreducibleDecompositionTau`) 分岐。K=H transport は `rw [hHK]` で可 (columnSum_mem_S が実証)。per-θ 仮説 discharge が bulk。→ `per_phi_anchored_image` に投入 → anchored 公式。
2. **X_irr を cY に chain-adjoin**: `retarget_isCoherent_of_supportedDecomposition` (S07:4031, 既存) で既約 X-member を 1 ペアずつ cY に adjoin (anchored 公式=供給する supported decomposition)。→ coherence of Y∪X_irr。**standalone cX_irr 不要**。
3. **columns を §7 union で結合**: (Y∪X_irr)-coherence と cX_col (`certainTypeSet_isCoherent_tau`) を union engine で結合。diagonal=column anchored 公式、cross-orth=mixed-inner toolkit (cont.⁶)。
4. **capstone** (`sibleySetup_is_coherent` X-nonempty, S08_CoherenceTheorems:59)。
**realistic scope: 大 (dispatch capstone 級 + 2 段 glue)、多ターン。foundation は landed。次=dispatch family (rw [hHK] transport)。**
**正本=本 session 41 cont.⁷ 続⁵。per-φ foundation 完成 (7 bricks)。組立=HYBRID (chain-adjoin X_irr + union columns, cX 不要)。次=dispatch family。**

## 2026-06-15 (session 42, lane-b 再開, Opus): (6.8.2.3) per-φ anchored 公式 end-to-end landed (新 leaf, 6 commits)

**新 leaf = `OddOrder/Peterfalvi/S08_CaseBAssembly.lean`** (S08_CaseBCoherence2 が 2157 行で 1500 上限超過 → active assembly を新 leaf へ。root import 追加、AxiomsCheck は frontier leaf 不要)。S08_CaseBCoherence2 は hub 分割対象 (issue 化推奨)。

### ✅ landed (全 axiom-clean [propext, Classical.choice, Quot.sound], full build 3626 jobs):
| commit | 結果 | 役割 |
|---|---|---|
| `9a87548c` | **`caseB_constituentDecomposition`** | per-θ dispatch: θ:Irr H に対し `Ind^L_H θ` の (5.4) 分解を column/irreducible 分岐。**dispatch 条件は値レベル `∃ χ₂≠1, columnSum h46 χ₂ = Ind^L_H θ`** (CF L 上等式 → ↥h46.K vs ↥H 型不一致を回避)。column→`columnDecompositionTau` (heq ▸ cast)、irr→`irreducibleDecompositionTau`。per-θ 仮説は conditional bundle hcol/hirr (parametrized)。witness は `.choose` (Type 値ゴール ⟹ Prop ∃ の large-elim 不可) |
| `d8631d8b` | **`caseB_constituentDecomposition_tau1`** + projection refactor | `(dispatch).tau1 = hyp.tau`。bundle を `.1/.2.…` 射影で消費 (obtain=And.casesOn は field 還元を阻む)、column index は `heq ▸` (rw=Eq.mpr 不可)。`charPsiDecomp_eqRec_tau1` (cast 越しの tau1 不変) |
| `a9a3a7bf` | **per_phi_anchored_image cY 一般化** (S08_CaseBCoherence2 内) + **`sum_constituentWeight_sq_subtype`** | (1) Y-anchor を hyp.coherentYset から任意 cY へ (exists_decomposition_caseB は \|Y\|=2 edge で swapped cY を返す ⟹ 必須)。(2) hsq: `∑_θ aθ²=\|H:W₂\|` over subtype |
| `ae49ef08` | **`caseB_hagg`** | (6.8.2.2)→(6.8.2.3) aggregate `Xagg − \|H:W₂\|·Y₀ = ∑ aθ·((D θ).X−(D θ).Y)`。aggregate_eq_sum_of_constituent + sum_smul_constituent_diff_pos_weight_subtype。**hmemimg は仮説側 rw (`rw [htau1] at h`); hconstit は `.trans` (rw=motive エラー回避); ℂ-anchor↔ℕ-anchor は Nat.cast_smul_eq_nsmul** |
| `38a21b44` | **`caseB_per_phi_anchored`** | **(6.8.2.3) anchored image 本体**: `(Ind^L_H θ − aθ·η₁)^{hyp.tau} = (D θ).X − aθ·cY.ext η₁`。per_phi_anchored_image の thin wiring (hagg/hsq 内部組立)。**family D は抽象** (tau1=hyp.tau な任意 family) ⟹ dispatch 構築と分離 |

### 🎯 (6.8.2.3) route-independent core = landed (skeleton)。残 = per-θ discharge のみ:
`caseB_per_phi_anchored` が要求する未充足入力 (= 次セッションの genuine §5/§6 math):
1. **family D 構築**: `caseB_constituentDecomposition` を subtype 上で。per-θ bundle **hcol** (column: hdeg/hmapagree/hSdiff/htau1_mema/hχψ/hχbarψ for χ₂) + **hirr** (irreducible: hirr'/hreal/hdiffsupp/hdiffasupp/htau1_mema/hχaχ1/hχbaraχ1/hχχbar' for Ind^L_H θ) の discharge。column=certain-type (4.9) 構造; irr=case-A Dade chain ミラー (`retarget_isCoherent_fromDade_X`/`DadeChainStep` の field 群)。
2. **hXorth**: `∀ θ, ⟨(D θ).X, cY.ext η₁⟩=0` (seam-1: mixed-inner toolkit cont.⁶ — column=`inner_certainTypeExtension_columnSum_coherent_extension_eq_zero`, irr=`inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero`)。dispatch 越しゆえ tau1 同様 per-branch 証明。
3. **hbi**: `∀ θ, ⟨(D θ).Y, cY.ext η₁⟩ = bθ ∈ ℤ` (ZIrr inner = ℤ; `inner_mem_ZIrr_int`)。

### ▶▶ HYBRID 組立 (cont.⁷ 訂正のまま、anchored 公式が diagonal data):
anchored 公式 landed ⟹ cont.⁷ 続⁵ の組立計画 (chain-adjoin X_irr to cY + union with cX_col) の diagonal/hgen 入力が供給可能に。残 = (1) per-θ discharge → 具体 D、(2) X_irr chain-adjoin (`retarget_isCoherent_of_supportedDecomposition`)、(3) cX_col union、(4) capstone (`sibleySetup_is_coherent` X-nonempty branch)。

**正本=本 session 42。(6.8.2.3) core landed (abstract D skeleton)。次=per-θ discharge (hcol/hirr → D 具体化, hXorth/hbi)。Opus 継続。**

### session 42 cont.: family 構築子 landed + hXorth/hbi 経路確定
**✅ landed (`142b86dc`)**: `caseB_phi_family` (D 構築子 = dispatch over subtype) + `caseB_phi_family_tau1`。
⟹ `caseB_per_phi_anchored` の 4 入力中 **D + htau1 供給可能**。残 = hXorth + hbi。

**▶▶ hXorth/hbi 経路 (精査済、次の実装対象):**
- **hXorth** `⟨(D i).X, cY.ext η₁⟩=0` = `inner_X_Y_eq_zero_of_orthogonal` (S08:926, `⟨D.X,Y⟩=0` ⟸ `∀α∈D.imageFamily.imageSet, ⟨Y,α⟩=0`) + **per-branch seam-1**:
  - column: imageSet = `columnRFamilyTau.imageSet` = `certainTypeR.imageSet` = R(μ_j) σ-images。cY.ext η₁ ⊥ それ = cont.⁶ toolkit `inner_coherent_extension_certainTypeOmegaSigma_eq_zero` (generic cS ⟹ cY 適用可)。
  - irr: imageSet = `dadeOrthonormalCharacterImageFamilyOfDiff.imageSet`。cY.ext η₁ ⊥ それ = `inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero` (S08CP1, 既存)。
  - ⚠ dispatch 越し ⟹ **`charPsiDecomp_eqRec_imageSet` cast helper 要** (tau1 同型: column branch の `heq ▸` cast が imageSet を保つ。imageSet : Set(CF G ℂ) は χ 非依存ゆえ `cases h; rfl`)。`unfold caseB_phi_family caseB_constituentDecomposition; split` で per-branch。
- **hbi** `⟨(D i).Y, cY.ext η₁⟩ = bᵢ∈ℤ` = **hXorth に依存**: tau1_image で `(D i).Y = (D i).X − hyp.tau(Ind θ−aη₁)` ⟹ `⟨(D i).Y, cY.ext η₁⟩ = 0 − ⟨hyp.tau(Ind θ−aη₁), cY.ext η₁⟩` (hXorth)。後者 = htau1_mema (bundle, hyp.tau(Ind θ−aη₁)∈ZIrr) + cY.ext η₁∈ZIrr ⟹ inner_mem_ZIrr_int で ℤ。bᵢ := −(witness)。
- ⚠ cY.ext η₁ ∈ ZIrr: coherence extension の ZIrr 性 (要確認: `IsCoherent.extension_mem_ZIrr` 類)。

**∴ 次 = (1) `charPsiDecomp_eqRec_imageSet` helper → (2) hXorth per-branch (toolkit cY 適用) → (3) hbi (hXorth + integrality) → (4) caseB_per_phi_anchored を caseB_phi_family で具体化 (abstract D 解消) → (5) per-θ bundle (hcol/hirr) discharge → (6) HYBRID 組立。**
**正本=本 session 42 cont.。family landed、hXorth/hbi 経路確定。次=hXorth (cast helper + cY-general toolkit)。**

### session 42 cont.²: ⚠ hXorth の partner-anchor 要件 (設計精緻化、未実装)
hXorth の column seam-1 `⟨cY.ext η₁, ω_ij^σ⟩=0` を精査: toolkit `inner_coherent_extension_certainTypeOmegaSigma_eq_zero` (S08:1246) は **差 `cY.ext η − cY.ext η'` が tic V 上消失** (`coherent_extension_diff_apply_eq_zero_of_mem_ticVdiffV`) を使うため、**distinct partner η' ∈ Yset (η₁≠η', ⟨η₁,η'⟩=0, η₁−η' は H^#-supported) が必須**。⟹ 単一 η₁ では証明不可。
**含意**: `caseB_per_phi_anchored` の hXorth 入力 (または family の hXorth 証明) に **partner anchor η' (|Yset|≥2)** を追加要。case-B は |Yset|≥2 が成立するはず (Yset = S(H')-filtration、複数 linear chars) — 要確認 (`exists_Yset_linearRepresentativeFamily` の 2≤n、または \|Yset\|≥2 は別途)。**∴ hXorth 実装時は partner η' を threading する設計に。** irr branch の seam-1 (`inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero`) は partner 不要か要確認。
**正本=本 session 42 cont.²。hXorth は partner-anchor 要 (設計追加)。次=cast helper + partner-threading hXorth。**

### session 42 cont.³ (lane-b, Opus): ✅ cast helper landed + 🔑 partner-anchor 要件 解決 (|Yset|≥2 既存)
**✅ landed (`94206d98`, axiom-clean)**: `charPsiDecomp_eqRec_imageSet` (cast helper, brick #1; `charPsiDecomp_eqRec_tau1` の imageSet 版、`cases h; rfl`)。dispatch の column-branch `heq ▸` cast 越しに `imageFamily.imageSet` 不変 (imageSet : Finset(CF G ℂ) は χ 非依存)。

**🔑 cont.² の「partner-anchor |Yset|≥2 要確認」は解決 = 既存**: `hyp.two_le_Yset_ncard` (SibleyDadeHypothesis field, S08_CaseBCoherence:310/331 で使用)。partner 抽出は `Set.exists_ne_of_one_lt_ncard (by have := hyp.two_le_Yset_ncard; omega) η₁` (precedent: S08_CaseBCoherence:331)。

**▶▶ hXorth column 次手 (recipe 確定)**: toolkit `inner_coherent_extension_certainTypeOmegaSigma_eq_zero` (S08_CaseBCoherence2:1246) を η=η₁ + partner η' で instantiate。**要 discharge する partner 4 条件**:
1. `η' ∈ S₁` — `two_le_Yset_ncard` + `exists_ne_of_one_lt_ncard` (η'≠η₁ かつ η'∈Yset)。
2. `IsIrreducibleCharacter η'` — Yset/S₁ members は既約 (要 lemma: coherence set membership → irreducible)。
3. `⟨η₁, η'⟩ = 0` — distinct 既約は直交 (`irreducibleCharacter_inner_eq_ite` + η₁≠η')。
4. `(η₁ − η').support ⊆ supportInSubgroup (sharpImage H) L` — Yset 差の H^#-support 性 (要 lemma)。
**precedent = S08_CaseBCoherence:310-340** (同 toolkit を別文脈で使用、partner 抽出+4 条件 discharge の実例)。これを読んで column hXorth lemma を組む。
irr branch (`inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero`, S08CP1) は partner 不要か要確認。
**dispatch 越し**: `charPsiDecomp_eqRec_imageSet` (landed) + `unfold caseB_phi_family caseB_constituentDecomposition; split` で per-branch。

**正本=本 session 42 cont.³。cast helper landed、|Yset|≥2 解決 (two_le_Yset_ncard)。次=hXorth column (toolkit instantiate, partner 4 条件 discharge, precedent S08_CaseBCoherence:310-340) → irr branch → hbi → caseB_phi_family 具体化。**

### session 42 cont.⁴ (lane-b, Opus): ✅✅ (6.8.2.3) wiring COMPLETE — abstract D 解消 (3 commits)
**✅ landed (全 axiom-clean [propext, Classical.choice, Quot.sound], full build 3822 jobs green):**
| commit | 結果 | 役割 |
|---|---|---|
| `030a2b65` | **`charPsiDecomp_eqRec_X`/`_Y`** + **`psiDecomp_Y_inner_int`** | cast helper の X/Y 版 (tau1/imageSet と同型、`cases h; rfl`) + **route 非依存 hbi**: 任意 (5.4) 分解 D で X⊥Y₀ かつ τ₁-image∈ZIrr かつ Y₀∈ZIrr なら `⟨D.Y,Y₀⟩ = −⟨D.tau1(χ−ψ),Y₀⟩ ∈ ℤ` (`Y=X−τ₁(χ−ψ)` via tau1_image + `inner_sub_left` + `inner_mem_ZIrr_int`)。column/irr 分岐不要の汎用 brick |
| `fb7d02ba` | **`CaseBColBundle`/`CaseBIrrBundle`** abbrev + dispatch 3 補題 | bundle 抽出 (caseB_constituentDecomposition の inline hcol/hirr と defeq、dispatch 補題で共有) + `caseB_constituentDecomposition_tau1_mem_ZIrr` (hyp.tau(Ind θ−a·η₁)∈ZIrr を branch bundle から; column=witness rw, irr=直接) + `_X_orthogonal` (unfold/split + `charPsiDecomp_eqRec_X` cast + standalone column/irr seam-1; partner η'・per-θ anchor `hirrAnc` は明示仮説) + `_Y_inner_int` (`psiDecomp_Y_inner_int` 経由) |
| `fe4f53c1` | **`caseB_per_phi_anchored_family`** | **abstract D 解消**: `caseB_per_phi_anchored` を具体 family `caseB_phi_family` に特殊化。D/hXorth/hbi を dispatch 補題で discharge (`b` は `_Y_inner_int` の choice)。各 θ=i.val で `(Ind^L_H θ−aᵢ·η₁)^{hyp.tau} = (caseB_phi_family … i).X − aᵢ·cY.extension η₁` |

**🎯 (6.8.2.3) per-φ anchored image は具体 family 上で完全組立済**。`caseB_per_phi_anchored_family` の残り入力 = **全て genuine §5/§6 content (capstone 側 discharge)**:
1. **per-θ bundles `hcol`/`hirr`** (`∀ i, CaseBColBundle/CaseBIrrBundle hyp h46 i.val η₁ (constituentWeight hφ' i.val)`): column=certain-type (4.9) reflection の structural data / irr=case-A Dade chain (`DadeChainStep`/`retarget_isCoherent_fromDade_X` field 群)。**bulk の discharge**。
2. **η₁-anchor data** (`hη₁`/`hη₁irr`/`hrealc1`/`hdiffsuppc1`/`hc1barS1`/`hνZc1`/`hc1c1bar`): Y-anchor η₁ の実既約性・非実・supported conj 差・ZIrr extension。`hνZc1 = cY.extension_mem_ZIrr η₁ (subset_span hη₁)`。
3. **partner anchor** (`η'`/`hη'Y`/`hη'irr`/`hee`/`hsupp`): η'≠η₁∈Yset、既約、⟨η₁,η'⟩=0、(η₁−η') H^#-supported。抽出=`Set.exists_ne_of_one_lt_ncard (two_le_Yset_ncard) η₁` (precedent S08_CaseBCoherence:331); 4 条件 discharge は Yset-member の既約性/直交/support lemma 要 (precedent S08_CaseBCoherence:310-340)。
4. **per-θ anchor-vs-constituent** (`hirrAnc i`): irr branch で ⟨η₁,Ind θ⟩=⟨η₁,(Ind θ)conj⟩=⟨η₁conj,Ind θ⟩=⟨η₁conj,(Ind θ)conj⟩=0 (η₁ linear ⊥ 既約 induced)。
5. **(6.8.2.2) aggregate** (`Xagg`/`hXaggorth`/`hdecomp`): `exists_decomposition_caseB` (S08:126) から。

**▶▶ 次の具体ステップ (順):** (1) **anchor data discharge** (η₁-anchor + partner + hirrAnc — Yset-member の既約性/support の lemma 整備が核; precedent あり) → (2) **per-θ bundles discharge** (column/irr structural、bulk) → (3) **(6.8.2.2) aggregate 接続** (`exists_decomposition_caseB` の wiring; \|Yset\|=2 edge で cY swap 注意 — `per_phi_anchored_image` cY 一般化済) → (4) **HYBRID 組立** (anchored 公式を diagonal data に: cY に X_irr を `retarget_isCoherent_of_supportedDecomposition` で chain-adjoin + cX_col `certainTypeSet_isCoherent_tau` と §7 union) → (5) capstone `sibleySetup_is_coherent`。
**正本=本 session 42 cont.⁴。(6.8.2.3) 具体 family 上 完全組立 (abstract D 解消)。次=anchor data discharge (Yset-member 既約性/support lemma + partner 抽出, precedent S08_CaseBCoherence:310-340)。**

### session 42 cont.⁴ 続: ✅ `caseB_per_phi_anchored_fromYset` — Y-anchor data 内製化 (commit `6330ad76`)
cont.⁴ の `caseB_per_phi_anchored_family` を強化: **η₁-anchor + partner block 全体を `hη₁ : η₁ ∈ Yset` だけから discharge**。partner = **η̄₁ (共役)** の教科書的選択を内製 (既存 `inner_decomposition_X_coherentYset_extension_eq_zero_of_mem_Yset` S08CB2:1390 / `inner_certainTypeExtension_columnSum_coherentYset_extension_eq_zero` S08CB2:1449 と同パターン):
- η̄₁∈Y = `Yset_closedUnderConjugate`、η₁≠η̄₁ = `Yset_hasNoRealCharacters.not_mem_of_isReal` ((5.2.a) odd⇒no real irr)、⟨η₁,η̄₁⟩=0 = `irreducibleCharacter_inner_eq_ite`+hne、(η₁−η̄₁) H^#-support = `sMember_diffSupport_of_charValue_eq`+`Yset_apply_one` (等次数)。`hη₁irr`=`isIrreducibleCharacter_of_mem_Yset`、`hνZc1`=`extension_mem_ZIrr`。

**⟹ `caseB_per_phi_anchored_fromYset` の残り入力 = genuine §5/§6 hard core のみ (boilerplate anchor 消滅):**
1. **per-θ bundles `hcol`/`hirr`** (column=(4.9) certain-type structural / irr=case-A Dade chain field) — **bulk**。
2. **`hirrAnc i`** (per-θ: ⟨η₁,Ind θ⟩ 系 4 直交; η₁∈Yset linear ⊥ irr constituent Ind θ)。
3. **(6.8.2.2) aggregate `hXaggorth`/`hdecomp`** (`exists_decomposition_caseB` S08:126)。

**▶▶ 次の brick 候補 (contained 順):** (a) **(6.8.2.2) aggregate 接続** = `exists_decomposition_caseB` を fromYset の hXaggorth/hdecomp に wiring (\|Y\|=2 edge で cY swap; `per_phi_anchored_image` は cY 一般化済ゆえ吸収可) → (b) **hirrAnc discharge** (η₁ vs Ind θ 直交; distinct irr or Yset⊥X 構造) → (c) **per-θ bundles** (column/irr structural, bulk) → (d) **HYBRID 組立** (anchored 公式 = diagonal: cY に X_irr chain-adjoin `retarget_isCoherent_of_supportedDecomposition` + cX_col `certainTypeSet_isCoherent_tau` を §7 union) → (e) capstone `sibleySetup_is_coherent`。
**正本=本 session 42 cont.⁴ 続。fromYset で anchor 内製化完了。次=(6.8.2.2) aggregate 接続 or hirrAnc discharge。**

### session 42 cont.⁴ 続²: 🔑 capstone case-B の正確な frontier map (hmapagree linchpin = dadeMap canonicality)
fromYset 完成後の (6.8) capstone case-B (`sibleySetup_is_coherent` の X-nonempty / `cases.inr` 枝) を末端まで精査。

**capstone case-B が供給する構造 (`hyp.cases.inr`, S08CP1:3321-3326):**
`∃ h46 : Hypothesis46 (sharpImage H) L, h46.dade = hyp.dade ∧ h46.K = H ∧ h46.W1 = W1 ∧ (card h46.W2).Prime ∧ h46.W2 ≤ ⁅H,H⁆ ∧ Coprime (card H) (card W1)`。⟹ **h46 + hHK + `h46.dade = hyp.dade` が直接手に入る**。

**assembly の path (capstone case-B branch):**
1. **cX_col** (reducible columns μ_j) = `certainTypeSet_isCoherent_tau` (S08CB2:1651, **sorry-free shell**) — 要 `hmapagree`。
2. **cX_irr** (irreducible 部) = case-A 機構 `xChainCoherent` (S08CP1:2701) over irr X-members — 要 per-step `XAdjoinStepInput` (= per-θ bundle 相当)。
3. **cX = cX_col ∪ cX_irr** (union)。
4. **cX ∪ cY** = `coherentXunionYset_caseB_of_glued` (S08CB2:1616, **sorry-free shell**) — 要 ν / hmixed / hpair / D / hgen。**hmixed = (6.8.2.3) content = fromYset の anchored 公式が供給**。

**🔑 linchpin = `hmapagree`** (`dadeIntegralCharacterMap h46.dade0 h46.tau φ = hyp.tau φ` on H^#-supported φ; cX_col + column bundle conjunct 2 + 全 map-agreement の gate):
- h46.dade0 (enlarged, A₀=A∪Vᴸ) と h46.dade (base, A=H^#) は Hypothesis46 の**別フィールド**で、A 上一致は構造に**無い**。`cases.inr` も `h46.dade=hyp.dade` は与えるが `h46.dade0.restrict A ↔ h46.dade` は与えない。
- **しかし導出可能** (producer-gate 不要): `Hypothesis.dadeMap_restrict` (S04:3641) は `IsDadeMap.unique` (S04:3442) で証明 = **Dade map は一意**。`Hypothesis` の `H : {a//a∈A}→Subgroup G` フィールド (S04:196) は `centralizer_eq_sup`+`_disjoint`+`_coprime` で **C_G(a) 内 C_L(a) の normal Hall complement = Schur-Zassenhaus 一意** ⟹ (G,A,L) から canonical ⟹ 同 (G,A,L) の 2 Hypothesis は同 dadeMap。
- **導出鎖**: φ A-supported に対し `dadeIntegralCharacterMap h46.dade0 h46.tau φ` =[`dadeIntegralCharacterMap_restrict_eq_of_support` S08CB2:1585]= `dadeIntegralCharacterMap (h46.dade0.restrict A) (h46.tau.restrict A) φ` =[`apply_of_support` S07:5243]= `(h46.dade0.restrict A).dadeMap ⟨φ⟩` =[**H-field 一意性 → IsDadeMap.unique**]= `hyp.dade.dadeMap ⟨φ⟩` =[`apply_of_support` 逆]= `hyp.tau φ`。

**▶▶ 次の brick (linchpin, 推奨 = canonicality 経路、構造改変も producer 影響も無し):**
**`dadeMap_eq_of_hypothesis` (S04 一般補題)**: 同 (G,A,L) の 2 Hypothesis hyp₁ hyp₂ → `hyp₁.dadeMap = hyp₂.dadeMap`。核 = `hyp₁.H a = hyp₂.H a` (normal Hall complement 一意; Schur-Zassenhaus、要 mathlib `Subgroup.IsComplement`/coprime uniqueness 探索) → dadeSupport 一致 → `IsDadeMap hyp₁ τ ↔ IsDadeMap hyp₂ τ` → `IsDadeMap.unique`。これで `hmapagree` (S08, h46 用 wrapper) → cX_col → assembly が連鎖 unblock。
**代替** (canonicality が重い場合): `cases.inr` に `h46.dade0.restrict A` の dadeMap が `hyp.dade` と一致する条項を追加 (producer obligation 化、2026-06-13 の CertainTypeHypothesis→Hypothesis46 強化と同型)。ただし `SibleyDadeHypothesis` core 改変ゆえ producer 全更新要 = 重い。
**正本=本 session 42 cont.⁴ 続²。capstone case-B path 完全 map。linchpin = hmapagree = dadeMap canonicality (H-field Schur-Zassenhaus 一意)。次 = `dadeMap_eq_of_hypothesis` (S04)。**

### session 42 cont.⁴ 續³: ✅ canonicality core `le_of_card_coprime_index` 着地 (commit `be9fc9ec`)
hmapagree linchpin (cont.⁴ 續²) の**群論核を 1 個 landing**: `le_of_card_coprime_index` (S08_CaseBAssembly, axiom-clean) = 「N normal + |K| coprime to N.index ⟹ K ≤ N」(K の C⧸N 像が位数 |gcd(|K|,[C:N])=1 ⟹ 自明 ⟹ K ≤ ker(mk' N)=N)。mathlib: `card_map_dvd`(H 明示第1引数!)/`card_subgroup_dvd_card`/`map_eq_bot_iff`/`card_eq_one`(Index:473)/`ker_mk'`。

**▶▶ canonicality 残り (linchpin 完成への brick 順, 確定):**
1. ✅ **Lemma A** `le_of_card_coprime_index` (done)。
2. **Lemma C = H-field 一意性** `h46.dade0.H (incl a) = hyp.dade.H a` (a∈A): 両者 C_G(a) 内で C_L(a)=`centralizerIn L a` の normal complement (`centralizer_eq_sup`=⊔, `centralizer_disjoint`=⊓⊥, `H_normalized`=normal in C_G(a), `centralizer_coprime`=coprime)。**C_G(a) へ relativize** (`.subgroupOf (Subgroup.centralizer {a})`) して Lemma A を両向き適用 → le_antisymm。要 API: `Subgroup.index_subgroupOf` / [C_G(a):H.subgroupOf]=|C_L(a)| (∵ H⊔C_L=C_G(a) ∧ H⊓C_L=⊥ ⟹ index=|complement|; `Subgroup.relindex`/`card_mul_index` 経由) + |H| coprime |C_L| (centralizer_coprime)。⚠ subgroupOf の index 計算が核。
3. **Lemma D = Hypothesis ext**: `h46.dade0.restrict A = hyp.dade` を H-field 一致 (Lemma C, 全 a) + restrict.H 補題 (S04:348 `(hyp.restrict).H a = hyp.H (incl a)`) + **構造 ext (H が唯一の data field、他 Prop は proof-irrel)** で。⚠ `S04.Hypothesis.ext` の形 (H funext + Prop 自動) を要確認。
4. **Lemma E = hmapagree**: φ A-supported に対し `dadeIntegralCharacterMap h46.dade0 h46.tau φ` = (`dadeIntegralCharacterMap_restrict_eq_of_support` S08CB2:1585) = `…(h46.dade0.restrict A)(h46.tau.restrict A) φ` = (Lemma D で Hypothesis 一致 + apply_of_support) = `hyp.tau φ`。⚠ tau (FullDadeIsometryData) 側の restrict 一致も要 (data 引数無視ゆえ dadeIntegralCharacterMap は hyp のみ依存、cont.⁷ 續³ 知見で吸収可)。
5. → `certainTypeSet_isCoherent_tau` の hmapagree 充足 → **cX_col 完成** → assembly (cX_col∪cX_irr∪cY, cont.⁴ 續² path)。

**正本=本 session 42 cont.⁴ 續³。Lemma A (canonicality 核) landed。次 = Lemma C (H-field 一意性, C_G(a) relativize + Lemma A 両向き)。**

### session 42 cont.⁴ 續⁴: Lemma C tooling 確定 (API archaeology 完了) — ~60-80 行の relativize 証明
Lemma C (`dade_H_eq` 等: 同 (G,A,L) の 2 Hypothesis の H-field 一致) の必要 API を全特定。**dadeSupport は H-field 依存** (S04:362, hCoset 経由) ⟹ uniqueness は H-field 一致が必須 (shortcut 無し)。
**tooling (確定):**
- 核 = ↥C (C=`Subgroup.centralizer {a.1}`) への relativize。各 `hyp.H a`/`Cℓ`(=`centralizerIn L a.1`) を `.subgroupOf C`。
- **`(hyp.H a).subgroupOf C` の Normal instance in ↥C**: H_normalized (∀c∈C, ∀x∈H a, cxc⁻¹∈H a) から構成。⚠ 手動 (mathlib に `normal_subgroupOf` 直接なし、`normal_subgroupOf_iff` は別物)。
- **index [↥C : (hyp.H a).subgroupOf C] = |Cℓ|**: 第2同型 `QuotientGroup.quotientInfEquivProdNormalQuotient` (mathlib QuotientGroup/Basic:293, ただし N normal in **whole group** 要 ⟹ ↥C 内で適用) + disjoint(⊓=⊥)/sup(⊔=C=⊤ in ↥C) rewrite + card transport。**または** `Nat.card C = |H a|·|Cℓ|` 積公式 + `card_mul_index`。⚠ **積公式 `card_sup_mul_card_inf` は mathlib に無い** (要自前 or 第2同型)。
- card 保存 = `Subgroup.subgroupOfEquivOfLe` (Map:294)。index/card = `IsComplement'.index_eq_card`(Complement:634)/`card_mul`(:649) も利用可だが IsComplement' 構成自体が積公式要。
- coprime = `hyp.centralizer_coprime a a` (= Coprime |H a| |Cℓ|)。
- 仕上げ = Lemma A (`le_of_card_coprime_index`, ✅) 両向き → le_antisymm → subgroupOf_le で G に戻す。
**規模 = ~60-80 行 (normal instance 構成 + 第2同型 in ↥C + card 計算 + Lemma A 適用)。well-defined だが focused pass 推奨。**
**正本=本 session 42 cont.⁴ 續⁴。Lemma C tooling 完全特定。実装は ↥C relativize の plumbing が核 (normal instance + 第2同型/積公式)。**

## 2026-06-15 (session 43, lane-b 再開, Opus): ✅✅✅ hmapagree linchpin COMPLETE + cX_col 無条件化 (commit `39c02b6e`)

**Lemma C は cont.⁴ 續⁴ の後すぐ着地済み**だった (`dade_H_eq`, commit `34670c02`; note が実装に遅れていた)。本 session で **linchpin の残り (Lemma D/E + cX_col) を完走**。全 sorry-free + axiom-clean ([propext, Classical.choice, Quot.sound] のみ、`#print axioms` 4 件確認)、full build 3830 jobs green (1.86s incremental)。

### ✅ landed (S08_CaseBAssembly, +75 行):
| 宣言 | 役割 |
|---|---|
| `dadeHypothesis_ext_of_H_eq` | **Lemma D (構造 ext)**: `S04.Hypothesis` の唯一の data field は `H` (他 8 個 Prop) ⟹ H-field 一致なら構造一致。`cases p; cases q; subst hH; rfl` (Prop fields は proof irrelevance=definitional で `rfl` が閉じる) |
| `dadeIntegralCharacterMap_congr_hyp` | **data 無視 congr**: `dadeIntegralCharacterMap` の def (S07:5233) は第2引数 `_dade` を本体で使わない ⟹ 同 hypothesis なら data 不問で同じ map。`subst h; rfl` |
| `SibleyDadeHypothesis.dade0_map_eq_tau_of_support` | **Lemma E = hmapagree linchpin**: H^#-supported φ で `dadeIntegralCharacterMap h46.dade0 h46.tau φ = hyp.tau φ`。鎖 = `restrict_eq_of_support` (symm, h46.dade0 を H^# に制限) → Lemma D (`h46.dade0.restrict (sharpImage H) = hyp.dade`, **`dade_H_eq` canonicality で `h46.dade=hyp.dade` 不要**) → `congr_hyp` + `hyp.tau` abbrev unfold |
| `SibleyDadeHypothesis.certainTypeSet_isCoherent_tau_canonical` | **cX_col 無条件化**: `certainTypeSet_isCoherent_tau` (S08CB2:1651) の `hmapagree` 仮説を Lemma E で discharge (各 φ∈zSupportedSpan は `support_subset_of_mem_zSupportedSpan` で H^#-supported)。⟹ reducible columns {μ_j} の hyp.tau-coherence が**仮説無しで**手に入る |

### 🔑 知見 (再調査不要):
- **`dade_H_eq` は canonicality ゆえ `h46.dade = hyp.dade` (cases.inr 由来) を一切要しない** — `h46.dade0.restrict (sharpImage H)` と `hyp.dade` は両方 `Hypothesis G (sharpImage H) L` で、H-field は (G,A,L) から決まる (normal Hall complement 一意)。
- **`dadeIntegralCharacterMap` は data 無視** (cont.⁷ 續³ の知見を S07:5233 def で確認: 本体 = `Classical.choose (LinearMap.exists_extend hyp.dadeLinearMap)` のみ)。
- A₀ = `sharpImage H ∪ Vᴸ` ⟹ `sharpImage H ⊆ A₀` = `Set.subset_union_left`; restrict の `hA₁_norm` = `hyp.dade.L_normalizes_A` (小さい方の集合の正規化)。

### ▶▶ 次の brick (capstone case-B assembly, cont.⁴ 續² path の残り):
1. ✅ **cX_col** = `certainTypeSet_isCoherent_tau_canonical` (done)。
2. **cX_irr** = case-A 機構 `xChainCoherent` (S08CP1:2701) を irreducible X-members 上で。要 per-step `XAdjoinStepInput` (= per-θ irr bundle 相当)。
3. **cX = cX_col ∪ cX_irr** (union)。
4. **cX ∪ cY** = `coherentXunionYset_caseB_of_glued` (S08CB2:1616, sorry-free shell)。要 ν / hmixed (= (6.8.2.3) content = `caseB_per_phi_anchored_fromYset` の anchored 公式が供給) / hpair / D / hgen。
5. capstone `sibleySetup_is_coherent` の `cases.inr` 枝 wiring (S08_CoherenceTheorems:59)。
**linchpin (hmapagree=map-agreement) は解除済 ⟹ 残りは cX_irr の per-θ bundle discharge と glue の data 供給。**
**正本=本 session 43。hmapagree linchpin + cX_col 完了 (`39c02b6e`)。次=cX_irr (xChainCoherent over irr X) or glue (coherentXunionYset_caseB_of_glued の ν/hmixed/hpair/D/hgen)。Opus 継続。**

### session 43 cont.: ✅ `caseB_column_mapagree` — column bundle の hmapagree conjunct を linchpin で discharge (commit `383556b0`)
`CaseBColBundle` (per-θ column branch, S08_CaseBAssembly:180) の conjunct #2 = `hyp.tau (μ_j − μ̄_j) = dadeIntegralCharacterMap h46.dade0 h46.tau (μ_j − μ̄_j)` を **linchpin の直接 payoff として** discharge。鎖 = `columnSum_conj_eq` (μ̄_j = μ_{χ₂⁻¹}, S06:621) → `columnDiff_support_subset` (μ_j − μ̄_j は H^#-supported, hdeg 要) → `dade0_map_eq_tau_of_support` の symm。**linchpin 以前は構成不可能だった conjunct**。sorry-free + axiom-clean、full build 3830 jobs (2.86s)。

**per-θ column bundle (CaseBColBundle) の残り conjunct の地図**:
- ✅ #1 hdeg + #2 hmapagree = `caseB_column_mapagree` (**unconditional**, `a044bc3f`)。hdeg は free fact `columnSum_inv_apply_one` (S06:464, ∑μ_{χ₂⁻¹}(1)=∑μ_{χ₂}(1)) ゆえ caseB_column_mapagree が内製 (realness 経由は不要だった)。**bundle-intrinsic 2 conjunct は side-hypothesis 無しで解放**。
- #3 hSdiff (μ_j−η₁ 系 support) / #4 htau1_mema (ZIrr) / #5,#6 hχψ/hχbarψ (⟨μ_j, η₁⟩=0 系): **η₁/a-coupled** ⟹ dispatch family の anchor 選択 (caseB_per_phi_anchored_fromYset の η₁=Y-member) に結合。**assembly phase (dispatch family 構築) で η₁/a 確定後に discharge**。
**⟹ column bundle の bundle-intrinsic 部 (hdeg + hmapagree) は完全解放; 残り 4 conjunct は dispatch family (HYBRID 組立 step 1) と一体 (η₁/a に依存)。**
**正本=本 session 43 cont.。caseB_column_mapagree unconditional landed (`a044bc3f`)。次=dispatch family 構築 (HYBRID step 1, η₁/a-coupled conjunct を巻き込む本体; caseB_per_phi_anchored_fromYset L917 の per-θ hcol/hirr 入力)。Opus 継続。**

### session 43 cont.²: 残り conjunct = X⊥Y 直交の精密 mapping (原文 (6.8.2.2)/(6.8.2.3) 照合)
dispatch family の per-θ bundle (CaseBColBundle 残り 4 conjunct + CaseBIrrBundle) を原文 `04.8.mmd` L166-214 と照合。**X⊥Y 直交が 2 レベルに分かれる**:
- **extension-level** `R(χ_i) ⊥ 𝒴^{τ_1}` = 原文 (5.3)/(5.5) = **既存補題 `inner_certainTypeExtension_columnSum_coherentYset_extension_eq_zero` (S08CB2:1449) で構築済 ✅** (η∈Yset だけから discharge; `caseB_constituentDecomposition_X_orthogonal` が消費)。
- **raw source-level** `⟨χ_i, η_j⟩=0` = 原文 "**by (4.1)**" (L166: `(η_j−η_1, χ_i−d_iχ_1)=0`)。これが **CaseBColBundle の hχψ/hχbarψ** (`⟨columnSum χ₂, a•η₁⟩=0`) の正体。

**crux = raw `⟨columnSum, η⟩=0` (η∈Yset)**: codebase で `inner_eq_zero_of_mem_span_of_pairwise_orthogonal` (S08CB2:1558) が hpair を取り span へ延ばす engine だが、**hpair 自体 (= `∀ χ∈X, ∀ η∈Y, ⟨χ,η⟩=0`) は "supplied as hpair at the glue" として defer**。columnSum=∑μ_{ij} ⟹ `⟨columnSum,η⟩=∑⟨μ_{ij},η⟩`、各 `⟨μ_{ij},η⟩=δ(μ_{ij}=η)=0` には **grid-char μ_{ij} ≠ η (∈Yset)** が要る (= 原文 (4.1) = certain-type char ⊥ S(H'))。grid-char の S/Xset membership 補題は未構築 → **次の foundational sub-problem**。
- 利用可能: `disjoint_Xset_Yset` (S08CorePart2:893)、`columnFamily_mu_sum_inner` (μ の Gram 行列, S06)、irr-Kronecker `irreducibleCharacter_inner_eq_ite`。
- 残り conjunct: hSdiff#2 (`columnSum−a•η₁` H^#-support, a=次数整合で 1 消失) / htau1_mema (ZIrr) も a/η₁-coupled。

**正本=本 session 43 cont.²。X⊥Y を 2 レベルに分離 (extension=1449 済 / raw=(4.1) 未)。次 foundational = raw grid-char 直交 `⟨μ_{ij},η⟩=0` (原文 (4.1); μ_{ij}≠η∈Yset の構造事実、§4/§6 char theory) → hχψ/hχbarψ → bundle。Opus 継続。**

### session 43 cont.³: ✅✅ raw X⊥Y 直交 (4.1) 構築 — column bundle 4/6 conjunct free (commit `60570744`)
前 cont.² で特定した crux (`μ_{ij}≠η∈Yset`) を **degree 論法で解決**: grid-char と Yset member は degree で区別される (η(1)=|W₁| ≡ 0, μ_{ij}(1)=δ+a·|W₁| ≡ ±1 mod |W₁|, |W₁|≠1)。
- `inner_columnFamily_mu_Yset_eq_zero` (per-constituent): `μ_{ij}` は `IrreducibleCharacter` (`SignedIrreducibleDifferenceFamily.mu`), η∈Yset 既約、degree-distinct → irr-Kronecker `irreducibleCharacter_inner_eq_ite`。核 = `certainType_degree_modEq` (μ(1)=sign+w₁·a) + `Yset_apply_one` (η(1)=w₁) + `sign_eq` (±1) + `W1_nontrivial` (w₁≠1)。**要 `hW1 : h46.W1 = hyp.W1`** (cases.inr 由来; capstone が供給)。
- `inner_columnSum_Yset_eq_zero` (column): `∑ᵢ ⟨μ_{ij},η⟩=0` via `inner_sum_left`。
- `caseB_column_orthogonal_Yset` (**hχψ**: `⟨columnSum,a•η₁⟩=0`) + `caseB_column_conj_orthogonal_Yset` (**hχbarψ**, via `columnSum_conj_eq`)。`Nat.cast_smul_eq_nsmul`+`inner_smul_right`。

**⟹ CaseBColBundle 6 conjunct中 4 free** (hdeg/hmapagree/hχψ/hχbarψ; 全 `hW1` だけで)。**残り 2 = hSdiff#2** (`columnSum−a•η₁` H^#-support; a=degree整合で 1 消失要 — `columnSum(1)=∑μ(1)` と `a•η₁(1)=a·|W₁|` が一致する a) **+ htau1_mema** (`hyp.tau(columnSum−a•η₁)∈ZIrr`)。両者 dispatch の weight `a=constituentWeight` に結合 (degree-matching) ⟹ dispatch family 構築時に確定。
**正本=本 session 43 cont.³。raw X⊥Y (4.1) 構築完了 (`60570744`)、column bundle 4/6 free。次=hSdiff#2/htau1_mema (weight-a coupled) or CaseBIrrBundle (irreducible 枝)。Opus 継続。**

### session 43 cont.⁴: ✅✅✅ CaseBColBundle 6/6 conjunct すべて dischargeable (commit `fbcf8e44`) + degree-match の全ピース特定
**残り 2 conjunct (hSdiff/htau1_mema) を degree-match `h1` 仮説付きで完成**:
- `caseB_column_sub_smul_support` + `caseB_column_hSdiff` (**hSdiff**): `columnSum−a•η₁` H^#-support。columnSum=Ind^L_H (`columnSum_eq_induce_H`, h46.K=H) ⟹ `support_indW2_sub_smul_subset_sharpImage` を **W2:=H で再利用** (le_refl H)。`columnSum−conj` は columnDiff_support_subset。
- `caseB_column_htau1_mema` (**htau1_mema**): `hyp.tau(columnSum−a•η₁)∈ZIrr` via `dadeIntegralCharacterMap_mem_ZIrr_of_supported` ((2.6) integrality) + `caseB_column_sub_smul_support` + `Submodule.sub_mem`(columnSum=∑μ.mem_ZIrr / η₁ irreducible mem_ZIrr)。

**⟹ CaseBColBundle 6 conjunct すべて standalone 補題化** (hdeg/hmapagree/hχψ/hχbarψ + hSdiff/htau1_mema)。hSdiff/htau1_mema は **degree-match `h1: columnSum(1)=a·η₁(1)` を仮説に取る** (他は hW1/hHK だけ)。

**🔑 degree-match の全ピース存在 (= weight reconciliation `aθ=θ(1)`)**:
- `certainType_central_restriction` (S08CB2:2119): W₂⊆Z(H) central ⟹ `Res^H_{W₂}θ = θ(1)·φ` ([Is]2.27, Schur)。kernel 条件 = `0<constituentWeight` (φ が現れる)。
- `inner_central_restrict_eq_apply_one` (S08CB2:2147): `⟨φ,Res θ⟩ = θ(1)`。
- `constituentWeight_spec` (S08CB2:806): `⟨φ,Res θ⟩ = constituentWeight`。
- ⟹ **`constituentWeight = θ(1)`**。degree match = `columnSum(1)=(Ind θ)(1)=|W₁|·θ(1)=constituentWeight·|W₁|=a·η₁(1)` (η₁(1)=|W₁| via Yset_apply_one, columnSum=Ind θ index |W₁|)。

**▶▶ 次 (well-defined)**: (1) `caseB_column_degree_match` (`columnSum χ₂(1)=constituentWeight·η₁(1)` when columnSum=Ind θ; 上記 3 補題 chain + 中心条件) → (2) **`caseB_column_bundle` 完全 constructor** (CaseBColBundle を 6 conjunct から組立、degree-match 内製) → (3) CaseBIrrBundle (irreducible 枝) → (4) dispatch family `hcol`/`hirr` discharge (caseB_per_phi_anchored_fromYset の入力) → (5) X_irr chain-adjoin + cX_col union + capstone。
**正本=本 session 43 cont.⁴。CaseBColBundle 6/6 dischargeable (`fbcf8e44`)、degree-match 全ピース特定 (constituentWeight=θ(1))。次=caseB_column_degree_match → 完全 bundle constructor。Opus 継続。**

### session 43 cont.⁵: ✅✅✅ `caseB_column_bundle` 完全 constructor — column branch `hcol` 構成可能 (commit `7fd14af0`)
degree-match core + 完全 bundle constructor:
- `constituentWeight_eq_apply_one`: `0 < constituentWeight` ⟹ `constituentWeight = θ(1)`。W₂ central ⟹ `Res^H_{W₂}θ = θ(1)·λ` (Schur `exists_central_linear_restriction`、kernel 条件不要)、`aθ = θ(1)·⟨φ,λ⟩` で ⟨φ,λ⟩=Kronecker、positivity が δ=1 強制。**一発緑** (casework + irr-Kronecker)。
- `caseB_column_degree_match`: `columnSum(1) = constituentWeight·η₁(1)`。`induce_apply_one` (`(Ind θ)(1)=H.index·θ(1)`) + `index_H_eq_card_W1` + `Yset_apply_one` (η₁(1)=|W₁|) + constituentWeight=θ(1)。
- `caseB_column_bundle`: 6 conjunct を degree-match h1 で組立 ⟹ `CaseBColBundle hyp h46 θ η₁ (constituentWeight hφ' θ)`。⚠ CaseBColBundle の def は file 後方 (line 519) ゆえ bundle constructor は CaseBIrrBundle 後ろに配置 (forward ref 回避)。

**⟹ dispatch の column-branch 入力 `hcol` (caseB_per_phi_anchored_fromYset の `hcol : ∀ i, CaseBColBundle hyp h46 i.val η₁ (constituentWeight hφ' i.val)`) が `0<constituentWeight`+中心/Hall data から構成可能。** 残り dispatch 入力:
1. **CaseBIrrBundle (`hirr`)**: irreducible 枝 (Ind θ が既約のとき)。conjunct 群は CaseBIrrBundle (S08CaseBAssembly:550) — irreducibility/non-realness/supports/ZIrr/直交スカラー。case-A Dade chain ミラー。column と類似だが既約 Ind θ。
2. **hirrAnc**: per-θ `⟨η₁, Ind θ⟩` 系 4 直交 (η₁∈Yset linear ⊥ 既約 induced)。raw X⊥Y と同型 (degree or distinct-irr)。
3. **hXaggorth/hdecomp**: (6.8.2.2) aggregate (`exists_decomposition_caseB`)。
→ これらが揃えば caseB_per_phi_anchored_fromYset 適用 → per-φ image → X_irr chain-adjoin + cX_col union + capstone。
**正本=本 session 43 cont.⁵。column hcol 完全構成可能 (`7fd14af0`)。次=CaseBIrrBundle (hirr, 既約枝) → hirrAnc → dispatch family。Opus 継続。**

### session 43 cont.⁶: CaseBIrrBundle (hirr) の精密 mapping — 8 conjunct、既約性 #1 が gating
CaseBIrrBundle (S08CaseBAssembly:519) は仮説 `(∀ χ₂≠1, columnSum χ₂ ≠ Ind^L_H θ)` (= Ind θ は column でない) の下で 8 conjunct:
1. **`IsIrreducibleCharacter (Ind^L_H θ)`** ← **gating, value↔index seam**。
2. `¬ IsReal (Ind^L_H θ)` (non-real)。
3. `((Ind θ).conj − Ind θ) H^#-support`。
4. `(Ind θ − a•η₁) H^#-support` ← **column 再利用** (`support_indW2_sub_smul` W2:=H + degree-match)。
5. `hyp.tau(Ind θ − a•η₁) ∈ ZIrr` ← **column 再利用** (`dadeICM_mem_ZIrr_of_supported`)。
6. `⟨Ind θ, a•η₁⟩=0` / 7. `⟨(Ind θ).conj, a•η₁⟩=0` ← X⊥Y (Ind θ irreducible ⊥ η₁∈Yset, degree or distinct-irr)。
8. `⟨Ind θ, (Ind θ).conj⟩=0` ← non-real + irr-Kronecker。

**🔑 #1 既約性の bridge (value↔index)**: machinery は index-level — `induce_isIrreducible_of_forall_chiRestrict_ne` (S06:902, `∀χ₂, chiRestrict χ₂ ≠ θ_K → Ind^L_K θ_K irreducible`) + (4.5.b) `exists_eq_certainType_or_induce` (S06:938)。bundle は value-level (θ:Irr ↥H, Ind^L_H θ)。橋:
- θ を h46.K=H で θ_K:Irr ↥K に transport。
- χ₂≠1: `chiRestrict χ₂ = θ_K ⟹ columnSum χ₂ = induce K (chiRestrict χ₂) = induce H θ` (4.5.a `induce_restrict_certainType_eq` + `coe_chiRestrict` + hHK) ⟹ 仮説矛盾。✓
- ⚠ **χ₂=1 edge**: `induce_isIrreducible_…` は ∀χ₂ (含 1) を要す。`chiRestrict 1 ≠ θ_K` を別途要する (column-1 = principal の構造; θ≠trivial か chiRestrict 1 の特定要)。← **次の精査点**。
- 또는 `exists_eq_certainType_or_induce` 経由 (Ind θ を μ で割り、column でないゆえ irreducible 枝) の方が χ₂=1 edge を回避できるか要検討。

**▶▶ 次**: (1) #1 既約性 bridge (χ₂=1 edge 解決; induce_isIrreducible 直用 vs exists_eq_certainType_or_induce 経由を精査) → (2) #2/#8 non-real (odd-order no-real-irr; `Yset_hasNoRealCharacters` 類似が L 全体であるか) → (3) #4/#5 support/ZIrr (column 再利用) + #6/#7 X⊥Y (Ind θ irreducible版) → (4) `caseB_irr_bundle` constructor → hirrAnc → dispatch family assembly → capstone。
**正本=本 session 43 cont.⁶。CaseBIrrBundle mapping 完了、#1 既約性が gating (value↔index seam, χ₂=1 edge)。次=#1 bridge 精査 (induce_isIrreducible 直用 vs (4.5.b) 経由)。Opus 継続。**

### session 43 cont.⁷: ✅ CaseBIrrBundle の seam-free conjunct #3/#4/#5 完了 (commits `aa536164`/`e956da40`)
column 機構を irreducible 枝に流用:
- `caseB_induce_degree_match` (`(Ind θ)(1)=constituentWeight·η₁(1)`) + `caseB_irr_sub_smul_support` (#4) + `caseB_irr_htau1_mema` (#5, `induce_mem_ZIrr`)。
- `caseB_irr_conj_diff_support` (#3): `(Ind θ).conj − Ind θ` H^#-support。**irreducibility 不要** — 両項 H-support (conj は support 不変) + 1 で消失 (Ind θ(1)=|W₁|θ(1) real, star 固定; `simp [← Nat.cast_mul]`)。

**⟹ CaseBIrrBundle 8 conjunct中 3 (#3/#4/#5) が seam-free standalone。残り 5 はすべて #1 (既約性) に gated**:
- **#1 `IsIrreducibleCharacter (Ind^L_H θ)`** = **唯一の真の gate**。`induce_isIrreducible_of_forall_chiRestrict_ne` (index-level, ∀χ₂ chiRestrict≠χ_K) を使うには (a) θ:Irr↥H → χ_K:Irr↥K transport (hHK=h46.K=H, subgroup-eq cast)、(b) χ₂≠1: chiRestrict χ₂=χ_K ⟹ columnSum χ₂=Ind θ 矛盾、(c) **χ₂=1 edge**: `chiRestrict_ne_trivial` は χ₂≠1 限定ゆえ chiRestrict 1 vs χ_K を別途。⚠ value↔index seam + transport が core difficulty。
- #2 non-real / #8 ⟨Ind θ, conj⟩=0: #1 + odd-order no-real-irr。#6/#7 ⟨Ind θ, a•η₁⟩=0: #1 + Ind θ≠η₁ (degree θ(1)>1 or X/Y disjoint; θ(1)=1 で degree collision に注意)。

**▶▶ 次 (#1 を正面から)**: induce_isIrreducible 直用の seam (transport + χ₂=1) を組む。χ₂=1 edge が重い場合は ChatGPT 相談 ([[feedback-ask-chatgpt-for-elided-gaps]], 最強モデル) で cleanest bridge を得る。#1 着地後は #2/#6/#7/#8 → caseB_irr_bundle constructor → hirrAnc → dispatch family。
**正本=本 session 43 cont.⁷。irr seam-free #3/#4/#5 done (`e956da40`)。残りは #1 既約性 seam が唯一の gate (value↔index transport + χ₂=1 edge)。次=#1 正面 (必要なら ChatGPT)。Opus 継続。**

### session 43 cont.⁸: 🎯 #1 既約性の math 完全確定 (χ₂=1 edge 解決) — 残り = ↥K↔↥H transport plumbing
**χ₂=1 edge を解決**: `(h46.columnFamily 1).mu 0 = trivialClassFunction L` (S06_CertainTypeCharacters:1015, `columnFamily_one_...`) ⟹ `chiRestrict 1 = Res_K((columnFamily 1).mu 0) = Res_K(trivial) = trivial ↥K` (coe_chiRestrict + restrict_trivial)。
**⟹ #1 の論法確定** (`induce_isIrreducible_of_forall_chiRestrict_ne (∀χ₂, chiRestrict χ₂ ≠ θ_K)`):
- χ₂≠1: `chiRestrict χ₂ = θ_K ⟹ columnSum χ₂ = induce K (chiRestrict χ₂) = induce H θ` (4.5.a `induce_restrict_certainType_eq` + coe_chiRestrict + hHK transport) ⟹ hnotcol 矛盾。
- χ₂=1: `chiRestrict 1 = trivial ≠ θ_K` ⟸ **`θ ≠ trivial`** (= structural input)。
- ⟹ `inertia θ_K = K` ⟹ `induce K θ_K` irreducible ⟹ (induce_congr で) `induce H θ` irreducible。

**残り plumbing (mechanical)**: (a) θ:Irr↥H → θ_K:Irr↥h46.K の transport (hHK : h46.K=H; `hHK ▸`/cast or `compHom (subgroup eq equiv)`)、(b) `induce h46.K θ_K = induce H θ` (`Hypothesis.induce_congr_of_subgroup_eq hHK`、columnSum_mem_S が実例)、(c) chiRestrict χ₂ ≠ θ_K の transport 越し比較。**↥K↔↥H transport が唯一の Lean 難所** (math は完結)。

**`θ ≠ trivial` の出所**: dispatch の `0 < constituentWeight hφ' θ` から (θ=trivial ⟹ Res θ=trivial ⟹ ⟨φ',trivial⟩=0=weight、φ'≠trivial 前提) 導出可、または capstone が供給。⚠ φ'≠trivial が dispatch hypothesis にあるか要確認 (caseB_per_phi_anchored_fromYset の φ 制約)。

**▶▶ 次**: (1) #1 = `caseB_irr_induce_isIrreducible (θ≠trivial) (hnotcol)` の transport plumbing を組む (ChatGPT で transport incantation を取得も可)。(2) #2 non-real (odd-order no-real-irr; L 全体の補題確認) → #8 (#1+#2)、#6/#7 (Ind θ≠η₁; θ(1)>1 で degree、θ(1)=1 は X/Y disjoint)。(3) caseB_irr_bundle constructor → hirrAnc → dispatch family。
**正本=本 session 43 cont.⁸。#1 math 完全確定 (chiRestrict 1=trivial → χ₂=1 edge は θ≠trivial で閉)。残り = ↥K↔↥H transport plumbing のみ。Opus 継続。**

### session 43 cont.⁹: ✅✅✅ #1 既約性 GATE CLEAR (`f08c89ba`) — value↔index seam 突破
`caseB_irr_induce_isIrreducible`: `Ind^L_H θ` 既約 (hnotcol = not-nontrivial-column + θ≠trivial)。transport plumbing 実装:
- θ:↥H → θK:↥h46.K = `⟨compHom (MulEquiv.subgroupCongr hHK).toMonoidHom θ, compHom_of_surjective e.surjective θ.2⟩` (既約性 transport)。
- `induce h46.K θK = induce H θ` = `S04.Hypothesis.induce_congr_of_subgroup_eq hHK hθKval`。
- `induce_isIrreducible_of_forall_chiRestrict_ne`: χ₂≠1 は columnSum 矛盾 (induce_restrict_certainType_eq + coe_chiRestrict + hcontra)、χ₂=1 は chiRestrict 1=trivial (certainType_zero_column_anchor) vs θ≠trivial (e 全射で θ(e k)=1 ⟹ θ=trivial)。
- 知見: `(θK:CF)` の coe-mk は simp で還元されない → χ₂=1 は **e.surjective で h=e k に分解**して compHom_apply 適用 (e.symm 評価より clean)。

**⟹ irr-branch の gate #1 解除。残り #2/#6/#7/#8 は #1 given で tractable**:
- #2 non-real: `Ind^L_H θ` 既約(#1) + θ≠trivial + odd-order ⟹ no-real (要 L 全体の no-real-nontrivial-irr 補題確認)。
- #8 `⟨Ind θ, conj⟩=0`: #1 + #2 (conj 既約 + distinct + irr-Kronecker)。
- #6/#7 `⟨Ind θ, a•η₁⟩=0`: #1 + `Ind θ ≠ η₁` (θ(1)>1 で degree、θ(1)=1 は X/Y disjoint)。

**⚠ 入力依存**: #1 は `θ≠trivial` を要す (dispatch の 0<constituentWeight + φ'≠trivial から、または capstone 供給)。caseB_irr_bundle constructor で θ≠trivial を input に取る。
**▶▶ 次**: #2 non-real (odd-order 補題) → #8 → #6/#7 (≠η₁) → `caseB_irr_bundle` constructor (θ≠trivial input) → hirrAnc → (6.8.2.2) aggregate → dispatch family。
**正本=本 session 43 cont.⁹。#1 既約性 GATE CLEAR (`f08c89ba`, value↔index seam 突破)。次=#2 non-real → #6/#7/#8 → caseB_irr_bundle。Opus 継続。**

### session 43 cont.¹⁰: ✅ #2 non-real (`1c52f22f`) — irr branch 5/8
- `caseB_induce_ne_trivial`: `Ind^L_H θ ≠ 1_L` (degree |W₁|·θ(1)、|W₁|>1 via W1_nontrivial; `Nat.dvd_one` で contra)。
- `caseB_irr_nonreal` (#2): 既約 Ind θ は non-real。`not_isReal_of_ne_trivial_of_odd_card'` (BrauerPermUncond:233, Peterfalvi (1.1)) + `hyp.card_L_odd` + ne_trivial。
**⟹ CaseBIrrBundle #1✅#2✅#3✅#4✅#5✅ = 5/8。残り #6/#7/#8**:
- #8 `⟨Ind θ, (Ind θ).conj⟩=0`: #1 + #2 (conj 既約 `IsIrreducibleCharacter.conj`? + Ind θ≠conj from ¬IsReal + irr-Kronecker)。**clean、次**。
- #6/#7 `⟨Ind θ, a•η₁⟩=0` / `⟨(Ind θ).conj, a•η₁⟩=0`: 既約 Ind θ ⊥ η₁∈Yset。**`Ind θ ≠ η₁` が要** (θ(1)>1 で degree distinct; θ(1)=1 だと Ind θ∈Yset の可能性 → X/Y disjoint or structural input)。⚠ ≠η₁ が #6/#7 の subtlety。caseB_irr_bundle で `Ind θ≠η₁`/`(Ind θ).conj≠η₁` を structural input に取る (capstone 供給、X-membership 由来) のが robust。
**▶▶ 次**: #8 (clean) → #6/#7 (≠η₁ input) → `caseB_irr_bundle` constructor (θ≠trivial + ≠η₁ inputs) → hirrAnc → aggregate → dispatch family。
**正本=本 session 43 cont.¹⁰。#2 done、irr 5/8 (`1c52f22f`)。次=#8 → #6/#7 → caseB_irr_bundle。Opus 継続。**

### session 43 cont.¹¹: ✅✅✅ 両 dispatch bundle (hcol + hirr) 構成可能 (commits `acca8f2f`/`d511632e`/`78e0abbe`)
irr branch 残り conjunct + 完全 constructor:
- #8 `caseB_irr_conj_inner` (`acca8f2f`): ⟨Ind θ, conj⟩=0 (#1+#2、conj 既約 `IsIrreducibleCharacter.conj`、irr-Kronecker; ne は `congrArg coe`+`coe_mk` simp)。
- #6/#7 `caseB_irr_(conj_)orthogonal_Yset` + helper `inner_irr_Yset_eq_zero` (`d511632e`): ⟨Ind θ, a•η₁⟩=0 / ⟨conj, a•η₁⟩=0、**`Ind θ≠η₁`/`conj≠η₁` を structural input** (X⊥Y distinctness、capstone 供給)。
- **`caseB_irr_bundle` (`78e0abbe`)**: 全 8 conjunct を組立 → `CaseBIrrBundle hyp h46 θ η₁ (constituentWeight hφ' θ)`。input = θ≠trivial + Ind θ≠η₁ + conj≠η₁ (+ 構造 hyp)。一発緑。

**⟹ 🎯 両 dispatch bundle constructor 完成**: `caseB_column_bundle` (hcol) + `caseB_irr_bundle` (hirr) = `caseB_per_phi_anchored_fromYset` の per-θ 入力。両者とも `0<constituentWeight` + 中心/Hall data + (irr は θ≠trivial/≠η₁ distinctness) から構成可能。

**▶▶ 次 (capstone への残り path)**:
1. **hirrAnc** (caseB_per_phi_anchored_fromYset の per-θ anchor-vs-constituent 直交 `⟨η₁, Ind θ⟩` 系 4): η₁∈Yset linear ⊥ 既約 Ind θ。`inner_irr_Yset_eq_zero` 類似 (η₁≠Ind θ)。
2. **dispatch family 構築**: `{θ//0<constituentWeight}` 上で hcol/hirr を dispatch (caseB_constituentDecomposition 値レベル分岐)、caseB_irr_bundle/caseB_column_bundle を供給。θ≠trivial/≠η₁ の structural input を解決 (degree θ(1)>1 ⟹ ≠η₁、or X-membership)。
3. **(6.8.2.2) aggregate** `hXaggorth`/`hdecomp` (`exists_decomposition_caseB` S08:126)。
4. → caseB_per_phi_anchored_fromYset per-φ image → HYBRID 組立 (X_irr chain-adjoin + cX_col union) → capstone `sibleySetup_is_coherent` (S08_CoherenceTheorems:59)。
**正本=本 session 43 cont.¹¹。両 bundle (hcol+hirr) constructor 完成 (`78e0abbe`)。次=hirrAnc → dispatch family → aggregate → HYBRID → capstone。Opus 継続。**

### session 43 cont.¹²: ✅ 全 per-θ dispatch 入力 (hcol/hirr/hirrAnc) + distinctness 機構完成 (commits `1ba0b967`/`a938c3ec`)
- **distinctness 機構**: `inner_Yset_irr_eq_zero` (Y-member ⊥ 別既約、η first)、`caseB_induce_ne_Yset`/`caseB_induce_conj_ne_Yset` (`Ind θ ≠ η`/`conj ≠ η` from `θ(1)≠1` degree)。⟹ **`θ(1)≠1` 単一 input が θ≠trivial + 全 ≠η₁ distinctness を出す** (φ≠trivial 不要)。
- **`caseB_hirrAnc`**: dispatch の hirrAnc (per-θ anchor 4-直交) を `∀i, θ(1)≠1` (hnonlin) から構成。Ind θ 既約(#1) + inner_Yset_irr_eq_zero。⚠ forward-ref 回避で caseB_induce_conj_ne_Yset 後ろに配置 (Python move)。

**⟹ 🎯 caseB_per_phi_anchored_fromYset の 3 per-θ 入力すべて構成可能**: hcol=`caseB_column_bundle`、hirr=`caseB_irr_bundle`、hirrAnc=`caseB_hirrAnc`。残り入力 = (6.8.2.2) aggregate `hXaggorth`/`hdecomp` (`exists_decomposition_caseB` S08CB2:126、存在) + `hnonlin` (∀i, θ(1)≠1)。

**📋 残り capstone への multi-step assembly (§8 case-B 中核、多ターン)**:
1. **hnonlin** `∀i:{θ//0<weight}, θ(1)≠1`: 中心制限 `Res_{W₂}θ=θ(1)·φ` (φ=source) + φ≠trivial + W₂⊆H' ⟹ θ 非線形。要 φ≠trivial (capstone 文脈 or 中心制限 chain)。
2. **dispatch family 構築**: hcol/hirr/hirrAnc + aggregate + hnonlin を caseB_per_phi_anchored_fromYset に wiring → per-i anchored image (concrete)。
3. **HYBRID 組立** (cont.⁷續⁵): per-φ image を diagonal data に、X_irr を cY に `retarget_isCoherent_of_supportedDecomposition` で chain-adjoin + cX_col (`certainTypeSet_isCoherent_tau_canonical`) を §7 union → coherence on Xset。
4. **cX ∪ cY glue**: `coherentXunionYset_caseB_of_glued` (S08CB2:1616, sorry-free shell)。
5. **case split + Frobenius**: capstone `sibleySetup_is_coherent` (S08_CoherenceTheorems:59) で hyp.cases 分岐、Frobenius は既存 discharge、CertainType は h46 から上記組立。
**正本=本 session 43 cont.¹²。全 per-θ dispatch 入力構成可能 (`a938c3ec`)。残り = hnonlin + family wiring + HYBRID + glue + case split (multi-turn)。infra 完成。Opus 継続。**

### session 43 cont.¹³: ✅ `caseB_hnonlin` — 最後の dispatch 入力 hnonlin 構成可能 (commit `d8490672`)
- **`caseB_hnonlin`** (S08_CaseBAssembly, caseB_hirrAnc 直前): `∀ i:{θ//0<weight}, θ(1)≠1` を **2 入力**から構成 — `W₂.subgroupOf H ≤ commutator ↥H` (= CertainType `cert.W2 ≤ ⁅H,H⁆`) + `φ≠trivial` (= X-side selector、compHom-equiv 形)。論法: degree-1 θ は ⁅H,H⁆ 上 trivial ⟹ `Res^H_{W₂}θ=1_{W₂}` ⟹ Clifford weight `⟨φ,Resθ⟩=⟨φ,1⟩=0` (φ≠1 既約の直交) ⟹ `constituentWeight_pos_iff` と矛盾。
- **支持補題** (LinearCharacter.lean、`apply_commutatorElement…` の直後): `IsIrreducibleCharacter.apply_eq_one_of_mem_commutator_of_apply_one_eq_one` — degree-1 既約指標は **commutator 部分群全体**で trivial (既存「kills commutators」を induced `χ:G→*ℂˣ` (`exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one`) + `Subgroup.commutator_le` で部分群レベルに持ち上げ; ℂˣ 可換ゆえ `ker χ ⊇ ⁅⊤,⊤⁆`)。reusable な一般事実なので RepresentationTheory に配置。
- axiom-clean ([propext,Classical.choice,Quot.sound])、full build 3832 jobs + AxiomsCheck green (1m23s; LinearCharacter upstream 触りゆえ大規模再ビルド)。

**⟹ 🎯 caseB_per_phi_anchored_fromYset の per-θ 入力 (hcol/hirr/hirrAnc) を駆動する単一 input `hnonlin` が構成可能に。残り capstone path**:
1. ✅ ~~hnonlin~~ (本 cont.¹³ = `caseB_hnonlin`)。
2. **dispatch family 構築** (次): `caseB_column_bundle`(hcol) + `caseB_irr_bundle`(hirr) + `caseB_hirrAnc`(hirrAnc) を `caseB_hnonlin` 由来の hnonlin 付きで `caseB_per_phi_anchored_fromYset` に wiring → per-i anchored image。⚠ **要精査**: 同 theorem の RHS が `(caseB_phi_family hyp h46 hW2H hφ' hcol hirr i).X` を参照 → 内部構成した hcol/hirr が statement に出る (caseB_phi_family の `.X` data 依存)。caseB_phi_family の構造を読んで「hcol/hirr を hyp に取り RHS をその family で書く」か「.X が proof-irrelevant に閉じる」かを決める。
3. HYBRID 組立 (per-φ image → diagonal data, X_irr chain-adjoin + cX_col §7 union)。
4. cX∪cY glue (`coherentXunionYset_caseB_of_glued` S08CB2:1616, sorry-free shell)。
5. case split + Frobenius → capstone `sibleySetup_is_coherent` (S08_CoherenceTheorems:59)。
**正本=本 session 43 cont.¹³。hnonlin 構成可能 (`d8490672`)。次=dispatch family wiring (`caseB_phi_family` の `.X` data 依存を精査してから statement 設計)。Opus 継続。**

### session 43 cont.¹⁴: ✅ `caseB_hcol` + `caseB_hirr` — dispatch trio 完成 (commit `e011f127`)
- **`caseB_hcol`** (S08_CaseBAssembly, caseB_irr_bundle 直後): `∀i, CaseBColBundle…` = `fun i => caseB_column_bundle … i.property hη₁`。非線形性 input 不要 (column witness `columnSum χ₂ = Ind^L_H θ` で gate)。要 `hW1 : h46.W1 = hyp.W1`。
- **`caseB_hirr`**: `∀i, CaseBIrrBundle…` = `fun i => caseB_irr_bundle …`、3 structural input (θ≠1 / Ind θ≠η₁ / conj≠η₁) を単一 `hnonlin` から (`caseB_induce_ne_Yset`/`caseB_induce_conj_ne_Yset` の degree 不一致)。
- 両者 axiom-clean、leaf build green (**S08_CaseBAssembly は true leaf = 誰も import しない** → full build 不要)。⚠ `[Fintype ↥H]` unusedFintypeInType warning は sibling `caseB_hirrAnc` (L753) と同じ既存パターン (bundle constructor が Fintype 要求ゆえ Finite 化不可、非 fatal)。

**⟹ 🎯 dispatch 入力トリオ (hcol=`caseB_hcol` / hirr=`caseB_hirr` / hirrAnc=`caseB_hirrAnc`) すべて構成可能。`caseB_per_phi_anchored_fromYset` (per-φ anchored image producer, L1546) は構造データ + (W₂⊆⁅H,H⁆, φ≠1)[hnonlin] + hW1 + aggregate(hXaggorth/hdecomp) から完全に feed 可能。**

**📋 残り = 🔴 HYBRID 組立 (step 3、本節の主残務・多ターン) → glue (step 4) → case split (step 5)**:
- **chain-adjoin engine 判明**: `retarget_isCoherent_of_supportedDecomposition` (S07_Coherence:4031)。入力 = `hS₁ : IsCoherent τ S₁ A` + `Da : CharacterPsiDecomposition τ χ (a•chi1)` (= `caseB_phi_family … i`、χ=Ind θ, a=weight, chi1=η₁∈S₁) + χ/χ̄ 正規直交 (`hχχ` 等) + `hperElem` (S₁ image ⊥ Da.imageFamily.imageSet) + `hgen`。出力 = `IsCoherent τ (S₁∪{χ,χ̄}) A`。⟹ 1 既約 constituent ごとに {Ind θ, conj} を adjoin。
- **🔬 次ターン RECON (HYBRID 設計の前提)**:
  1. **Xset W2 の構造** (`hyp.Xset W2` = S−S(W2)) と、cX_col (μ_j columns) + X_irr (既約 Ind θ) がどう Xset を被覆/分割するか (`mem_Xset`)。
  2. **cX_col** = `certainTypeSet_isCoherent_tau` (S08CB2:1651、`hmapagree` 要) を base coherence にできるか。
  3. **chain-adjoin の順序**: base = cX_col から X_irr family を fold-adjoin する設計 (`retarget_isCoherent_of_supportedDecomposition` を ∀i で畳む) か、別の base か。
  4. **case-A テンプレート**: case-A の cX 構築 (`nonempty_coherent_S_caseA_of_frobenius` 周辺) を読んで HYBRID の雛形にする (case-A 完了済ゆえ最良の参照)。
  5. `hperElem` (S₁ image ⊥ R(χ)) の供給元 — seam-1 orthogonality (`columnDecompositionTau_X_orthogonal` 等) が既にあるか。
**正本=本 session 43 cont.¹⁴。dispatch トリオ完成 (`e011f127`)。次=HYBRID 組立の RECON (Xset W2 構造 + cX_col base + chain-adjoin 順序 + case-A テンプレート)。Opus 継続。**

### session 43 cont.¹⁵: 🔬 HYBRID→capstone landscape を完全 RECON (commit: 本 note のみ)
Lean commit なし。dispatch トリオ完成後の残務 = **cX 組立 (T8-analog, 最重 node) + capstone wiring** を engine/既存部品レベルで完全に地図化。

**判明した構造 (Z=W₂ ルート、blocker note `s08_6_8_blocker_central_Z.md` で確定済)**:
- case-B は **Z = W₂** ルート (Cor 2.30 が中心 Z 要求、⁅H,H⁆⊄Z(H) ゆえ ⁅H,H⁆ では degree bound 不成立)。X := `hyp.Xset W2`、Y := `Yset = S(⁅H,H⁆)`。**`Xset W2 ∪ Yset ⊊ S` (filtrationDiff = S(W₂)∖S(⁅H,H⁆) が gap)** — Frobenius の `Xset⁅H,H⁆∪Yset=S` ショートカットは case-B では使えない (意図的に elide)。→S は blocker note 「correct path」。
- **anchor 解決**: per-φ images (`caseB_per_phi_anchored_fromYset`, η₁-anchored `τ(Ind θ−aη₁)=X−a·cY.ext η₁`) は **glue の diagonal D / extension 値**。cX 自体は X-internal anchor (case-A の `xBaseBlock`) で組む。

**engine 在庫 (確認済)**:
- `retarget_isCoherent_of_supportedDecomposition` (S07:4031) — **任意 τ** (incl. hyp.tau)、`Da:CharacterPsiDecomposition τ χ (a•chi1)` (= per-φ image) + 正規直交 + `hperElem` + `chi1∈S₁` から `IsCoherent τ (S₁∪{χ,χ̄})`。⚠ chi1 (anchor) ∈ S₁ 要 → 単独で pure-cX には不向き (chi1=η₁∉Xset)。
- `xChainCoherent` (CorePart1:2701) — Dade map 上の conjugate-pair fold (`coherentOfPairChainCover` + `XAdjoinStepInput.adjoin`)。`XAdjoinStepInput` (CorePart1:2583, ~25 field) = per-step ingredient (orthonormal χ/χ̄ + member-family + degree bound `2a<∑deg²` + S₁⊥)。多くの field は `CaseBIrrBundle` から既に出る。
- `per_phi_anchored_image` (CB2:1908) — per-φ image family の汎用 producer (`caseB_per_phi_anchored_fromYset` がその case-B 実体)。
- **base 部品**: `certainTypeSet_isCoherent_tau_canonical` (S08CB:170, **unconditional**, μ_j columns coherence per nontrivial k)。
- **glue shell**: `coherentXunionYset_caseB_of_glued` (CB2:1616, sorry-free) — cX + ν + agreement/hmixed/D/hgen → `IsCoherent hyp.tau (Xset W2 ∪ Yset)`。
- **capstone template (Frobenius)**: `coherentS_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner` (S08CT:388 経由) — Z=⁅H,H⁆ で直接 S。case-B はこの mirror を Z=W₂ で。
- **set bridge**: `Xset_commutator_eq_Xset_union_filtrationDiff` (CorePart2:877)。
- **case-A pure-cX テンプレート**: `Xset_centralCommutator_isCoherent_of_irreducible_X` (CoreCore:1046) — 但し **全 X-member 既約**前提 (common-index prime-power degree machinery + xBaseBlock anchor)。case-B は **mixed** (columns μ_j + irreducible Ind θ) ゆえ直接流用不可。

**🔴 残務 (multi-turn、優先順)**:
1. **cX = `IsCoherent hyp.tau (Xset W2)` 組立** [最重・T8-analog]: columns (certainTypeSet_isCoherent_tau_canonical) を base に、irreducible Ind θ を per-φ images 経由で adjoin。mixed ゆえ case-A builder 流用不可 — 新規 builder か `retarget_isCoherent_of_supportedDecomposition` の反復。
2. **→S route** (`Xset W2 ∪ Yset ⊊ S` の gap = filtrationDiff): blocker note「correct path」を実装 (Frobenius と異なる)。
3. **capstone case-split wiring**: `sibleySetup_is_coherent` (S08CT:59) で hyp.cases 分岐 (Frobenius=既存 builder / CertainType=h46+W₂+φ を供給して上記 cX→glue→S)。

**▶▶ 次ターン具体第一手 (推奨)**: cX 組立の最小単位から着手。候補 = (a) **gated skeleton**: `coherenceTarget_caseB_of_cX_of_glueData` (cX+ν+D+hgen を hyp に取り CoherenceTarget を産む sorry-free 補題、Frobenius builder を mirror) で wiring を前倒し ([[feedback-gated-endpoint-skeleton-pattern]])、cX/route-to-S を named residual 化。または (b) cX の prerequisite 正規直交補題 (X-member 像どうし / column⊥irr) を個別に。**(a) を推奨** (robust、capstone 構造を確定、cX を孤立 obligation 化)。
**正本=本 session 43 cont.¹⁵。HYBRID→capstone 完全地図化 (Z=W₂ ルート確定、engine 在庫確認)。次=cX wiring の gated skeleton (`coherenceTarget_caseB_of_cX_of_glueData`) 着手。Opus 継続。**

### session 43 cont.¹⁶: 📖 教科書 (6.8.2)/(6.8.3) 原文照合で残務構造を確定 (commit: 本 note のみ)
Lean commit なし。`references/peterfalvi/04.8` L156-244 を直読し、cont.¹⁵ の推測を**原文で確定/訂正**。⚠ **残務は heavy core で quick-win 無し**と判明 (正直に記録)。

**原文構造 (04.8 L156-244)**:
- **(6.8.2) [L224]**: case-B の `X∪Y` coherence は **τ₂ を per-φ images から直接構成** (cX を別途作って glue、ではない)。τ₂: ℤ[X∪Y]→ℤ[Irr G]、τ on ℤ[X∪Y,L^#] 一致 + η₁^τ₂=Y。(6.8.2.3) `(χ−aη₁)^τ=X₁−aY` (= 私の per-φ images) が内積保存を与える。
- **(6.8.3) [L228-244]**: S coherence。**case (A)/(B) 一様** — break pair S₂={ψ,ψ̄}⊆S, S₁⊇X∪Y coherent だが S₁∪S₂ not、Thm (5.6) で degree bound → 矛盾。**唯一の差 = 最終算術** [L244]: case A `|Z|−1≥2|W₁|` (W₁ FPF on Z); **case B `|H:Z|≥(2|W₁|+1)²`** (W₁ FPF on H/H′ かつ H′/Z)。

**確定した構造的事実**:
- **X (=Xset W2) は mixed**: 非自明 χ₂ の column μ_j (columnSum, **可約**, W₂⊄ker ゆえ ∈X) + 既約 Ind θ。⟹ retarget (単一既約 pair) は既約 X-member のみ、可約 column は cX_col 集合 coherence。
- **2 ルート**: (1) **separate cX + glue** (`coherentXunionYset_caseB_of_glued` が要求する cX:IsCoherent (Xset W2) を別途構築 — case-A `Xset_..._of_irreducible_X` は全既約前提ゆえ mixed では流用不可、新規 ~300 LOC)。(2) **incremental adjoin** (cY から retarget で X-member を順次 adjoin、per-φ images = supported decomposition、anchor η₁∈cY=S₁ ✓ — 原文 (6.8.2) τ₂ に一致、より軽い)。可約 column は cX_col を union。**(2) 推奨** (per-φ images を直接使う、原文整合)。
- **(6.8.3) L4 は case-A `false_of_coherentXunionYset_of_not_coherentS` (CB2:3439) を mirror** だが: (i) Z=W₂、(ii) 算術 = `false_of_w2_break_arith` 新規 (case-A `false_of_centralCommutator_break_arith` CB2:3094 は `2w1≤cZ-1` 前提、case-B は `|H:W₂|≥(2w1+1)²`)、(iii) case-B (5.6) X-sum bound (X が mixed ゆえ case-A `xSum_le_two_psi` と異なる)、(iv) case-B S-facts (S に可約 member)。

**🔴 正直な評価**: 残務 (X∪Y coherence assembly + (6.8.3) L4 + capstone wiring) は **interlocking heavy core、各 ~100-300 LOC、clean quick-win 無し**。dispatch 層 (hnonlin/hcol/hirr/hirrAnc, cont.¹³-¹⁴) は完了。ここからは**大きいビルディングブロック単位**の multi-session push。

**▶▶ 次ターン具体第一手 (確定)**: **Route (2) の第一歩 = 既約 X-member 単一 adjoin**。`retarget_isCoherent_of_supportedDecomposition` (S07:4031) を per-φ image (`caseB_per_phi_anchored_fromYset` の Da) + CaseBIrrBundle 正規直交で instantiate し、cY (or 既adjoin prefix) に {Ind θ, conj} を adjoin する補題。hperElem (prefix 像 ⊥ R(Ind θ)) / hgen の供給を精査。これが fold (xChainCoherent 類似) の per-step。**(cont.¹⁵ の gated-skeleton 推奨は撤回** — glue shell が要求する cX は Route 1 専用で、Route 2 = 原文整合かつ軽い)。
**正本=本 session 43 cont.¹⁶。原文照合で (6.8.2)=τ₂ direct / (6.8.3)=一様 A/B (算術のみ差) と確定。残務 heavy core (quick-win 無し)。次=Route 2 既約 X-member 単一 adjoin 補題。Opus 継続。**

### session 43 cont.¹⁷: ✅ `adjoin_irr_nonreal_of_supportedDecomposition` — fold per-step (commit `e72771ad`)
- **`adjoin_irr_nonreal_of_supportedDecomposition`** (S08_CaseBAssembly 末尾、general/leaf-local): `retarget_isCoherent_of_supportedDecomposition` の wrapper。χ 既約 + non-real + chi1 既約 から 5 正規直交 hyp (⟨χ,χ⟩=⟨χ̄,χ̄⟩=⟨χ₁,χ₁⟩=1, ⟨χ,χ̄⟩=⟨χ̄,χ⟩=0) を discharge (irr Kronecker `if`、`caseB_irr_conj_inner` mirror + `inner_conj_symm`)。`noncomputable def` (IsCoherent=Type)。残す S₁-依存入力 = hperElem/hχ_S1/hχbar_S1/chi1∈S₁/htau1_*/hY/hgen は fold caller が供給。axiom-clean、leaf green。⚠ 真の general ゆえ split (0070) で S07 へ lift 候補。

**⟹ X∪Y fold の per-step (orthonormality) 完成。残 fold hard parts (次)**:
1. **hperElem** (prefix 像 ⊥ `Da.imageFamily.imageSet` = R(Ind θ)): 既約枝 prefix 直交。case-A `pairCover_orthogonal_to_prefix` (CorePart1:2735) は全既約前提 → case-B prefix は column 混在ゆえ要適応 (or column ⊥ irr-R(χ) を別途)。
2. **column base**: cY ∪ cX_col (`certainTypeSet_isCoherent_tau_canonical`) を §7 union (cross-orthogonality 要) で base coherent set 化 → そこに既約を fold-adjoin。
3. **htau1_chi1 / hY / hgen**: per-φ image (`caseB_phi_family`) の構造から (Da.tau1=hyp.tau via `caseB_phi_family_tau1`、Da.Y=per_phi の Y 成分)。
4. **fold 全体**: `xChainCoherent` 類似で base から X-member を順次 adjoin (per-φ image = Da)。
**正本=本 session 43 cont.¹⁷。fold per-step orthonormality wrapper 完成 (`e72771ad`)。次=fold hard parts (hperElem prefix⊥R(χ) / column base union / htau1-hY-hgen 供給)。Opus 継続。**

### session 43 cont.¹⁸: 🧭 ルート決定 — Route 1 (cX X-internal + glue)、cX は xChainCoherent + column base (commit: 本 note のみ)
Lean commit なし。consumer 解析でルート曖昧性を解消し cX 構築法を確定。⚠ 残務は heavy T8 (multi-session) 継続。

**決定的事実 (consumer + engine 解析)**:
- **per-φ images は未 consume** = Route 1 の **glue diagonal D** 用 (`caseB_per_phi_anchored_fromYset` の `hdecomp`/`hXaggorth` が glue shell `coherentXunionYset_caseB_of_glued` の D/`hDτ` と一致)。⟹ **Route 1 が intended**: cX (Xset W2 coherence) を別途構築 → cY と glue (D=per-φ images)。cY=`coherentYset` 済、D 構築可 (dispatch trio + `exists_decomposition_caseB` aggregate)。**残 = cX。**
- **cX は X-internal 構築** (per-φ images は η₁-anchored ゆえ pure-X には非使用)。case-A `Xset_..._withCover_of_irreducible_X` (CorePart2:4294) は **全既約前提** (`hX`) ゆえ mixed には流用不可。
- **🔑 但し raw `xChainCoherent` (CorePart1:2701) は base `S₀` を一般 coherent 集合に取れる** (全既約不要)。かつ **`hyp.tau` = `dadeIntegralCharacterMap hyp.dade (fullDadeIsometryData hyp.hconj)`** (4294 が hyp.tau 結論で内部 xChainCoherent 呼ぶ ⟹ 一致、map mismatch 無し)。⟹ **mixed cX = xChainCoherent で base S₀=columns (cX_col coherent)、既約 pair を adjoin** で到達可能。

**🔴 cX 構築の残り難所 (次以降)**:
1. **column base S₀**: columns 全体 (= ⋃ degree-class ごとの `certainTypeSet h46 k`) の coherence。⚠ **multi-degree complication** — columns は degree class で分かれ各 `certainTypeSet k` が coherent (cX_col)、その**和**の coherence が要 (degree class 間 union)。
2. **cover dichotomy**: `∀ φ ∈ Xset W2, (column ∃χ₂≠1 columnSum=φ) ∨ IsIrreducibleCharacter φ` (dispatch by_cases + `caseB_irr_induce_isIrreducible`)。
3. **hstep (XAdjoinStepInput, ~300 LOC monolith)**: 既約 X-member ごとの member-family + degree bound `2a<∑deg²`。case-A `hstep` の mixed 適応 (prefix に column 混在 ⟹ `pairCover_orthogonal_to_prefix` 全既約版は不可、column⊥irr 直交を別途)。
4. xChainCoherent 組立 → cX → glue shell (D=per-φ) → X∪Y coherence → (6.8.3) L4 → CoherenceTarget。

**▶▶ 次ターン具体第一手**: cover dichotomy (#2、set 構造、tractable) を build — `caseB_Xset_member_column_or_irreducible`。dispatch by_cases で column witness or `caseB_irr_induce_isIrreducible` (θ≠trivial は W₂⊄ker θ から)。

**⏱ 状況メモ (正直)**: dispatch 層 (hnonlin/hcol/hirr/hirrAnc + per-step adjoin) 完了後、frontier は **heavy T8 mixed cX** (multi-session、clean quick-win 無し)。loop の per-turn context reload で route 再考が嵩んだ。次以降は cover→base union→hstep を順次 build (RECON 偏重を脱する)。ユーザーが望めば (a) loop 継続 / (b) 集中 workflow (要 opt-in) / (c) B を signature-pin (endpoint B/C/D/E) へ redirect も可。
**正本=本 session 43 cont.¹⁸。Route 1 確定 (cX=xChainCoherent+column base, hyp.tau=Dade map)。次=cover dichotomy build。Opus 継続。**

### session 43 cont.¹⁹: ✅ `caseB_induce_column_or_irreducible` — cover dichotomy per-θ (commit `69e36299`)
非自明 θ で `Ind^L_H θ` = column (∃χ₂≠1 columnSum=Ind θ) ∨ irreducible。by_cases + `caseB_irr_induce_isIrreducible`。axiom-clean、leaf green。⟹ cover の per-θ 部品完成。次 = (a) Xset-level cover (hyp.Xset W2 の各 member を Ind θ 化して dichotomy 適用、W₂↔h46.W2 同定要)、(b) column base union (multi-degree `certainTypeSet` 和の coherence)、(c) hstep (XAdjoinStepInput, 既約 adjoin の member-family/degree)。**正本=本 cont.¹⁹。次=Xset-level cover or column base union。Opus 継続。**

### session 43 cont.²⁰: 🧱 cX/X∪Y = heavy T8 確定 + 設計テンション特定 (commit: 本 note のみ)
Lean commit なし (engine 在庫を exhaustive に確認し残務の本質を確定)。dispatch 層 (hnonlin/hcol/hirr/hirrAnc) + per-step adjoin (`adjoin_irr_nonreal_of_supportedDecomposition`) + cover dichotomy (`caseB_induce_column_or_irreducible`) は完了 (4 Lean commits)。ここから先 = **heavy T8** (multi-session)。

**🔑 設計テンション (要解決、loop-cadence では不向き)**:
- **教科書 (6.8.2)** = τ₂ を ℤ[X∪Y] 上に**直接**構成 (cX を別途作らない)。τ₂ は supported lattice で τ 一致 + η₁^τ₂=Y、生成集合 {ℤ[X∪Y,L^#]∪{η₁}} 上で内積保存 (per-φ images = (6.8.2.3))。
- **repo §7 engines** は全て (a) **単一 pair adjoin** (`retarget_isCoherent_of_supportedDecomposition` (4031) / `…_and_memberFamily` (4126)、{χ,χ̄} 一組) か (b) **cX+glue** (`coherentUnion_of_glued*` (4407-4581)、別途 `cX:IsCoherent (Xset W2)` 要)。**教科書 τ₂ (直接 X∪Y) に対応する engine が無い。**
- ⟹ 2 択: **(I) cX を構築** (repo engines 用) — mixed set ゆえ重い: multi-degree column base (各 `certainTypeSet h46 k` per degree class を union) + 既約 adjoin via xChainCoherent + **hstep (XAdjoinStepInput ~300 LOC、member-family/degree-bound)**。⚠ column の既約 constituent と irr X-member の重複/直交が要精査 (naive orthogonal adjoin が崩れうる)。 **(II) 新 §7 engine** = 教科書 τ₂ (cY + per-φ image family + generator 内積保存 → IsCoherent (X∪Y) 直接、retarget を family 化、~100-150 LOC)。
- **(II) が教科書整合かつ cX の mixed 複雑性を回避** (η₁ anchor で全 X-member を cY に接続、separate cX 不要) — **推奨**。但し新 engine の正当性証明 (generator が ℤ[X∪Y] を張る + isometry) は要構築。

**▶▶ 次の focused session の第一手**: **(II) τ₂ family engine** を S07 に構築 — `coherentUnion_of_supportedDecompositionFamily` (hS₀:IsCoherent S₀ + family Dχ:per-member supported decomposition anchored in S₀ + 正規直交 + generator-span hyp → IsCoherent (S₀∪T))。retarget の family 一般化。これが (6.8.2) τ₂ = X∪Y coherence を per-φ images から直接与え、cX/multi-degree/hstep を**全て回避**。

**⏱ 正直な status**: endpoint A は heavy T8 + 設計判断点。dispatch/cover 層 (4 commits) 完了。残りは focused multi-turn build (τ₂ family engine 推奨)。loop の per-turn reload で route/engine 再考が嵩んだ — 次は (II) を腰を据えて build。ユーザー裁量: (a) loop 継続で (II) build / (b) 集中 workflow (要 opt-in) / (c) B を signature-pin (endpoint B/C/D/E) へ redirect。
**正本=本 cont.²⁰。cX/X∪Y=heavy T8、教科書τ₂ vs repo cX+glue の設計テンション特定。推奨=(II) S07 τ₂ family engine 新設。Opus 継続。**

### session 43 cont.²¹: 🔍 cX fold の orthogonality blocker = μ_{ij}∈X 構造 (commit: 本 note 1 行)
cX を xChainCoherent fold で組むには X-member が pairwise orthogonal 要。既存: `inner_columnSum_Yset_eq_zero` (column⊥Y, S08CBA:250)、`ind_cross_inner_eq_zero` (cross-column, S06CTChar:448)。**未解決 = 既約 X-member (irr branch Ind θ) ⊥ column か**: ⟨Ind θ, columnSum χ₂⟩=∑⟨Ind θ, μ_{ij}⟩、これが 0 ⟺ Ind θ ≠ 各 grid char μ_{ij}。irr branch は Ind θ≠columnSum (和) しか与えず、Ind θ≠μ_{ij} (個別) は **μ_{ij}∈X か否か**に依存。μ_{ij} は SignedIrreducibleDifferenceFamily の σ-image (certain subgroup 上)、H-induce 個別ではない ⟹ **μ_{ij}∉X が有力 (未証明)**。**▶ 次ターン: μ_{ij}∈X を S06 certain-type 構造で確定 → 確定すれば column⊥irr orthogonality lemma を build (cX fold 解禁)。確定できねば τ₂ engine (option II) か focused 集中 build へ。** dispatch/cover/per-step 層 = 4 commits 完了。endpoint A 残 = heavy cX (この orthogonality + hstep ~300LOC + fold + glue + L4)。

### session 43 cont.²²: ✅ `caseB_inner_irr_columnSum_eq_zero` — irr⊥column (cont.²⁰/²¹ の悲観を訂正) (commit `cc0c3aa0`)
**cont.²⁰/²¹ の「μ_{ij}∈X 構造が未解決ゆえ irr⊥column が blocked」は誤り** — degree-mod-|W₁| 論法で**直接証明可能**だった: Ind θ degree=|W₁|·θ(1)≡0、grid char μ_{ij} degree≡±1 (certainType_degree_modEq)、|W₁|≠1 ⟹ Ind θ≠μ_{ij} ⟹ ⟨Indθ,columnSum⟩=∑⟨Indθ,μ_{ij}⟩=0 (`inner_columnFamily_mu_Yset_eq_zero` の X⊥Y 論法を Y-degree|W₁|→|W₁|·θ(1) で mirror)。axiom-clean、leaf green。
**⟹ cX fold の orthogonality 群は揃った**: column⊥Y (`inner_columnSum_Yset_eq_zero`)、cross-column (`ind_cross_inner_eq_zero`, images)、**irr⊥column (本 commit)**、irr⊥irr (Kronecker)。**cX fold は当初思ったより tractable。**
**▶ 次: cX fold の残り** = (a) column base coherence (cX_col / certainTypeSet, 単一 k は `certainTypeSet_isCoherent_tau_canonical`; multi-degree は要 union or 単一 class 確認)、(b) **hstep (XAdjoinStepInput)** = 既約 adjoin の member-family+degree-bound (case-A `hstep` の mixed 適応、orthogonality は本群で供給可)、(c) xChainCoherent 組立。次手 = hstep の最小 piece or column base 確認。
**正本=本 cont.²²。irr⊥column 完成 (`cc0c3aa0`)、orthogonality 群 揃う、cX fold tractable と判明。次=hstep/column base。Opus 継続。**

### session 43 cont.²³: ✅ orthogonality/prefix infra COMPLETE (8 commits) — 残=heavy gates (hstep core / L4)
cont.¹⁹-²³ で case-B X-fold の orthogonality 層を完成 (5 commits): cover dichotomy (`caseB_induce_column_or_irreducible`), irr⊥column (`caseB_inner_irr_columnSum_eq_zero`), columnSum-cross (`inner_columnSum_cross_eq_zero`), conj⊥column (`caseB_inner_irr_conj_columnSum_eq_zero`), column-base 束 (`caseB_irr_orthogonal_columnBase` = hχ_S1/hχbar_S1 の column 部分)。+ session 前半の dispatch trio + per-step adjoin = **session 43 で計 8 Lean commits**。
**⟹ cX fold の per-step orthogonality 入力は揃った** (χ/χ̄ ⊥ column base; prior irr pair は Kronecker)。
**🔴 残る heavy gates (loop-quick-win 無し、focused build 要)**:
1. **hstep core** = `XAdjoinStepInput` の member-family + (6.6) degree-bound `2a<∑deg²`。(6.6) Cor 2.30 bound は Z-generic (`exists_source_primePow_centralBound_of_mem_Xset`、中心 W₂ で適用可) ⟹ 大半 case-A 流用可。但し member-family が mixed prefix (column+irr) ゆえ case-A `exists_pairUnion_memberFamily_of_irreducible_X` (全既約前提) の適応要。~200-300 LOC。
2. **column base coherence** = 全 column の coherence。⚠ 未解決: 単一 degree class (= 1 つの `certainTypeSet`、`certainTypeSet_isCoherent_tau_canonical` 直用) か multi-degree (union 要) か — case (c2) の column degree 一様性を (4.9)/(6.8.2) で確認要。
3. **xChainCoherent 組立** (column base S₀ + irr adjoin) → cX。
4. **glue** (`coherentXunionYset_caseB_of_glued` 既存) → X∪Y coherence。
5. **(6.8.3) L4** (X∪Y→S) = case-A `false_of_coherentXunionYset_of_not_coherentS` (CB2:3439) の case-B 適応 (Z=W₂、算術 |H:W₂|≥(2|W₁|+1)²、case-B S-facts)。~100 LOC。
**▶ 次: hstep core に着手** (case-A member-family 機構を読んで mixed prefix 適応; (6.6) bound は Z-generic で流用)。**正本=本 cont.²³。orthogonality 層完成 (8 commits)。次=hstep core (heavy)。Opus 継続。**

### session 43 cont.²⁴: ✅ hpair (X⊥Y) — glue input 完成 (commit `a528906c`); 10 commits 累積
cont.¹⁹-²⁴ で S-level cover (`caseB_S_member_column_or_irreducible`) + X⊥Y (`caseB_Xset_orthogonal_Yset`, glue の hpair) を追加。**session 43 計 10 Lean commits** (dispatch trio + per-step adjoin + cover ×2 + orthogonality ×4 + S-cover + hpair)。
**glue shell `coherentXunionYset_caseB_of_glued` の入力状況**: hpair ✅ / cY ✅ (coherentYset) / D=per-φ images ✅ (構成可) / **cX ❌ (heavy)** / ν・hagreeX・hmixed (cX 依存) ❌ / hgen (cX 非依存だが intricate span 包含) ❌。
**🔴 capstone closure は heavy core 待ち** (loop-cadence では不可、focused build 要):
1. **cX** = `IsCoherent (Xset W2)`: hstep (mixed-prefix member-family、case-A `exists_pairUnion_memberFamily_of_irreducible_X` は全既約前提で流用不可、新規 ~200LOC) + column base ν-union (engine 無、ν 構築要) + xChainCoherent。
2. **(6.8.3) L4** (X∪Y→S): case-A `false_of_coherentXunionYset_of_not_coherentS` (CB2:3439) の case-B 適応 (Z=W₂、算術 |H:W₂|≥(2|W₁|+1)²、case-B (5.6) bound + S-facts)。~100LOC。最も decomposable か。
3. **hgen** (X∪Y span 包含、cX 非依存): intricate だが loop で挑戦可。
**▶ 次**: heavy pieces の decomposability を精査し最も committable な sub-piece を選ぶ (L4 arithmetic core or hgen)。**正本=本 cont.²⁴。prerequisite 層 10 commits 完成、capstone は heavy core (cX/L4) 待ち。Opus 継続。**

### session 43 cont.²⁵: ✅✅✅ case-B (6.8.3) 算術層 COMPLETE (3 commits) + 構造的発見 (mixed-S break-pair)
main を clean fast-forward 取り込み (lane-g Thm 3.8 / lane-h Thm E + AxiomsCheck のみ、Peterfalvi 無関係)。**新 leaf `S08_CaseBEndgame.lean`** (134 行、imports CaseBCoherence2) を切り、教科書 (6.8.3) 統一論法 (04.8 L234-244) の **case-B 算術層を完全形式化** (3 commits、全 green + axiom-clean):

1. **`false_of_w2_break_arith`** (`07452579`): case-B 算術核。break (5.6) `w1·hZ·(cZ−1) ≤ 2w1²d` + Cor 2.30 `d²≤hZ` + FPF `(2w1+1)²≤hZ` → False。論法: `cZ−1≥1` で `hZ≤2w1d` → `d²≤hZ≤2w1d` で `d≤2w1` → `hZ≤4w1²` で `(2w1+1)²≤hZ` 矛盾。case-A `false_of_centralCommutator_break_arith` (CorePart2:3094) の mirror、FPF 入力が `|H:Z|` 側 ((2w1+1)²) なのが差。
2. **`two_mul_add_one_sq_le_of_two_fpf_factors`** (`e1b7c1a8`): case-B FPF index bound `(2w1+1)²≤|H:Z|`。W₁ FPF on H/H′ と H′/Z の 2 factor それぞれ `two_mul_add_one_le_of_odd_dvd` (CorePart1:2838、(6.5)(a) chief-factor 算術、既存再利用) で `≥2w1+1` → `|H:Z|=|H:H′|·|H′:Z|` で square。oddness + `card_modEq_one` 整除 + index 積を仮説化 (FPF action 2 本 + chain index 恒等式を named obligation 化)。
3. **`false_of_caseB_break_of_bounds`** (`4f16fef0`): 算術 spine。1+2 を合成し (6.8.3) case-B 矛盾を **「(5.6) break + Cor 2.30 + 2-FPF factors → False」**に完全還元。各仮説を Sibley-data source でラベル化。

**🔑🔑 決定的構造発見 (L4 設計を変える)**: `exists_coherentBreakPair` (CorePart1:965) は **`hSbirr : ∀ χ ∈ Sb, IsIrreducibleCharacter χ` (全既約) を要求**。case-B の S は**可約 column μ_j (columnSum = Ind^L_H θ for some θ、∈S) を含む mixed** ゆえ、**case-A の break-pair engine (`exists_coherentBreakPair` / `xSum_le_two_psi`、ともに `hSbirr` / Frobenius `hF` 依存) は case-B に直接適用不可**。教科書の (5.6) は ‖χ‖²-weighted 和 `∑χ(1)²/‖χ‖²` で可約 member を扱う ⟹ **case-B には norm-aware な (5.6) bound + reducible-S 対応の conjugate-pair break が新規に必要**。これが残 heavy core の本体 (cont.¹⁶-²⁴ が "heavy interlocking core" と呼んでいた中身の正体)。

**⟹ 残務 = `false_of_caseB_break_of_bounds` の仮説 discharge (優先順・難度評価)**:
1. **`hbreak` = (5.6) mixed-X break bound** [🔴 最重・新規 infra]: reducible-S 対応 break-pair existence (case-A `exists_coherentBreakPair` の ‖χ‖²-weighted 一般化) + mixed-X の `∑χ(1)²/‖χ‖² = |W₁||H:Z|(|Z|−1)` 再指標化 (sources θ で和を取り直す、(1.5.c,d))。case-A `xSum_le_two_psi`/`sMember_degreeSqReBound_of_not_coherent` は Frobenius+全既約前提ゆえ要全面適応。
2. **2-FPF factor blocks** [🟡 中・群論]: W₁ FPF on H/H′・H′/W₂ を case-B CertainType data から。template = case-A `centralCommutator_card_subgroupOf_lower` (CorePart2:725、単一 factor、`IsFrobeniusAction.subgroup`+`card_modEq_one`)。要: case-B の W₁-action データ (CertainType hypothesis の構造未精査) + chain index `|H:W₂|=|H:H′|·|H′:W₂|`。
3. **`hdsq` = Cor 2.30 `d²≤|H:W₂|`** [🟢 易]: W₂ central ゆえ `θ.isIrreducible.exists_degree_sq_le_index` 直用 (case-A L4 line 3479-3486 と同型、Z=W₂ に置換)。
4. **`hcZ` = |W₂|≥2 / `hw1odd` / oddness** [🟢 易]: 奇位数 + W₂≠1。

**▶▶ 次の focused session 第一手 (推奨)**: **#2 (2-FPF factor blocks) を先に landing** — group-theory で #1 より tractable、`centralCommutator_card_subgroupOf_lower` template + 既存 `two_mul_add_one_le_of_odd_dvd`/`IsFrobeniusAction.subgroup` で組める。要 RECON = case-B CertainType が W₁-FPF-on-H/H′・H′/W₂ をどう供給するか (S06.CertainTypeHypothesis 構造)。#1 (norm-aware (5.6)) は最重、別 focused session か workflow 候補。
**正本=本 cont.²⁵。算術層 3 commits 完結 (新 leaf S08_CaseBEndgame)。L4 は `false_of_caseB_break_of_bounds` 仮説 discharge に還元。決定的発見=mixed-S ゆえ case-A break-pair 不適用→norm-aware (5.6) が heavy core。次=#2 FPF factor blocks (群論、tractable)。Opus 継続。**

### session 43 cont.²⁶: ✅✅ FPF tower 構築 (cont.²⁵ 後 +5 commits) — `hfpf` obligation の H/H′ 枝を実 Sibley data から完全導出
cont.²⁵ で「#2 FPF factor blocks (tractable)」と判定後、FPF 導出層を S08_CaseBEndgame に構築 (本 session 計 8 Lean commits)。**(6.8.3) `hfpf` (= `(2|W₁|+1)²≤|H:W₂|`) を gated tower として組み、H/H′ 枝を実データで close**:

1. **`two_mul_add_one_sq_le_index_of_chain`** (`0a084543`): 抽象 FPF bound を subgroup chain `W≤M≤K` (K odd) に橋渡し。oddness (index∣|K|) + chain index 積 (`relIndex_mul_index`) を discharge、残入力 = 2 FPF 整除 + section 非自明。
2. **`W1_dvd_index_of_fixedPoints_le`** (`7fc0dd0c`): 機械核。coprime action + 固定点⊆M → `quotient_of_fixedPoints_le` で商 FPF → `card_modEq_one` で `|W| ∣ |H:M|−1`。
3. **`caseB_W1_dvd_index_of_centralizer_le`** (`c9cb284a`): W₁-共役 action を**証明内 letI** で setup、`a•x` を `toMulAut_apply`+`conjNormal_apply` で共役展開 (🔑 compHom smul は rfl/rw/simp 不可、内部 letI が鍵)。可換形 `hcomm` から `hfix` を discharge。M characteristic → invariant。
4. **`caseB_W1_dvd_index_commutator`** (`3335a772`): **H/H′ 枝完成・実 Sibley data**。`hcomm` を `cert.centralizer_W2` (C_L(a)⊓K=W₂) + W₂⊆⁅H,H⁆ + `commutator_subgroupOf_self` で discharge。arg = case-(c2) projection (`h46.toCertainTypeHypothesis` 等、`inertia_eq_H_of_c2` mirror)。

**⟹ `hfpf` の残務**: (a) **H′/W₂ 枝** `|W₁| ∣ |H′:W₂|−1` — W₁-action を **H′=commutator ↥H (部分群=群)** 上に setup、M=W₂-in-H′、固定点⊆W₂ を centralizer_W2 から。H/H′ の mirror だが「部分群を群として」action する分やや tricky。(b) **assembly**: 両整除 + section 非自明 (H 非可換, W₂≠H′) を `two_mul_add_one_sq_le_index_of_chain` に投入 → 完全 `hfpf`。

**🛑 正直な戦略フラグ (要認識)**: **FPF tower (`hfpf`) は (6.8.3) L4 の 4 obligation の 1 つに過ぎず、しかも easier な方**。L4 capstone (`false_of_coherentXunionYset_caseB_of_not_coherentS`) の真の long pole = **#1 norm-aware (5.6) break bound for reducible S** (cont.²⁵ 発見: case-B の S は可約 column を含む mixed ⟹ case-A の `exists_coherentBreakPair` [全既約要求] / `xSum_le_two_psi` [Frobenius+全既約] が不適用、‖χ‖²-weighted な break-pair existence + (5.6) bound の新規 infra が必要)。**#1 は未着手で最重**。FPF tower 完成 (hfpf close) しても #1 無しでは L4 は閉じない。⟹ hfpf 完成後の優先 = #1 の真の難度評価 (loop-tractable か、focused workflow / ChatGPT 相談 [[feedback-ask-chatgpt-for-elided-gaps]] が要るか)。

**▶ 次 (loop)**: H′/W₂ 枝 → assembly で `hfpf` を close、その後 #1 評価へ pivot。**正本=本 cont.²⁶。FPF tower 8 commits、H/H′ 実データ完成。残=H′/W₂+assembly→hfpf。真 long pole=#1 (reducible-S break, 未着手)。Opus 継続。**

### session 43 cont.²⁷: 🛑 #1 (reducible-S break) verdict 確定 — framework 一般化必須・loop-tractable でない
cont.²⁶ で #1 を long pole とフラグ後、S07/(5.6) 機構を精査して **定義的 verdict** を得た:
- **(5.6) engine `sMember_degreeSumBound_of_not_coherent` (CorePart2:2650) + `sMember_degreeSqReBound_of_not_coherent` は `hF : IsFrobeniusGroup` 依存** = case-A (Frobenius) 専用。case-B (CertainType) では `hF` 無し。
- **結論が S₁ を `χmem : Fin k → IrreducibleCharacter ↥L` として列挙**(`.re^2`、‖χ‖² denominator 無し)。case-B の S₁ は可約 column を含む ⟹ 既約列挙が破綻。
- **S07 に norm-weighted / reducible-aware な coherence-break 機構は存在しない**(grep 確認)。S07 coherence 理論全体が `‖χ‖²=1`(既約・正規直交)前提(S07:2492/2528/3240)。
- `exists_conjugatePairCover` も同様に既約 pair 前提。

⟹ **#1 = §5/§7 の coherence-break framework を「Frobenius-free かつ norm-weighted (reducible-S 対応)」に一般化する大規模改修**。`sMember_degreeSumBound_of_not_coherent` / `exists_conjugatePairCover` / DadeChainStep / (5.6) bound の reformulation を要し、**loop-cadence では不可・focused multi-session または framework 専任作業**。

**現状の B lane 成果(再利用可能)**: (6.8.3) 算術 spine + FPF tower(H/H′ 実データ完成、H′/W₂+assembly 残)は #1 と独立に valid。capstone `sibleySetup_is_coherent` の case-B branch は #1 が closeしない限り閉じない。

**▶ 戦略 fork(要ユーザー判断)**: (a) FPF tower 完成(hfpf 再利用 infra、L4 は #1 block 継続) / (b) #1 の textbook 再定式化を ChatGPT 評価(reducible-S 回避の余地精査) / (c) endpoint B/C/D/E signature-pin に redirect / (d) #1 framework 一般化に着手(大規模)。**正本=本 cont.²⁷。#1 = framework 一般化必須・loop 不可。**

### session 43 cont.²⁸: ✅ #1 ChatGPT 評価完了 (Pro 拡張 + project 資料) — verdict 確認 + 精緻化
ユーザー裁可で #1 を ChatGPT (GPT-5.5 Pro 拡張、odd-order project の教科書 upload を参照、思考 13m25s) に評価依頼。
全文+検証 = **notes/peterfalvi/s08_6_8_3_reducibleS_chatgpt_answer.md** (出典 04.7/04.8/04.17、私が cont.²⁷ と照合し確認)。

**結論 (検証済)**: cont.²⁷ verdict **確認** — case-B (6.8.3) は reducible column を含む S₁ に (5.6) を適用し
‖χ‖²-weighted 和を使う、**sidestep 無し**。**精緻化**:
- (5.6) は抽象 Hyp (5.2) 下の定理で**既約不要・Frobenius-free**。私の Lean 版 (`hF` + IrreducibleCharacter 列挙) は
  norm-1 特殊化 = artifact。case-B では (5.3.b) が Hyp (5.2) を確立 (R(μ_j)=ω_ij^σ、**構築済 σ-isometry に接続**)。
- 必要な一般化 = **systematic reweighting** (‖χᵢ‖²=1 → 一般 ‖χᵢ‖²、射影係数 1/‖χᵢ‖²)。既存 (5.6) 証明と概念同型、
  arbitrary virtual char でない。但し「more than a local patch」(S07/S08 core の (5.6) 機構 reweight、multi-session)。

**⟹ endpoint A (6.8 capstone) の残ブロッカー = (5.6) の norm-weighted/Frobenius-free 一般化 + (5.3.b)**。
systematic だが multi-session core。FPF tower (cont.²⁶、H/H′ 実データ済) は別 obligation で独立に valid。
**▶ 要ユーザー判断**: (a) (5.6) reweighting 着手 (endpoint A 完遂路、multi-session) / (b) FPF tower 完成優先 /
(c) endpoint B/C/D/E redirect。**正本=本 cont.²⁸ + chatgpt_answer.md。#1=systematic (5.6) reweight、sidestep 無し確定。**

### session 43 cont.³⁰: FPF tower H′/W₂ 枝の build recipe + (5.6) core = xAdjoinStep monolith 確認
両残務とも focused context 向き。次セッションが直接実行できるよう recipe を記録 (maxed context での careful build 回避)。

**FPF tower H′/W₂ 枝** (`|W₁| ∣ |H′:W₂|−1`、cont.²⁶ tower の残・hfpf 完成に必要): H/H′ (`caseB_W1_dvd_index_commutator`,
`3335a772`) の mirror だが nested ゆえ ~100 行・要注意:
- action setup: `actH : MulDistribMulAction ↥W1 ↥H` (compHom conjugation) → commutator ↥H は characteristic で
  W₁-invariant (`hMinv_comm`) → **`IsFrobeniusAction.invariantSubgroupMulDistribMulAction (commutator ↥H) hMinv_comm`**
  で `MulDistribMulAction ↥W1 ↥(commutator ↥H)`。**smul-coercion は定義的**: `(a•y : ↥(commutator ↥H)).val = a •_H (y:↥H)`
  (FrobeniusActionTI:80、`⟨fun a m => ⟨a•(m:N), …⟩⟩`)。⟹ `((a•y:↥(commutator ↥H)):↥L) = (a:L)(y:L)(a:L)⁻¹` (H/H′ の hsmul 再用)。
- M = `(W2.subgroupOf H).subgroupOf (commutator ↥H)` (要 `W2.subgroupOf H ≤ commutator ↥H`、case-B hderiv)。
  - **M.Normal**: W₂ central in H (case-B hW2cen) → W₂ ◁ H → M ◁ H′。
  - **hMinv (M の W₁-invariance)**: W₂=C_H(W₁) は W₁-invariant (a•x=axa⁻¹、x が W₁ 中心化ゆえ a⁻¹ba も中心化 → axa⁻¹∈C_H(W₁)=W₂)。
    ⚠ characteristic 不可ゆえこの centralizer 論法を要明示。
  - **hfix**: a•y=y → (a:L)(y:L) 可換 → (y:L)∈C_L(a)⊓K=W₂ (centralizer_W2) → y∈M。H/H′ の discharge を H′ レベルで mirror。
- `W1_dvd_index_of_fixedPoints_le (H:=↥(commutator ↥H)) hCop M hMinv hfix` → `|W₁| ∣ M.index−1 = |H′:W₂|−1`。
- 最後に **assembly**: `caseB_W1_dvd_index_commutator` (H/H′) + 上記 (H′/W₂) + `two_mul_add_one_sq_le_index_of_chain`
  (cont.²⁶ `0a084543`) → 完全 `(2|W₁|+1)²≤|H:W₂|` = hfpf。⟹ `false_of_caseB_break_of_bounds` の hfpf 入力完成。

**(5.6) reweighting core**: `xAdjoinStep` (S08CP1:2262、189 行 τ₂) は norm-1 (`hχχ=1`/`hchi1chi1=1`/`hmemortho` 対角=1) を
**全体に thread した monolith** — clean な incremental factoring 無し。weighted 版は ChatGPT Q4 を正本に copy+modify
(射影係数 1/‖χᵢ‖²)、major focused build。

**📍 session 43 cont 総括 (14 commits)**: FPF tower 8 Lean (H/H′ 実データ) + ChatGPT #1 verdict (sidestep 無し) +
(5.6) 完全 scoping (X-sum 済、core=weighted xAdjoinStep)。残 = (A) FPF H′/W₂+assembly [bounded・上記 recipe] /
(B) (5.6) core [xAdjoinStep weighted・major]。両者 focused context 推奨。**正本=本 cont.³⁰ + s56_reweighting_plan.md。**

### session 43 cont.³¹: ✅✅ FPF tower COMPLETE — hfpf を実 Sibley data から完全組立 (3 commits)
cont.³⁰ recipe を実行し H′/W₂ 枝 + assembly を landing (maxed context でも methodical build で突破):
- **`caseB_W1_dvd_relIndex_commutator`** (`c46b0d13`): `|W₁| ∣ |H′:W₂|−1`。W₁-action を H′=commutator ↥H 上に
  `invariantSubgroupMulDistribMulAction` (smul-coercion `rfl`) で setup、hMinv は W₂ normality (`conj_mem`、
  W₂ central)、hfix は centralizer_W2 を H′ で mirror。⚠ build tip: coercion 不一致は equality 回避 +
  normality(conj_mem)で頑健化; central→normal は `mem_center_iff` 手構成 (前向き rw)。
- **`caseB_fpf_bound`** (`17 commit`): 両整除 + `two_mul_add_one_sq_le_index_of_chain` → 完全
  `(2|W₁|+1)²≤|H:W₂|`。oddness は card_L_odd、残 input = nontriviality 2 本 (H 非可換 / W₂≠H′ = (6.8.3) Z≠H′)。

**⟹ case-B (6.8.3) の FPF/hfpf 側は完全に実 Sibley data 化。**`false_of_w2_break_arith` の hfpf 入力完成。
**残ブロッカー = (5.6) bound (`hbreak`)= weighted `xAdjoinStep` 一般化** (s56_reweighting_plan.md、major focused)。
+ Cor 2.30 (hdsq、易・L4 inline) + break-pair for reducible S (= (5.6) core の一部)。

**📍 endgame leaf (S08_CaseBEndgame, 396 行/9 定理) inventory**: 算術核 `false_of_w2_break_arith` / FPF index bound
`two_mul_add_one_sq_le_of_two_fpf_factors` / chain bridge `two_mul_add_one_sq_le_index_of_chain` / 機械核
`W1_dvd_index_of_fixedPoints_le` / action bridge `caseB_W1_dvd_index_of_centralizer_le` / H/H′ `caseB_W1_dvd_index_commutator`
/ H′/W₂ `caseB_W1_dvd_relIndex_commutator` / **hfpf `caseB_fpf_bound`** / 算術 spine `false_of_caseB_break_of_bounds`。
**正本=本 cont.³¹。FPF tower 完結、残=(5.6) core。**

### 🚨 訂正 (2026-06-16, cont.³⁷ = s56_reweighting_plan.md): 「残=(5.6) core / R(μ_j) deep bridge」は **誤診**
cont.³¹/³⁵/³⁶ の「(5.6) core = R(μ_j) via σ の deep §5↔§6 bridge を新規構成」は **誤り**。R(μ_j) は
**`certainTypeR`** (`S06_CertainTypeCoherence.lean:639`、lane-b 自身が 6/14 commit `72798461` で構築) として
**既存・4 field 充足** (image_eq=`dadeICM_columnDiff_eq_sum`)。reducible μ_j 用 Da も `certainTypeDecompositionDa`
(`:684`) 既存。**真の残務 = cX wiring 3 ピース (~350-550 LOC、deep math gap 無し)**: (A) weighted X-chain→cX /
(B) hmapagree / (C) extension assembly → glue (`coherentXunionYset_caseB_of_glued`、sorry-free) → sorry 解消。
2026-06-16 session: `xAdjoinStepW` 一般化 (`6a59b41e`) + `coherentDegreeSqNormBound_of_not_coherentW`
(`c7c3f6a0`) landed。**詳細・次手の正本 = `s56_reweighting_plan.md` cont.³⁷** (本ファイルの cont.³¹ は obsolete)。

## 2026-06-16 lane-b 再開 (session 44): 🎯🎯 engine-level architecture 確定 — (6.8.2) は標準 engine + base=certainType⊔Y、weighted 不要

lane-b 再開。原典 (6.8) + S07/S08 engine を engine-level で精読し、session 43 の chain-vs-direct / weighted-base
混乱を **engine 署名から決着**。**deep math gap は無く、残は hstep monolith assembly のみ**と再確認。

### ✅ engine-level で確定した事実 (session 43 の混乱を supersede):
1. **per-χ decomposition は全て η₁-anchored で uniform**: `columnDecompositionTau` (S08_CaseBCoherence2:1822)
   と `irreducibleDecompositionTau` (:1868) は**両方とも** `CharacterPsiDecomposition hyp.tau χ (a • η₁)`
   を産む (column も irr も共有 anchor η₁∈Y)。= 原典 (6.8.2.3) `(χ−a·η₁)^τ = X₁−a·Y` の uniform 形式化。
2. **標準 engine は reducible base を扱える**: `retarget_isCoherent_of_supportedDecomposition_and_memberFamily`
   (S07:4126) の per-member 直交 helper `inner_extension_member_orthogonal_imageSet` (S07:3845) は
   base member を `D' : CharacterPsiDecomposition τ χ' 0` で**一般に**取る (既約性要求なし)。⟹ 各 base member の
   直交は自分の decomposition で discharge。**reducible column を base に置ける** (Dmem=`certainTypeMemberDecomposition`)。
3. **engine 制約は anchor∈base + anchor norm-1 + adjoined-member norm-1 のみ** (`hchi1∈S₁`, `hchi1chi1=1`, `hχχ=1`)。
   η₁ は既約 (norm-1)、irr X-member も norm-1 ⟹ 充足。columns は adjoin せず base に置く (reducible でも IsCoherent OK)。

### 🧭 確定した (6.8.2) 構築経路 (session 43 の weighted/chain 議論を上書き):
**`IsCoherent hyp.tau (X∪Y)` を直接構築** (glue shell `coherentXunionYset_caseB_of_glued` の cX-分離は bypass):
- **base = certainTypeSet ⊔ Y** (η₁∈Y を含む、両者 coherent: `certainTypeSet_isCoherent_tau` / `coherentYset`、
  直交 `caseB_Xset_orthogonal_Yset`)。orthogonal-union glue (`coherentUnion_of_glued` 系) で組む。
- **既約 X-member を η₁ anchor で順次 adjoin** (`retarget_isCoherent_of_supportedDecomposition_and_memberFamily`、
  Da=`irreducibleDecompositionTau`)。→ 結果 = certainType ⊔ Y ⊔ irr-X = X∪Y。
- **⟹ weighted engine (xChainCoherentW/xAdjoinStepW) は (6.8.2) coherence 構築には不要** (session 43 の前提を訂正)。
  weighted bound `coherentDegreeSqNormBound_of_not_coherentW` は **(6.8.3) break** にのみ要る (S₁=X∪Y が reducible
  columns を含むため、Thm (5.6) の bound 側が weighted)。coherence 構築 (engine) と break bound (5.6 適用) は別レイヤ。

### 🔴 残る irreducible hard core = hstep monolith (~200-400 LOC、deep gap 無し、assembly-scale):
各 adjoin step の data (Da + heterogeneous Dmem + per-step 直交 + hgen)。Dmem dispatch =
column→`certainTypeMemberDecomposition`、Y/既-adjoin-irr→`memberExtensionDecomposition`。per-step 直交 = column⊥new
(`certainTypeR_imageSet_orthogonal_dadeOfDiff` cont.⁴¹)、irr⊥new (`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`)。
+ base-union glue + chain enumeration + (6.8.3) wiring。**全ツール在庫、engine/base 確定、deep math gap 無し**だが
loop-cadence 不適 (session 43 が ~18 iter で thrash した assembly-scale)。

**正本=本 session 44。engine=標準 (weighted 不要)、base=certainType⊔Y、残=hstep monolith assembly (sustained focus
or 集中 subagent or Workflow 向き)。次=base-union glue → 既約 X-member adjoin chain (hstep)。**

## 2026-06-16 lane-b (session 45, base-union piece): ✅ `hgen` for certainTypeSet base 着地 (new leaf S08_CaseBXunionY)

session-44 architecture の **base = `certainTypeSet h46 k ⊔ Y`** に向け、glue engine
`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` (S07:4581) の **`hgen`
(generation hypothesis) を column-base 用に完全形式化**。新 leaf `S08_CaseBXunionY.lean`
(imports `S08_CaseBAssembly`、OddOrder root に配線済、full build 3838 jobs/375s green、
sorry 141 不変、両 lemma axiom-clean = 3-axiom allowlist のみ)。

### ✅ landed (2 theorems, S08_CaseBXunionY.lean):
1. **`certainTypeSet_span_apply_one_eq_intMul`** (column degree-ratio integrality): 任意の
   `ψ ∈ ℤ[certainTypeSet h46 k]` は `ψ(1) = s·μ_{j₀}(1)` (`s∈ℤ`、`μ_{j₀}=columnSum k0` は
   任意の anchor member)。**核 = certainTypeSet 定義に組込まれた等次数性** (全 member が
   reference degree `∑_i μ_{ik}(1)` を共有、`columnSum_apply_one` 経由)。⟹ single-member ratio=1、
   span induction で integer combination へ。Frobenius `hsX`
   (`exists_charValue_one_eq_mul_xBaseBlock_anchor` 経由) の column 版置換。
2. **`hgen_withDiagonal_certainTypeSet`** ((6.8.1) generation hypothesis、column base): glue engine
   `hgen` を `X:=certainTypeSet h46 k`, `Y:=Yset`, diagonal `D:={columnSum k0 − a₀·η₁}` で discharge。
   `hgen_withDiagonal_of_frobenius` (S08_CoherenceCore:3235) の完全 mirror — supported φ を
   φ_X+φ_Y に分割、3 piece `(φ_X−s·μ_{j₀})`/`(φ_Y+s·(a₀·η₁))`/`s·(μ_{j₀}−a₀·η₁)` が各々 supported
   かつ右 submodule。anchor は **member** `k0≠1` (`hk0mem:columnSum k0∈certainTypeSet h46 k`)
   で取る (reference `k` 自身は trivial かもしれず column でない、RISK #5 に対応)。

### 🔑 RISK #2 (degree-class) は単一 certainTypeSet 内では杞憂と確認:
`certainTypeSet h46 k` は **定義上**全 member が同次数 (`∑_i μ_{iχ₂}(1)=∑_i μ_{ik}(1)`)。⟹
`hgen` の degree-ratio `s` は常に整数 (member 単体は ratio 1)。複数 degree-class 問題は
**raw (4.9) を単一 certainTypeSet 外で使う時のみ**で、本 base には不要。session 41 cont.⁷ の
ChatGPT 訂正 (「w₂ 素数 → 非零列は全同次数の単一 certain-type 族」) とも整合。

### 🔴 残る base-union obligation (この leaf では未着手、full base-union を閉じるのに必要):
base-union `IsCoherent hyp.tau (certainTypeSet ∪ Y)` を engine で組むには `hgen` の他に:
1. **ν 構築** (RISK #1、real new infra): `certainTypeExtension` (列上) と `coherentYset.extension`
   (Y上) で一致する単一 `IntegralCharacterMap`。`exists_integralCharacterMap_glue_of_orthonormal`
   (S07:3125) は **orthonormal SOURCE** を要求するが column は norm `|W₁|≠1` ゆえ直接不可。正攻法 =
   全非自明列の grid character `μ_{ij}` (これは正規直交既約) + Y を source family とする
   `coherentImageMapGlue` (列横断 grid 正規直交が要)。
2. **hDτ** (b≡0 conclusion): `ν(μ_{j₀}−a₀·η₁)=hyp.tau(μ_{j₀}−a₀·η₁)`。`columnDecompositionTau`
   (S08_CaseBCoherence2:1822) の `tau1_image` で `hyp.tau(μ_{j₀}−a₀·η₁)=D.X−D.Y`、pinning
   `per_constituent_Y_eq_smul` で `D.Y=a₀·Y₀`、`D.X=certainTypeExtension μ_{j₀}` ⟹ ν 一致と接続。
   per-φ aggregate (`caseB_per_phi_anchored_fromYset` 等) の wiring が要 — column-specific anchored
   image (`(μ_{j₀}−a₀η₁)^τ = certainTypeExtension μ_{j₀} − a₀·Y₀`) を materialize。
3. **hmixed**: `inner_certainTypeExtension_columnSum_coherentYset_extension_eq_zero`
   (S08_CaseBCoherence2:1449、**既存**) が列-Y image 直交を直接供給。+ source ⊥
   (`inner_columnSum_Yset_eq_zero` 既存) + hagreeX/hagreeY rewrite。
**⟹ `hgen` は ✅ 完了。次の長 pole = ν 構築 (1) + hDτ wiring (2)** (両者 heavy、ν は新 infra)。

**正本=本 session 45。`hgen_withDiagonal_certainTypeSet` + degree-ratio 補題 landed (new leaf
S08_CaseBXunionY、axiom-clean)。残=ν (列横断 grid glue) + hDτ (per-φ pinning wiring)。**

## 2026-06-16 lane-b 再開 (session 46): 🎯 thrashing 決着 — session 45 path = 教科書整合の sound route と確定 (textbook + engine 署名で照合)

lane-b 再開。session 43-45 (s08 plan) と cont.⁴³-⁴⁷ (s56_reweighting_plan) で **chain adjoin / 直接τ₂ /
certainTypeSet⊔Y glue の 3 アプローチが振動**していたのを、**原典 (6.8.2) 全文 (04.8.mmd L178-224) +
engine 署名**で照合し決着させた。**Lean commit は無し** (engine 在庫を exhaustive に確認し、振動を解消して
正しい 1 経路を確定する RECON; 次の build を fresh context で安全に回すための consolidation)。

### ✅ 教科書 (6.8.2) の構造 (ground truth, 確定):
- **(6.8.2) は τ₂ を Z[X∪Y] 上に直接構成**: τ₂ は τ on `Z[X∪Y,L^#]` 一致 + `η₁^τ₂ = Y` (Y=η₁^τ₁ or −η₂^τ₁)。
  生成集合 `{Z[X∪Y,L^#] ∪ {η₁}}` (これが Z[X∪Y] を生成) 上で内積保存を (6.8.2.3) で検証 → X∪Y coherent。
- **🔑 case (A) と違い cX = IsCoherent(X) を独立に構成しない** (case (B) の X は可約 column μ_j を含むので
  「X coherent」を経由できない; case (A) のみ (6.6) で X⊂Irr L coherent)。X-coherence は (6.8.2) の帰結であって前提でない。

### ✅ engine 照合の決定的発見 (振動の根本原因):
- **`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` (S07:4581) は `hX:IsCoherent τ X` と
  `hY:IsCoherent τ Y` を両方独立に要求** (= 2 coherent 集合の貼り合わせ engine、case-A Frobenius assembly の
  ミラー)。⟹ これを `X:=Xset W2` で使うと **cX-standalone (mixed X の coherence) を強いる** = 教科書非整合の
  重い道。cont.⁴³-⁴⁵ の `xChainCoherentW` (cX-standalone) thrashing の正体。
- **✅✅ session 45 の path は健全**: glue を `X:=certainTypeSet h46 k` (= 可約 column のみ、`hgen` 済) で使い、
  **既約 X-member は後段で retarget adjoin** する。⟹ cX-standalone (mixed) を回避しつつ既存 infra を最大活用する
  **正しい Strategy-B-chain**。session 45 は後退でなく前進だった (cont.⁴⁶ の「session 45=detour」評は誤り)。

### 🧭 確定した case-B 経路 (これで振動終了、以後この 1 本):
1. **base glue** (session 45 進行中): `coherentXunionYset_caseB_of_glued` 系を `X:=certainTypeSet h46 k`,
   `Y:=Yset` で適用 → `IsCoherent hyp.tau (certainTypeSet ∪ Y)`。入力 = cX(=`certainTypeSet_isCoherent_tau_canonical`
   ✅) / cY(=`coherentYset` ✅) / hpair(✅) / hgen(✅ session 45) / **ν + hagreeX/Y + hmixed + hDτ (残)**。
2. **既約 X-member adjoin**: `retarget_isCoherent_of_decompositions_and_memberFamily` (S07:3979) で
   (certainTypeSet∪Y) に既約 X-member を per-pair 追加 → `IsCoherent hyp.tau (Xset W2 ∪ Y)`。
   per-χ data = `irreducibleDecompositionTau` (S08CBC2:1868)、Dmem dispatch (column→`certainTypeMemberDecomposition`)。
3. **(6.8.3)**: 単一 break {ψ,ψ̄} に Thm (5.6) (`coherentDegreeSqNormBound_of_not_coherentW`) + X-sum +
   FPF tower (`caseB_fpf_bound` ✅) → `false_of_caseB_break_of_bounds` (✅算術 spine) → S coherent → sole sorry。

### 🔭 次の build = ν 構築 (session 45 long pole、全部品在庫・deep gap 無し):
**`exists_integralCharacterMap_glue_of_orthonormal` (S07:3125) を `X-source = grid {μ_{ij}}`,
`Y-source = Yset` で適用**。columnSum は norm |W₁| で非 orthonormal だが **μ_{ij} は正規直交既約**ゆえ
source に取れる; ν は linearity で `ν(columnSum)=∑_i ν(μ_{ij})=∑_i certainTypeExtension(μ_{ij})=
certainTypeExtension(columnSum)` ⟹ hagreeX (on columnSum) 充足。νX=`certainTypeExtension` (=`certainType_isCoherent`
.extension S06:513、=dadeICM S06:453)、νY=`coherentYset.extension`。**要部品 (全在庫)**:
- grid orthonormality `⟨μ_{ij},μ_{i'j'}⟩=δ`: within-column=既約正規直交、cross-column=`columnFamily_mu_ne`
  (S06_CertainTypeClifford:827 で使用) + 既約 ⟹ 直交。set-level 組立 (sigma index over deg-class-k columns×Fin w₁) が intricate。
- μ_{ij}⊥η: `inner_coherentYset_extension_certainTypeRImage_eq_zero` (S08CBC2:1331) / source ⊥ `inner_columnSum_Yset_eq_zero`。
- hagreeX 接続: ν(columnSum)=certainTypeExtension(columnSum) を linearity で (`map_sum`)。
**その後**: hmixed (`inner_certainTypeExtension_columnSum_coherentYset_extension_eq_zero` S08CBC2:1449 既存) +
hDτ (per-φ pinning `per_constituent_Y_eq_smul` wiring) → base glue 完成 → step 2 adjoin → step 3 → sole sorry。

**📊 honest reckoning**: deep math gap 無し・全 ingredients/infra 在庫だが **large intricate assembly** (ν~100-150
LOC + adjoin chain + (6.8.3) wiring、multi-session)。session 43-47 の振動は loop の per-turn context reload が原因と
確定 ⟹ **sustained focus で 1 経路 (上記) を腰を据えて build** すべき (loop-cadence 不適は実証済)。
**正本=本 session 46。3 アプローチ振動を textbook+engine 署名で決着 (session 45 path=sound Strategy-B-chain)、
cX-standalone は教科書非整合と確定。次=ν 構築 (grid μ_{ij} orthonormal glue、全部品在庫)。**

### session 46 cont.: ✅ `certainTypeSet_finite` landed (ν-glue hXfin foundation, S08_CaseBXunionY, axiom-clean)
ν 構築の最初の bounded 部品を landing。`certainTypeSet h46 k` 有限性 = `certainTypeSet ⊆ range(columnSum h46)`
+ W₂-dual 型 `(...→* ℂˣ)` 有限 (`SibleyDadeHypothesis.finite_linearCharacters_of_finite`、有限群 linear char)。
standalone (hyp/hHK 不要)、commit `1c4753f2`、leaf green 3627 jobs、axiom-clean (3 allowlist)。

**▶▶ 次の sub-piece = grid source 族の set-level 組立 + 正規直交性** (ν-glue `exists_integralCharacterMap_glue_of_orthonormal`
の hXfin/hXorth/hXY 入力)。grid set = `⋃_{χ₂∈deg-class-k} {(h46.columnFamily χ₂).mu i | i:Fin w₁}` (finite union of
finite)。正規直交性: within-column = μ_{ij} 既約 (norm 1) + 相異 (`columnFamily_mu_ne`、同 χ₂ 内 i≠i')、cross-column =
`columnFamily_mu_ne` (χ₂≠χ₂') + 既約直交。grid⊥Y = `inner_coherentYset_extension_certainTypeRImage_eq_zero`
(S08CBC2:1331) 系 / source ⊥ `inner_columnSum_Yset_eq_zero`。要確認 = `columnFamily_mu_ne` の正確な署名
(S06_CertainTypeCharacters:547) + μ_{ij} 既約補題名 + columnFamily_mu_sum_inner (S06CTChar 近傍)。組立後:
νX=`certainTypeExtension` (S06:513=coherence.extension)、νY=`coherentYset.extension` → glue ν → hagreeX は
ν(columnSum)=∑ν(μ_{ij})=certainTypeExtension(columnSum) を `map_sum` で。次 turn は sustained focus で grid 組立から。

### session 46 cont.²: ✅✅ ν 構築 (session 45 long pole) COMPLETE + base glue を単一 obligation hDτ に還元
**`exists_glue_nu_columnSum_Yset` landed** (commit `0ac7ece5`, S08_CaseBXunionY, axiom-clean): 結合 ν を
grid source 族 {μ_{ij}} (正規直交既約) と Y の `exists_integralCharacterMap_glue_of_orthonormal` で構築、
columnSum 一致は linearity (`columnSum_def`+`map_sum`) で grid 一致から復元。grid⊥Y = 既存
`inner_columnFamily_mu_Yset_eq_zero`、grid 正規直交 = 既約 Kronecker (`irreducibleCharacter_inner` + CF-level
`hinner` idiom)。**全 3 axioms allowlist**。

**🎯 base glue (`coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`, X:=certainTypeSet, Y:=Yset) の
機械的入力は全て解決可能と確定 — 残る実質 obligation は hDτ ただ 1 つ**:
- **cX** = `certainTypeSet_isCoherent_tau_canonical hk` ✅ / **cY** = `coherentYset` ✅
- **hagreeX** ✅: `IsCoherent.congrMap` (S08CBC2:1531) は `extension := c.extension` で **extension 保存** ⟹
  canonical.extension = `certainTypeExtension` ⟹ `exists_glue_nu_columnSum_Yset` の columnSum 一致が直結
- **hagreeY** ✅: ν lemma 直接 / **hgen** ✅: `hgen_withDiagonal_certainTypeSet` (session 45)
- **hsrc_ortho** ✅: `inner_eq_zero_of_mem_span_of_pairwise_orthogonal` (S08CBC2:1555) + hpair=`inner_columnSum_Yset_eq_zero`
- **hmixed** ✅: ⟨νx,νy⟩=⟨cTE(columnSum),cY.ext(η)⟩=0 (`inner_certainTypeExtension_columnSum_coherentYset_extension_eq_zero`
  S08CBC2:1449, 要 hHK) かつ ⟨columnSum,η⟩=0 (column⊥Y) ⟹ 両辺 0
- **🔴 hDτ** (唯一残): `ν(columnSum k0 − a₀η₁) = hyp.tau(columnSum k0 − a₀η₁)`。LHS=cTE(columnSum k0)−a₀·cY.ext(η₁)
  (ν linearity)。RHS は **(6.8.2.3) anchored image** = `columnDecompositionTau` (S08CBC2:1822) の D で
  `hyp.tau(columnSum−a₀η₁)=D.X−D.Y`、pinning `per_constituent_Y_eq_smul` (S08CBC2:871) で `D.Y=a₀·cY.ext(η₁)`・
  `D.X=cTE(columnSum k0)` ⟹ 一致。**materialize 要** (multi-step、(6.8.2.3) 実質内容)。
  入力在庫: `columnDecompositionTau` の hmapagree=`caseB_column_mapagree`✅ / hχψ=`caseB_column_orthogonal_Yset`✅ /
  hχbarψ=`caseB_column_conj_orthogonal_Yset`✅ / hdeg=`columnSum_inv_apply_one`✅ / hSdiff,htau1_mema=要構成。
  per-φ 機構 `caseB_per_phi_anchored` (S08_CaseBAssembly:1416) も既存。

**⟹ ▶▶ 次 turn の第一手 = hDτ materialize** (anchor column k0 の `columnDecompositionTau` D 構築 → D.X/D.Y を pinning
抽出 → `tau(columnSum k0−a₀η₁)=cTE(columnSum k0)−a₀·cY.ext(η₁)` を確立) → base glue assembly
(`coherentCertainTypeSet_union_Yset`) → 既約 adjoin (retarget) → IsCoherent(Xset∪Y) → (6.8.3) → sole sorry。
**正本=本 session 46 cont.²。ν=DONE、base glue は hDτ ((6.8.2.3) anchored image) 単一 obligation に還元、discharge 経路確定。**

### session 46 cont.³: ✅✅ base glue assembly `coherentCertainTypeSet_union_Yset` landed — 単一 obligation `hanchored` のみ
**`coherentCertainTypeSet_union_Yset` (commit `8152a356`, S08_CaseBXunionY, axiom-clean)**: case-B base glue
`IsCoherent hyp.tau (certainTypeSet h46 k ∪ Yset)` を gated skeleton として完成。機械的入力を全て内部 discharge:
- **ν 抽出は `.choose`** (∃ν は Prop ⟹ IsCoherent データ goal に `obtain` 不可; `have hspec:=…choose_spec`+`set ν:=…choose`)
- hagreeX: `exact hνcol χ₂` (**`canonical.extension` は `certainTypeExtension` と defeq** — `IsCoherent.congrMap` の
  `extension := c.extension` 経由、`rfl` 不要で `exact` 通過)
- hsrc_ortho/hmixed/hgen = 既存 lemma 直結、hDτ = ν linearity (`map_sub`/`map_nsmul`) で hanchored に還元
- **唯一 hypothesis = `hanchored`**: `hyp.tau(columnSum k0 − a₀•η₁) = certainTypeExtension(columnSum k0)
  − a₀•coherentYset.extension(η₁)` (= (6.8.2.3) column anchored image、faithful)

**🔴 残る単一 obligation = `hanchored` ((6.8.2.3) column anchored image) — deep hard core**:
route = `columnDecompositionTau` D (S08CBC2:1822、入力 hdeg=`columnSum_inv_apply_one`/hmapagree=`caseB_column_mapagree`/
hχψ・hχbarψ=`caseB_column_orthogonal_Yset`系/hSdiff・htau1_mema=要構成) → `D.tau1_image: hyp.tau(columnSum−a₀η₁)=D.X−D.Y`
(D.tau1=hyp.tau) → pinning `D.Y=a₀•cY.ext(η₁)` (`per_constituent_Y_eq_smul` または `caseB_per_phi_anchored` S08CBA:1416、
要 (6.8.2.2)=hdecomp [S08CBC `inner_tau_indW2_sub_smul_eq` 系で実質済] + D family `caseB_constituentDecomposition` S08CBA:1037
+ hXorth/hbi) → `D.X=certainTypeExtension(columnSum)` 同定。**multi-hundred LOC、per-constituent + pinning の (6.8.2.3) 本体**
(lane が長く hard core としてきた部分)。**loop-cadence 不適、focused build 要。**

**▶▶ 次 = `hanchored` materialize** (上記 route)。完成すれば base glue 即完成 → 既約 X-member adjoin
(`retarget_isCoherent_of_decompositions_and_memberFamily` + `irreducibleDecompositionTau`) → IsCoherent(Xset∪Y) →
(6.8.3) [FPF tower `caseB_fpf_bound`✅ + (5.6) bound `coherentDegreeSqNormBound_of_not_coherentW`✅] → sole sorry。
**正本=本 cont.³。base glue=完成 (skeleton)、唯一残=hanchored ((6.8.2.3) per-constituent 本体、deep)。**

### session 46 cont.⁴: 🔬 hanchored を精密マップ — 残る crux = `(caseB_phi_family).X = certainTypeExtension(columnSum)` 同定 (新規 pinning)
hanchored の discharge 経路を engine 在庫で exhaustive に確認。Lean commit なし (route 確定の RECON)。
**既存 (6.8.2.3) 機構**: `caseB_per_phi_anchored_fromYset` (S08CBA:1647) が anchored image
`hyp.tau(Ind^L_H θ − cw•η₁) = (caseB_phi_family … i).X − cw•cY.ext(η₁)` を与える (pinning は内部 = `per_phi_anchored_image`)。
bundles は **dischargeable** (`caseB_column_bundle` S08CBA:921 = theorem、`caseB_column_bundleFamily` :1002)。
**⟹ hanchored の残務 3 点**:
1. **per-φ family setup**: column k0 を `caseB_per_phi_anchored_fromYset` の枠 (φ:Irr W2、constituent θ) に乗せる。
   columnSum k0 = Ind^L_H θ_{k0} (`columnSum_eq_induce_H`, hHK) を per-φ family の constituent i に同定。
2. **hdecomp = (6.8.2.2) aggregate**: `hyp.tau(Ind_{W2} φ − [H:W2]•η₁) = Xagg − [H:W2]•cY.ext(η₁)` を供給
   (S08CBC の `inner_tau_indW2_sub_smul_eq` 系で実質材料はある; aggregate 形への wiring 要)。
3. **🔴🔴 crux (新規・未存在)**: `(caseB_phi_family … i).X = certainTypeExtension(columnSum k0)`。
   caseB_phi_family の X は `hyp.tau(…)` の R(columnSum)=σ-image 族への projection で、これが
   `certainTypeExtension(columnSum)=δ·∑ω^σ` に一致するのは **(6.8.2.3) pinning 結論** (‖X‖²=‖columnSum‖²=|W₁|、
   X∈ℤ[σ-images]、符号確定)。**structural でなく pinning 依存ゆえ新規 lemma 要。これが真の hard core。**

**📊 honest reckoning**: base glue の機械的 80% は完成 (ν + skeleton)。残る hanchored = (6.8.2.3) per-constituent
本体で、per-φ assembly + hdecomp wiring + **新規 X=cTE pinning identity** の 3 点。これは教科書 (6.8.2.3) の
忠実形式化 (reconstruction、research gap でない) だが **multi-hundred LOC の dedicated focused build**。
loop/end-of-session で rush すると thrash する実績ゾーン。**▶ 次 = fresh focus で (3) X=cTE pinning から
(最 hard・他を gate)、または (1)(2) wiring を先に。正本=本 cont.⁴。**

### session 47: 🔬 RECON — norm-論法ショートカット不在を確定 + columnDecompositionTau 入力は既に全完備(note 訂正)
4 commit (Lean は net-zero: `7fbbdf32` で 2 補題追加 → `571bef53` で削除)。endpoint A 継続。

**⚠ 自己訂正(stale note の修正)**: cont.³ の「hSdiff・htau1_mema=要構成」は **誤り(stale)**。実際は
**既に全部存在**していた — `caseB_column_sub_smul_support` (S08CBA:297) = μ_j−a·η₁ supportedness、
`caseB_column_hSdiff` (S08CBA:315) = hSdiff 両半分、`caseB_column_htau1_mema` (S08CBA:340) = ZIrr membership、
すべて `caseB_column_bundle` (S08CBA:921) が束ねて `CaseBColBundle` を完成済。session 47 で一度 standalone 版
(`columnSum_sub_smul_Yset_support`/`tau_columnSum_sub_smul_mem_ZIrr`)を書いたが既存と重複 ⟹ 規約に従い revert。
**教訓: 新補題前に既存 bundle/helper を grep して被覆確認すること。**

**🎯 ⟹ columnDecompositionTau (S08CBC2:1822) の column-branch 入力は既に全完備** (要構成は無い):
hdeg=`columnSum_inv_apply_one`✅ / hmapagree=`caseB_column_mapagree`✅ / hSdiff=`caseB_column_hSdiff`✅ /
htau1_mema=`caseB_column_htau1_mema`✅ / hχψ・hχbarψ=`caseB_column_orthogonal_Yset`系✅。
さらに `caseB_phi_family`/`caseB_per_phi_anchored_fromYset` も組立済 ⟹ per-φ 機構は note が示唆したより完成度が高い。
**唯一の真の gap = crux pinning `(caseB_phi_family … θ).X = certainTypeExtension(μ_j)`** (cont.⁴ と一致)。
`caseB_per_phi_anchored_fromYset` は `τ(Ind_H θ − aθ·η₁) = (phi_family θ).X − aθ·ν₁` を与える(Y-side pinning
= per_constituent_Y_eq_smul は engine 内部で済)ので、残るは X-side の同定のみ。その入力 hcol/hirr/hirrAnc/
hXaggorth/hdecomp((6.8.2.2) aggregate)の wiring + 新規 X=cTE identity が pinning 本体。

**🔬 norm-論法は hard core を回避しない(将来セッション向け・再調査不要)**: 独立に norm 論法
`‖T − RHS‖²=0` (T=τ(μ_j−a·η₁), RHS=cTEμ−a·ν₁) を精査した結論 — **ショートカット無し**。
- `⟨T,T⟩=‖RHS‖²=w₁+a₀²` は FREE: isometry `dadeIntegralCharacterMap_inner_eq_on_supported_span hyp.dade hyp.hconj`
  (**hyp.tau はこの abbrev = defeq**, μ_j−a·η₁ supported via `caseB_column_sub_smul_support`) + 列 Gram `columnFamily_mu_sum_inner`
  (⟨μ_j,μ_j⟩=w₁, ⟨μ_j,μ̄_j⟩=0) + `inner_columnSum_Yset_eq_zero` + `certainTypeExtension_columnSum_inner`
  (cTE 等長) + `inner_certainTypeExtension_columnSum_coherentYset_extension_eq_zero` (cTEμ⊥ν₁) + ν₁ norm 1。
- **しかし `⟨T,RHS⟩=w₁+a₀²` の cross-term は hard**: `⟨T,cTEμ⟩=w₁` (hXmass) と `⟨T,ν₁⟩=−a₀` (hYmass) に分解されるが、
  **個別に isometry で取り出せない**。τ(μ_j−μ̄_j)=cTEμ−cTEμ̄ は `⟨T,cTEμ⟩−⟨T,cTEμ̄⟩=w₁` の 1 式しか与えず、
  cTEμ 単体は **supported vector の τ-像でない**(μ_j 単体は μ_j(1)≠0 で unsupported)ため、分離する第 2 の独立 isometry 関係が無い。
- reciprocity `inner_tau_eq_inner_restrict` 経由でも hXmass = `⟨μ_j−a₀η₁, Res_L(cTEμ)⟩` で、**Res_L(certainTypeExtension μ_j)
  = Res_L(δ_j ∑ω_{ij}^σ) の構造**(σ-image の制限)に bottom-out — 同じ深い (6.8.2.3) 内容。
- ⟹ **hard core は projection-coeff pinning と同一**: D.X=∑_{α∈R}coeff(α)·α で `coeff(false,i)=1 ∀i ∧ coeff(true,i)=0 ∀i`
  を示すこと(R=`certainTypeR.imageSet`={δ_j ω_{ij}^σ}∪{−δ_j ω_{ij'}^σ}、2w₁ 個; cTEμ=∑_i certainTypeRImage(false,i))。

**🔑 {0,1}-pinning は既存 (5.4.b `norm_eq_and_X_eq_sum_of_norm_Y_ge`, S07:1469) — crux を「E=false-half」に精密化**:
S07_Coherence に既に rich な (5.4)-(5.6) 理論がある(3 回目 grep で確認、重複回避):
- `inner_self_chi_eq_sum_coeff` (S07:1356) = `‖χ‖² = ∑_{α∈R}coeff(α)` (= free fact 2)。
- `inner_self_chi_re_le_inner_self_X` (S07:1382) = (5.4.a) `‖χ‖²≤‖X‖²` (整数 Cauchy-Schwarz `finset_sum_le_sum_sq`)。
- **`norm_eq_and_X_eq_sum_of_norm_Y_ge` (S07:1469) = (5.4.b)**: `‖ψ‖²≤‖Y‖²` ⟹ `‖X‖²=‖χ‖²` ∧
  **`∃ E ⊆ R(χ), X = ∑_{α∈E}α ∧ |E|=‖χ‖²`**。これがまさに私の {0,1}+count 知見(E={coeff=1}、整数核 `finset_sum_eq_sum_sq_iff` ZIrrFourier:313)。
  ⟹ **整数論法を再実装するな**。`‖ψ‖²≤‖Y‖²` は (5.6.2) `inner_self_Y_re_le_inner_self_psi` の逆向きで、
  column では `ψ=a·η₁`, `‖ψ‖²=a²`, `‖Y‖²=a²` (Y-pinning) ⟹ 等号 ⟹ 5.4.b 適用可。

⟹ **crux の真の残務 = `E = {certainTypeRImage(false,i) | i}`** (= false-half、= cTEμ)。5.4.b は「ある E」しか与えず、
**E が共役列 σ-image (true-half {−δ_j ω_{ij'}^σ}) を含まないこと = coeff(true,i)=0 ∀i** が deep gap。
= 単一スカラー `⟨τ(μ_j−a·η₁), certainTypeExtension(μ̄_j)⟩ = 0` (cTEμ̄ = −true-half-sum)。
これは「τ(μ_j−a·η₁) が共役列の σ-image 成分を持たない」= 教科書 (6.8.2.3)/(4.9) の σ-isometry 構造そのもの。

**✅ landed (session 47, `7e961346`, axiom-clean): `certainTypeExtension_columnSum_eq_falseHalf_sum`**
= 構造的橋渡し `cTEμ = ∑_i certainTypeRImage χ₂ χ₂⁻¹ (false,i)`(cTEμ = R-族の false-half-sum)。
= 5.4.b の結論 `X=∑_{α∈E}α` を cTEμ に同定する最終ステップの非自明部分(両辺 δ_j•∑ω_{ij}^σ)。非重複(grep 確認)。

**▶▶ 次 = 単一スカラー `T = ⟨τ(μ_j−a·η₁), cTEμ̄⟩ = 0` の discharge**(これが残る唯一の deep content)。
これは σ-isometry の restriction 構造(`certainTypeOmegaSigma`/§5 σ map の Res_L、`inner_tau_eq_inner_restrict`
経由 `⟨μ_j−a·η₁, Res_L(ω_{ij'}^σ)⟩=0`)を要する **§5/§6 σ-subsystem の focused dive**(multi-hundred LOC、loop 不適)。
**T=0 の素材ポインタ(session 47 調査)**: §6 (4.3) restriction 機構 = `certainType_apply_eq_of_mem_V`
(S06_CertainTypeCharacters:878、`μ_{ij}(v)=δ_j·ω_{ij}(v)` on V⊆W−W₂)/ `inner_omegaColumnDiff_restrict_eq_zero`
(:895)/ `certainType_vanishes_of_ne`(:919); seam 直交性 = `inner_coherentYset_extension_certainTypeOmegaSigma_eq_zero`
(S08CBC2:1303、ν₁⊥σ-image)/ `inner_coherent_extension_certainTypeOmegaSigma_eq_zero`(:1246)/
`columnDecompositionTau_X_orthogonal`(S08CBA:1227、⟨D.X,ν₁⟩=0)/ `certainTypeR_imageSet_orthogonal_dadeOfDiff`
(S08CBHortho:44)。Dade reciprocity = `inner_tau_eq_inner_restrict`(S08CBCorePart2:48)。これらを組み合わせて
`⟨τ(μ_j−a·η₁), ω_{ij'}^σ⟩=0`(自列 anchored 像が共役列 σ-image 成分なし)を出すのが T=0 の本体。
**T=0 さえ出れば残りは機械的**: per-φ 経路で `τ(μ_j−a·η₁)=X−a·ν₁`(Y-pinning は engine 内済) → 5.4.b で
X=∑_{α∈E}α (|E|=‖μ_j‖²=w₁=`columnFamily_mu_sum_inner`) → T=0 で E⊆false-half、|false-half|=w₁ ⟹ E=false-half
(`Finset.eq_of_subset_of_card_le`) → `certainTypeExtension_columnSum_eq_falseHalf_sum` で X=cTEμ → hanchored。
**正本=本 session 47。** T=0 が次セッションの単一の山。

### session 48: 🚨🚨 重大発見 — hanchored (X=cTE) は cTE-glue 固有の **over-constraint** で、教科書が証明しない自列/共役列の relabeling 曖昧性に抵触(T=0 が multi-session 詰まる根本原因を特定)

session 47 の「T=0 が次の単一の山」を**精査して訂正**。Lean commit なし(architecture-level の RECON、要ユーザー判断)。endpoint A 継続だが frontier の **正しさ自体**に疑義。

**🔬 確定事実1: T=0 ⟺ hanchored ⟺ `D.X = cTEμ`(self 枝固定)。**
`coherentCertainTypeSet_union_Yset` は §7 engine `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` を呼ぶ。その `hagreeX: ν = hX.extension = cTE on X` が **ν を cTE に固定**し、`hDτ: ν d = τ d`(d=μ_{k0}−a₀η₁)が `extends_on_supported` で必須。⟹ `hDτ ⟺ cTEμ − a₀ν₁ = τ(μ−a₀η₁) = D.X − a₀ν₁ ⟺ D.X = cTEμ`。これが hanchored の正体。

**🔬 確定事実2: `D.X = cTEμ` は等長性から導けない(3 通りの独立計算で証明)。**
- `⟨τ(μ−aη), τ(μ−μ̄)⟩ = ⟨μ−aη, μ−μ̄⟩ = w₁`(等長)。LHS を展開 ⟹ `#(false∩E) − T = w₁`、ただし T=`⟨τ(μ−aη),cTEμ̄⟩`。これは `|E|=w₁`(既知)の再導出に終わる(`#(false∩E)+#(true∩E)=|E|=w₁` と T=−#(true∩E) で恒等)。
- `⟨τ(μ−aη), τ(μ̄−aη)⟩ = a²`(等長)⟹ `⟨D.X, D.X̄⟩ = 0`(X₁⊥X̄₁)。だが indicator 計算で `[(false,i)∈E][(true,i)∈Ē]=0 ∧ [(true,i)∈E][(false,i)∈Ē]=0` のみ ⟹ E=false-half を**強制しない**。
- `hXmass = ⟨τ(μ−aη),cTEμ⟩` と T は `hXmass = T + w₁`(cTE(μ−μ̄)=τ(μ−μ̄) を代入)で**循環**。どちらも等長単独で出ない。

**🔬 確定事実3(核心)— 明示的反例: `E=Ē=true-half` は全等長制約を満たし `X₁=−cTEμ̄ ≠ cTEμ`。**
基底 {ω_{i,k0}^σ}∪{ω_{i,k0⁻¹}^σ}(2w₁ 正規直交)で:E=true-half ⟹ X₁=∑_i(−δ)ω_{i,k0⁻¹}^σ=−cTEμ̄。Ē=true-half ⟹ X̄₁=∑_i(−δ)ω_{i,k0}^σ。`X₁−X̄₁` の係数 = (ω_{i,k0}: δ, ω_{i,k0⁻¹}: −δ) = `cTEμ−cTEμ̄` ✅、`⟨X₁,X̄₁⟩=0` ✅、`|E|=|Ē|=w₁` ✅。⟹ **等長 + 差分制約は X₁ を {cTEμ, −cTEμ̄} の2枝で曖昧にし、−conj 枝も完全に整合的**。

**🔑 確定事実4 — 教科書 (6.8.1) はこの曖昧性を明示し、case A は relabeling/第3列で解決、case B (6.8.2.3) は解決しない。**
(6.8.1) 原文: 「Considering ((χ₁−aη₁)^τ,(χ₂−χ₁)^τ), we see that **X=χ₁^{τ₁} or X=−χ₂^{τ₂}**. If n≥3, ... X=χ₁^{τ₁} by considering (...,(χ₃−d₃χ₁)^τ). If n=2, we may assume X=χ₁^{τ₁}, **possibly on replacing χ₁^{τ₁} and χ₂^{τ₂} by −χ₂^{τ₂} and −χ₁^{τ₁}**.」← 自列/負共役列の曖昧性を**第3列 or 符号付き relabeling** で resolve。
(6.8.2.3) 原文の証明は per-constituent b_i=a_i pinning((6.8.2.2) aggregate)→ 5.4.b で `α_i^τ=X_i−a_iY`(`X_i∈ℤ[R(χ_i)]`, `X_i⊥Y^{τ₁}`)で**終わり**。`X_i=cTEχ_i` は**一切主張しない**。続く (6.8.2) assembly は `((χ−a₀η₁)^τ, η₁^{τ₂})=(χ−a₀η₁,η₁)=−a₀` のみ要し、これは `(X_i−a₀Y, Y)=−a₀`(`X_i⊥Y`, `‖Y‖²=1`)で出る ⟹ **case B は X_i⊥Y のみで完遂、self/conj の解決不要**。

**⟹ 結論: Lean の cTE-glue は教科書 case B が証明も要求もしない `X=cTEμ`(self 枝)を強制する over-constraint。**
特定の `ofProjection` D(`D.X=proj_{R(μ)}(τ(μ−a₀η₁))`)が −conj 枝(`D.X=−cTEμ̄`)に落ちれば **hanchored は FALSE**。落ちるか否かは σ-image の H^# 上の値(深い §6 σ-machinery)依存で、等長性からは決まらない。これが T=0 が session 13–47 で hard core であり続けた**根本原因**:単一列の (6.8.2.3) では self/conj が原理的に未決で、教科書の解決(第3列 n≥3 / relabeling n=2)は**複数列/orientation の大域構造**を使う。

**🧭 推奨される再アーキテクチャ(要ユーザー裁可)**:
frontier `hanchored`(`X=cTEμ`)は**誤った target の可能性大**。教科書忠実な真の target は **`X⊥Y^{τ₁}` + `(χ−a₀η₁)^τ=X−a₀Y`**(= `caseB_per_phi_anchored_fromYset`/`per_phi_anchored_image` が**既に供給**)。
- 案A(textbook-faithful 再配線): union coherence を cTE-glue でなく「η₁↦Y + L^# 一致」の τ₂ で組む engine に差し替え。`(X−a₀Y, Y)=−a₀` の inner-product 検証のみ要求 ⟹ T=0 不要。障害: τ₂ を IntegralCharacterMap(basis-linear, per-irreducible)として構成する必要があり、`X_i` は列単位(per-irreducible でない)ゆえ basis 構成が awkward。§7 に「per-column anchored image から union を組む」非 glue engine が無い(`retarget_isCoherent_of_supportedDecomposition` は norm-1 既約専用)。
- 案B(orientation 解決): hanchored を `D.X = cTEμ ∨ D.X = −cTEμ̄` に弱め、(6.8.2.3)+第3列/relabeling で正しい枝を選ぶ大域論法を形式化。教科書 (6.8.1) の n≥3/n=2 論法の case-B 版が要る(教科書に明示が無いので reconstruction)。
- 案C(σ-restriction で self 枝を証明): `⟨μ−a₀η₁, Res_L(ω_{i,k0⁻¹}^σ)⟩=0` を H^# 上の σ-image 値から直接示す。session 47 が指した §6 補題(`certainType_apply_eq_of_mem_V` 等)は **V-値専用**で H^# に届かない ⟹ 新規 (6.8.2.2) Res-machinery(`Res_Z φ=aρ_Z+b1_Z`, (6.8.2.1) η^{τ₁} は Z^# 上定数)が要る。multi-hundred LOC。**ただし反例(事実3)が示す通り、単一列では self 枝が成立する保証が無いので案C は案B の orientation 論法と本質的に同じものを要する可能性が高い**。

**▶ 次セッションの推奨**: まず**案A の実現可能性**を精査(textbook-faithful union engine が §7 に組めるか/`exists_decomposition_caseB` 系が per-column X_i⊥Y で union を出せるか)。組めれば T=0 を完全に回避でき最短。組めなければ案B(orientation 大域論法、ChatGPT 相談推奨 [[feedback-ask-chatgpt-for-elided-gaps]])。**いずれにせよ session 47 の「T=0 が単一の山・出れば機械的」は楽観的すぎ — T=0 はそもそも単一列では未決(over-constrained)で、frontier の再定義が先決。**
**正本 = 本 session 48。** session 47 までの「hanchored materialize」路線は事実3/4 により保留。

### session 48 cont.: ✅ ユーザー裁可 = 案A(textbook-faithful 再配線)。具体ビルドプラン + 核心 reduction insight

**決定(ユーザー 2026-06-16)**: frontier を hanchored(T=0/X=cTE)から外し、**案A = textbook-faithful 再配線**で進める。

**🔑 核心 reduction insight(T=0 を深い σ-restriction なしで回避する鍵)**:
column cross-diagonal は irreducible constituent の cross-diagonal の**和**に分解できる:
`μ_j − a₀·η₁ = ∑_i (μ_{ij} − a_i·η₁)`(`a_i = μ_{ij}(1)/|W₁|`, `∑_i a_i = a₀`, 次数一致)。
かつ cTE は per-irreducible(`certainTypeExtension_mu`: `cTE(μ_{ij}) = δ_j ω_{ij}^σ`)で `∑_i cTE(μ_{ij}) = cTE(μ_j)`。
⟹ **各既約 μ_{ij} で per-irreducible hanchored `τ(μ_{ij}−a_iη₁) = cTE(μ_{ij}) − a_i·ν₁` が出れば、和を取って column hanchored が従う**。
だが per-irreducible 版も norm-1 ゆえ X_i = ±(単一 σ-image)で **self/conj 2-枝の曖昧性は残る**(教科書 6.8.1 の「X=χ₁^τ₁ or X=−χ₂^τ₂」そのもの)。

**∴ 真の解決 = 「chain は実際の像 X_i を使い cTE 同定を要求しない」**:
`adjoin_irr_nonreal_of_supportedDecomposition`(S08CBA:1720)/`xAdjoinStepW`(S08CoherenceWeighted:286)/
`retarget_isCoherent_of_supportedDecomposition`(S07:4031)は **`Da.X`(実際の (5.4) 分解像、self でも −conj でも)を使い**、
それが cTE か否かを問わず**有効な coherence を構成する**(`himg: τ(χ−a•χ₁)=Da.X − a•ext(χ₁)` は定義上成立)。
⟹ Xset coherence cX を chain で組めば `cX.extension(μ_{ij}) = X_i`(実像)。Y-glue の diagonal `hDτ: ν(χ−aη₁)=τ(χ−aη₁)`
は `ν=cX.extension` ゆえ **構成上自動成立**(T=0 不要)。cTE は base の coherence にしか使わず、glue には一切使わない。

**🚧 案A の障害(= 次セッションが解く核心)— Lean の Xset 構造の乖離**:
教科書 X = 個々の既約 `{μ_{ij} : Z⊄Ker}`。だが Lean `certainTypeSet h46 k` = **列 columnSum χ₂(既約の和)**で、
`caseB_Xset_conjugatePairCover`(S08CaseBEnumeration:134)は **S₀=certainTypeSet(列)** を base に非-S₀ 既約を pair。
⟹ 列を base coherence(cTE)にした時点で「列の cross-diagonal を cX.extension=cTE で扱う」=T=0 に逆戻り。
**列と個々の μ_{ij} が両方 Xset にあると `μ_j=∑μ_{ij}` の線形関係で `cX.extension(μ_j)=∑X_i` 整合性が要り、これが ∑-form の T=0**。

**▶▶ 案A の具体タスク(次セッション、focused、優先順)**:
1. **Xset/S/certainTypeSet の構造精査**: 個々の μ_{ij} は Xset に入るか?(`hyp.Xset W2` の定義 = S08CoherenceCorePart2:544 を読む)。
   textbook X は μ_{ij} だが Lean は列を S₀ にしている。**μ_{ij} を直接 X-member にできるか**(列を base から外し μ_{ij} を chain adjoin)が分岐点。
2. **per-irreducible 経路が組めるなら**: `caseB_per_phi_anchored_fromYset`(S08CBA:1647、既存)が既約 `Ind_H θ` の anchored 像
   `τ(Ind_H θ − a·η₁) = caseB_phi_family.X − a·ν₁` を与える。これを `adjoin_irr_nonreal_of_supportedDecomposition` に渡し
   chain で Xset coherence を組む → Y-glue は diagonal 自動。**cTE-glue base(`coherentCertainTypeSet_union_Yset`)は捨てる**(現在下流未消費なので影響なし)。
3. **列を base に残す必要がある場合**: 列 hanchored = ∑(per-irreducible hanchored) の線形 reduction を使うが、per-irreducible でも
   self/conj 解決が要る ⟹ 教科書 (6.8.1) の n≥3/relabeling 大域論法の case-B 版(ChatGPT 相談候補)。**1 より重い**。

**現状の資産(壊さない)**: `coherentCertainTypeSet_union_Yset`(hanchored gated skeleton)は下流未消費ゆえ**当面温存**(案A 確定後に撤去/置換)。
`exists_glue_nu_columnSum_Yset`/`certainTypeExtension_columnSum_eq_falseHalf_sum` 等は cTE-glue 専用なので案A では不要化するが削除は最後。
**正本 = 本 session 48 cont.。次の一手 = タスク1(Xset 構造精査)。**

### session 48 cont.²: ✅ 案A の健全な形を確定(cont. の per-μ_{ij}/basis-linear 懸念を精密化・解消)— Xset 構造精査の結論

**🔑 Xset 構造の確定事実**(`SsubFiltration`/`Xset` = S08CoherenceCorePart2:535-546 を読んだ):
`Xset hyp Z = hyp.S \ hyp.SsubFiltration Z`、`hyp.S = {Ind_H^L θ : θ∈Irr H, θ≠1}`。⟹ **X-member は誘導指標 Ind_H^L θ**。
- reducible な X-member = 列 `μ_j = columnSum = Ind_H^L χ_j`(χ_j=Res_H μ_{0j}∈Irr H、`columnSum_eq_induce_H`)。
- 個々の `μ_{ij}` は **W₁-軌道の構成要素で Ind でない ⟹ X に入らない**(cont. の「μ_{ij} を adjoin」は不可、訂正)。
- 既約な X-member = Ind_H^L θ で Ind が既約なもの(教科書 6.8.2.3 の χ_i = Ind_H θ_i、θ_i = Ind_Z φ の構成要素)。

**🎯 案A の正しい形(cont. の混乱を解消)— Y-glue を「列∪Y」でなく「full Xset」で、既約 anchor を使う**:
1. **cTE-base**: `certainTypeSet`(列)を **単独で** coherent(`certainTypeSet_isCoherent_tau`、cTE)。**Y なし ⟹ T=0 なし**。✅既存。
2. **chain**: `xChainCoherentW`(S08CoherenceWeighted:556)で既約 X-member pair を base に fold → **Xset coherent cX**。
   各既約 χ の adjoin は **実際の (6.8.2.3) 像 X_χ を使う**(`xAdjoinStepW`/`adjoin_irr_nonreal_of_supportedDecomposition`、
   `Da.X` 経由、cTE 同定不要)。cover = `caseB_Xset_conjugatePairCover`(S08CaseBEnumeration:134)✅既存。
   cX は coherence ゆえ `cX.ext` は **ℤ[Xset,L^#] 全体で τ 一致**(`extends_on_supported`)— 列像 cTE(μ_j) と既約像 X_χ の
   整合は **chain の coherence 証明が確立**(standalone T=0 でなく)。
3. **Y-glue**: `coherentXunionYset_caseB_of_glued`(S08CBC2:1616)で cX ⊕ Y。**diagonal anchor に既約 X-member χ₀** を使う。
   `hDτ: ν(χ₀−a₀η₁)=τ(χ₀−a₀η₁)` は `ν=cX.ext(χ₀)=X_{χ₀}`(chain 像)ゆえ **構成上自動**。

**🔑 列の cross-diagonal は既約 anchor + X-internal に分解 ⟹ 列の hDτ は T=0 なしで従う**:
`μ_j − a₀η₁ = (μ_j − χ₀) + (χ₀ − a₀η₁)`(χ₀ = 列と同次数 a₀|W₁| の既約 anchor)。
- `μ_j − χ₀`: 次数 0、H^#-supported(両者 Ind_H、H 正規ゆえ support⊆H、1 で消える)、∈ ℤ[Xset,L^#] ⟹ `ν=τ`(**cX coherence**)。
- `χ₀ − a₀η₁`: 既約 anchor diagonal ⟹ `ν=τ`(自動、chain 像)。
⟹ `hgen` が `{μ_j−χ₀}∪{χ₀−a₀η₁}` で列 cross-diagonal を生成すれば、列 hDτ は線形性で従う。**cTE(μ_j) は Y-diagonal に直接現れず、X-internal 経由で cX coherence が吸収 ⟹ standalone T=0 不要**。

**🚧 案A が依存する未検証前提(次セッションの検証標的、優先順)**:
1. **既約 X-member anchor χ₀ の存在**(列と同次数 a₀|W₁|)。case B は Z=W₂⊆H' ゆえ degree-1 X-member 無し(a₀>1)。
   ⟹ anchor は次数 a₀|W₁| の **既約 Ind_H θ**(θ(1)=a₀, Ind 既約)。存在は H 構造依存 — **要確認**(教科書 χ_i のどれかが既約か)。
   存在しない(全 X-member が列=reducible)региме では案A の anchor が無く、別途 reducible anchor の hDτ=T=0 に戻る恐れ。
2. **chain adjoin の decomposition 入力**: 既約 χ の base(cTE 列)に対する (6.8.2.3) 分解。`caseB_per_phi_anchored_fromYset`
   が anchored 像を与えるが、その full aggregate 入力(hcol/hirr/hirrAnc/hdecomp)の discharge が要る(既存 skeleton)。
3. **hgen**(列 cross-diagonal が既約 anchor + X-internal で生成)の形式化。

**▶▶ 次の一手**: 前提1(既約 X-member anchor の存在)を確認。存在すれば案A は既存インフラ(xChainCoherentW +
coherentXunionYset_caseB_of_glued)で組め、cTE-glue base(coherentCertainTypeSet_union_Yset)は不要化(撤去)。
存在が問題なら、教科書 (6.8.2) の τ₂ 構成(L^# 一致 + η₁↦Y の abstract isometry)を Lean で直接組む engine が要る
(basis-linear IntegralCharacterMap では列=Σμ_{ij} ゆえ per-μ_{ij} 値が要り、自然な cTE が T=0 を呼ぶ ⟹ ChatGPT 相談候補)。
**正本 = 本 session 48 cont.²。session 48 cont. の「per-irreducible で adjoin」は Xset 構造誤認ゆえ撤回、本 cont.² が正。**

### session 48 cont.³: 🔄 先行 course-correction との照合 — cont.² の chain 経路は detour、真の crux = reducible-column coherence producer

**重要照合(memory `peterfalvi-s6-coherence-reduction.md` 最新エントリ 2026-06-16「原典精読 course-correction」と突合)**:
先行 lane-b セッションが既に `references/peterfalvi/04.8.mmd` L156-244 を全文精読して確定していた:
- **case-B (6.8.2) = τ₂ 直接構成**(τ on Z[X∪Y,L^#] 一致 + η₁^{τ₂}=Y)。per-χ (6.8.2.3) `(χ−aη₁)^τ=X₁−aY` で τ₂ 内積保存。
- **chain adjoin (`xChainCoherentW`) は case-A (6.6) `X⊂Irr L` 専用 — case-B では DETOUR**(valid lemma だが経路外)。
- 正しい cX = per-χ (6.8.2.3) → `IsCoherent(Xset)` via τ₂|_X だが **組立未完 = IsCoherent(Xset) 産出器が無い**。

**⟹ 私の session 48 の位置づけ(訂正)**:
- session 48 の T=0 over-constraint 厳密証明(等長性から未決・反例・self/conj 曖昧性)は**この先行 course-correction と完全に整合**
  (cTE-glue の X=cTE 要求が間違い、textbook は X₁⊥Y のみ — 同じ結論を独立に厳密化した)。
- **cont.² の「xChainCoherentW で既約 anchor」案は先行セッションが detour 判定した chain を再提案 ⟹ 撤回**。

**🎯 真の crux(全セッション通じての根本、未解決)= basis-linear 枠での reducible-column coherence producer**:
case-B Xset は **reducible 列 μ_j を含む**。`IsCoherent.extension` は **IntegralCharacterMap = Irr(L) basis 上 ℤ-linear** ゆえ
τ₂ は per-μ_{ij} 値で決まる。per-χ (6.8.2.3) は **列レベルの像 X_χ しか与えない** ⟹ τ₂(列)=X_χ を満たす per-μ_{ij} 割当は
**未決定**で、自然な cТЕ 割当は T=0 を呼ぶ。これが全 3 経路がブロックされる共通根:
- 経路1 cTE-glue(s44-47): T=0 要求(over-constrained、本 session 48 で反駁)。
- 経路2 per-χ τ₂ 直接(先行・textbook 忠実): producer 無し(列レベル像から basis-linear τ₂ を組む = 同じ未決定性)。
- 経路3 chain(cont.²/xChainCoherentW): case-A 専用 detour。
- **教科書はこれを抽象 ℤ-linear τ₂ on ℤ[X∪Y](Irr(L) basis 全体に拡げない)で回避** — Lean の IntegralCharacterMap 枠と不整合。

**▶▶ 推奨される次の一手(要 focused/相談)**: 教科書 (6.8.2) の **abstract ℤ-linear τ₂ on ℤ[X∪Y]** を Lean で構成する方法
(IntegralCharacterMap を ℤ[X∪Y] 部分格子上で組むか、basis 拡張の per-μ_{ij} 自由度をどう埋めるか)を **ChatGPT 相談**
([[feedback-ask-chatgpt-for-elided-gaps]]、最強モデル)。または reducible-member coherence producer engine の設計。
これは単一セッションを超える**深いアーキ crux で複数セッション thrash 済**(s44-47 cTE / 先行 per-χ / cont.² chain)。
**正本 = 本 session 48 cont.³(cont.² の chain 案を supersede、先行 τ₂-direct course-correction を再確認 + T=0 反駁で厳密化)。**

### session 48 cont.⁴: ✅ 検証 workflow (6-agent, 実コード精読+敵対反証) で T0-FREE-CONFIRMED — cont.³ の「no producer」過度悲観を訂正

**6-agent workflow 結論 (実 file:line 精読)**: ユーザーの直感「文献どおりなら問題は起きない」は **正しい**。確定事項:
- **T=0/hanchored は cTE-glue 配線固有の artifact**(`coherentCertainTypeSet_union_Yset` S08CBXunionY:356-359 が RHS に cTE を使うため `D.X=cTE` を強制)。**decomposition 機構自体は T=0-free**: `columnDecompositionTau`(`ofProjection`, S07:1185, `D.X=∑coeff•α` は τ₁(χ−ψ) の **R(χ) への直交射影**で cTE 非依存)+ `per_phi_anchored_image`(S08CBC2:1908, `τ(χ−aη₁)=D.X−a•cY.ext η₁`)+ `per_constituent_Y_eq_smul`(Y-pinning)。どこも `D.X=cTE` を要求しない。
- **session 48 本体の over-constraint 証明(反例 E=Ē=true-half ⟹ X₁=−cTEμ̄)は厳密・正しい**(5.4.b は `E⊆R(μ_j), |E|=‖μ_j‖²` のみで E=false-half を同定しない)。
- **🔴 cont.³ の「basis-linear 枠で reducible-column coherence producer が無い = 全経路の共通根」は過度悲観・部分的に誤り**。Probe C 確認: 列は disjoint 基底 support で**線形独立** ⟹ `Basis.constr` で `extension(μ_j)=X_χ_j` を割当可能(IsCoherent は `ℤ[列]` 上のみ拘束、個々 μ_{ij} 値は自由)。**producer は構成可能**。
- **🔴 cont.³ の「chain は case-A detour ゆえ撤回」も訂正**: cont.² の **既約 anchor 経路は sound**(workflow が再確認)。`xChainCoherentW`+`caseB_Xset_conjugatePairCover`(S08CaseBEnumeration:134)は case-B 用に存在し、既約 X-member を実像 `Da.X` で fold(cTE 非依存)。

**🎯 確定した T0-free 経路(2 sub-route、いずれも cTE-glue を捨て (6.8.2.3) 実像 X_χ を使う)**:
- **案A1(cTE-base + chain + 既約 anchor)**: 列を cTE-base で単独 coherent(Y なし=T=0 なし)→ chain で既約 fold → cX → Y-glue を**既約 anchor χ₀**(列同次数 a₀|W₁|)で。列 cross-diagonal `μ_j−a₀η₁=(μ_j−χ₀)+(χ₀−a₀η₁)`、前者 cX.extends_on_supported・後者 chain 像 ⟹ hDτ auto。**唯一の未検証前提 = 既約 X-member anchor の存在**(case B は Z=W₂⊆H' ゆえ a₀>1; (6.8.2.3) の χ_i=Ind_H θ_i のどれかが既約か = 構造事実、要教科書確認)。
- **案A2(full X_χ-coherence、前提不要・最 robust)**: **全列**に (6.8.2.3) 実像 X_χ_j を割り当てた cX を Basis.constr で構成。等長 `⟨X_j,X_l⟩=⟨μ_j,μ_l⟩`(等長性から従う、Probe B)+ `extends_on_supported`(2 つの (6.8.2.3) 像の差 `τ(μ_j−μ_l)=X_j−X_l`)。すると **任意の anchor(列でも)で hDτ auto** ⟹ 既約 anchor 前提不要。

**▶▶ 残作業(T=0 でない、real だが原理的障害なし)**: (3b) `caseB_per_phi_anchored_fromYset`(S08CBA:1647)の aggregate 入力(hcol/hirr/hirrAnc/hXaggorth/hdecomp = (6.8.2.2) per-φ b_i=a_i pinning)を**全列**で discharge → (案A2) Basis.constr で cX 構成 + 等長/agreement → glue(`coherentXunionYset_caseB_of_glued` S08CBC2:1616, cX 入力)→ (6.8.3) break → sole sorry。完成後 `coherentCertainTypeSet_union_Yset`/`exists_glue_nu_columnSum_Yset`/`certainTypeExtension_columnSum_eq_falseHalf_sum`(cTE-glue 専用、下流未消費)を撤去。
**ChatGPT 相談は不要**(route は T=0-free + 既存インフラ)。**正本 = 本 session 48 cont.⁴**(cont.² sound・cont.³ 過度悲観を訂正、workflow `wf_7aeebca4-e2c` で code-verified)。

### session 48 cont.⁵: ✅✅ T=0-free base-union 実装完了 (2 commits, build-green, axiom-clean) — frontier が「不可能な T=0」→「4 dischargeable obligation」に転換

案A を実コードで実装。新 leaf `S08_CaseBXChiCoherence.lean`:
- **`xChiExtensionFun`/`xChiExtension`/`xChiExtension_mu_zero`/`_ne_zero`/`xChiExtension_columnSum`** (commit `57a95174`):
  列 μ_j=columnSum χ₂ を (6.8.2.3) 射影像 `Ximg χ₂` に送る大域 IntegralCharacterMap (Basis.constr + 0th-row trick)。
  ⚠ **pair-existential `∃ p, μ_{p.1,p.2}=ω ∧ p.2=0`** が必須 (単一-χ₂ existential は injectivity 適用時に
  `hex.choose` の pair packaging で whnf 爆発 → timeout; 原型 `certainTypeExtension_mu` の pair 構造に倣う)。
- **`certainTypeSet_isCoherent_via_anchoredImages`** (commit `57a95174`): IsCoherent hyp.tau (certainTypeSet)、
  extension=xChiExtension。3 field を列レベル仮説から証明 (cTE 非依存)。
- **`exists_glue_nu_columnSum_Yset_via_map`** (commit `cc7f27db`): glue を νX 一般化
  (`exists_integralCharacterMap_glue_of_orthonormal` は **source の正規直交のみ要し target νX 任意** — 私の
  「target 正規直交要」懸念は誤りだった)。νX=xChiExtension で ν(列)=Ximg。
- **`coherentCertainTypeSet_union_Yset_via_anchoredImages`** (commit `cc7f27db`): IsCoherent hyp.tau
  (certainTypeSet ∪ Y)。**核心成果: hDτ (cross-diagonal) が `hXanchored` ((6.8.2.3) 像) から 1 行で成立、
  T=0 (Ximg=cTE) を一切要求しない**。`coherentCertainTypeSet_union_Yset` (cTE-glue, hanchored=T=0 gated) の
  textbook-faithful 代替。⚠ hXanchored は **membership 形** (`columnSum χ₂ ∈ certainTypeSet`) で k0/k0' ミスマッチ回避。

**⟹ frontier 転換確定**: 「不可能/over-constrained な T=0」は消滅。残るは base-union の 4 gated obligation
(全て (6.8.2.3) per-column 出力、**dischargeable**、T=0 でない):
- `hXanchored` = `τ(columnSum χ₂ − a₀η₁) = Ximg χ₂ − a₀·cY.ext(η₁)` (per-column anchored image)。**最重 = (6.8.2.2) aggregate**。
- `hXinner` = `⟨Ximg χ₂, Ximg χ₂'⟩ = ⟨columnSum χ₂, columnSum χ₂'⟩` (cross-column 等長、τ-isometry から)。
- `hXzirr` = `Ximg χ₂ ∈ ZIrr G` (D.X ∈ ℤ[R])。
- `hXmixed` = `⟨Ximg χ₂, cY.ext y⟩ = 0` (seam-1 X_χ⊥Y^{τ₁}、既存 `inner_decomposition_X_coherentYset_extension_*`)。

**▶▶ 次セッション = 4 obligation の discharge**。設計: `Ximg χ₂ := (columnDecompositionTau D_{χ₂}).X`
(射影像、cTE 非依存)。hXanchored = `per_phi_anchored_image` (S08CBC2:1908) を列に適用 (Y-pinning 内済) —
入力 = `exists_decomposition_caseB` (S08CBC2:126) の (6.8.2.2) aggregate `hdecomp` + bundles
(`caseB_column_bundle` 等、session 47 で全完備確認済)。hXinner/hXzirr/hXmixed は D.X から機械的。
完成後 `coherentCertainTypeSet_union_Yset`/`exists_glue_nu_columnSum_Yset`/`certainTypeExtension_columnSum_eq_falseHalf_sum`
(cTE-glue 専用、下流未消費) を撤去。**正本 = 本 session 48 cont.⁵。ChatGPT 不要、既存インフラで closeable。**

### session 48 cont.⁶: discharge 経路マップ (Explore agent + 批判的評価) — 機械的 2 obligation vs Y-pinning hard core

T=0-free base-union の 4 obligation を `Ximg χ₂ := (columnDecompositionTau D_{χ₂}).X` で discharge する経路を精査。
**⚠ Explore agent の「4 つとも residual なしで closed」は過度楽観**(`.tau1_image` を Y-pinned 形と混同)。正確な分類:

**機械的 (信頼可、既存補題直結)**:
- `hXzirr` (`D.X ∈ ZIrr G`): `CharacterPsiDecomposition.X_eq` (`X=∑coeff•α`) + `imageFamily.mem_ZIrr` + `Submodule.sum_mem`。columnRFamilyTau.imageSet = certainTypeR.imageSet (各 σ-image ∈ ZIrr)。
- `hXmixed` (`⟨D.X, cY.ext y⟩=0`): **既存 `inner_decomposition_X_coherentYset_extension_eq_zero_of_mem_Yset` (S08CBC2:1390)** が D (imageSet が certainTypeRImage で covered な `himg` 付き) に対し `⟨D.X, coherentYset.ext η₁⟩=0` を与える。columnDecompositionTau の imageSet は certainTypeR ゆえ himg 充足。

**hard core (Y-pinning、(6.8.2.2) aggregate 本体)**:
- `hXanchored` (`τ(μ−a₀η₁) = D.X − a₀·cY.ext(η₁)`): `.tau1_image` は `τ(μ−a₀η₁) = D.X − D.Y` のみ。**`D.Y = a₀·cY.ext(η₁)` (Y-pinning) が非自明** = `per_constituent_Y_eq_smul`/`certainType_per_constituent_Y_eq_smul` (S08CBC2:1485) で、(6.8.2.2) aggregate (`hagg`/`hsq`/`hXaggorth`/`hbi`) を要する。aggregate は **`exists_decomposition_caseB` (S08CBC2:126, sorry-free)** が産むが、入力に case-B 構造仮説 (`hcop`/`hp`/`hHp`/`hprime`/`hW2comm`/`hW2cen`/`hφ1`/`hφ`/`hc2`/`hFPF`) を要する = **capstone レベルのデータ**。
- `hXinner` (`⟨D_χ₂.X, D_χ₂'.X⟩ = ⟨μ_χ₂, μ_χ₂'⟩`): cross-column 等長。`D.X = τ(μ−a₀η₁)+a₀cY.ext(η₁)` (Y-pinned anchored image から) を使い τ-isometry + `columnFamily_mu_sum_inner` + seam (X⊥Y)。**hXanchored の Y-pinning に依存** (D.X の anchored 形が要る)。

**確定した既存資産 (sorry-free、再利用可)**: `exists_decomposition_caseB` (6.8.2.2 aggregate 産出), `caseB_column_bundle` (S08CBA:921, columnDecompositionTau 入力供給), `caseB_per_phi_anchored_fromYset` (S08CBA:1647, per-φ anchored image w/ Y-pinning), `caseB_phi_family`, seam `inner_decomposition_X_coherentYset_extension_eq_zero_of_mem_Yset`。

**▶▶ discharge wrapper の設計 (次セッション、capstone-level)**: case-B 構造仮説を取り、
(1) `exists_decomposition_caseB` で (6.8.2.2) aggregate (cY, Xagg, hdecomp) を得る →
(2) `caseB_per_phi_anchored_fromYset` (or per_phi_anchored_image) で per-column anchored image
    `τ(μ_j−a₀η₁) = caseB_phi_family.X − a₀·cY.ext(η₁)` (Y-pinned) を得て **Ximg χ₂ := caseB_phi_family.X** と置く →
(3) hXanchored = (2) 直結、hXinner = (2)+isometry、hXzirr/hXmixed = 機械的 →
(4) `coherentCertainTypeSet_union_Yset_via_anchoredImages` を呼ぶ。
**hard core = (1)(2) の per-φ 機構を全 column で組む assembly** (新 math 無し、既存 sorry-free 補題の wiring、
ただし case-B 構造仮説の threading + φ-family ↔ column の同定で multi-hundred LOC)。
**T=0 は完全に消えた**(base-union が hXanchored から hDτ を出す)。**正本 = 本 session 48 cont.⁶。**

### session 48 cont.⁷: ✅ discharge を hXanchored 1 本に削減 — hXinner 導出 + hXzirr brick landed

3 commits (`944055f2`/`05722cc5` + 本 note)。base-union の 4 obligation のうち 3 を解決し、hard core を hXanchored 1 本に圧縮:
- **hXzirr** ✅ `characterPsiDecomposition_X_mem_ZIrr` (汎用、D.X=∑coeff•α + imageFamily.mem_ZIrr)。
- **hXinner** ✅ `xchi_inner_eq_of_anchored` — **hXanchored から代数的に導出** (別途 Y-pinning 不要):
  `Xj=τ(μj−a₀η₁)+a₀ν₁` (hXanchored 移項) + hXmixed (Xj⊥ν₁) + τ-等長 (`dadeIntegralCharacterMap_inner_eq_on_supported_span`) + 列⊥Y + ‖η₁‖²=‖ν₁‖²=1 ⟹ `⟨Xj,Xl⟩=⟨μj−a₀η₁,μl−a₀η₁⟩+a₀²−a₀²−a₀²+a₀²=⟨μj,μl⟩`。**これが key 簡略化**: 当初 hard core ×2 (hXanchored+hXinner) と見ていたが hXinner は hXanchored の系。
- **hXmixed** = 既存 `inner_decomposition_X_coherentYset_extension_eq_zero_of_mem_Yset` (Ximg=D.X、himg=imageSet⊆certainTypeRImage)。
- **hXanchored** = 唯一残る hard core = (6.8.2.2) aggregate `Y`-pinning。

⚠ Lean 知見 (再調査不要): hXinner 証明で `set τj/τl` は hanc を τj-form に畳んで後続 rw を壊す → τ-項は明示参照。
cross-term の inner_smul_left は `rw` でなく `simp only [..., inner_smul_left, star_natCast]` で robust 化 (nsmul→ℂ-smul の `← Nat.cast_smul_eq_nsmul ℂ a₀ ν` 後)。

**▶▶ 残る唯一の discharge = hXanchored**: `Ximg χ₂ := (columnDecompositionTau D).X`、
`τ(μ_j−a₀η₁) = Ximg χ₂ − a₀·cY.ext η₁` を `caseB_per_phi_anchored_fromYset` (S08CBA:1647) で。
入力 = `exists_decomposition_caseB` (S08CBC2:126, sorry-free) の (6.8.2.2) aggregate + caseB_hcol/hirr bundles +
case-B 構造仮説 (capstone level: hcop/hp/hHp/hprime/hW2comm/hW2cen/hc2/hFPF) + 列↔constituent 同定
(`columnSum_eq_induce_H`)。これが (6.8.2.3) per-φ assembly の本体 (新 math 無し、既存 sorry-free 補題の wiring)。
**正本 = 本 session 48 cont.⁷。** 完成後 cTE-glue 旧ファイル群 (下流未消費) を撤去。

### session 48 cont.⁸: 🧹 cTE-glue dead code 撤去 (over-constrained T=0 route の片付け)

cont.⁴ で確定した「cTE-glue は over-constrained ゆえ撤去」を実施 (commit `e52aee95`、184 行削除)。
grep で外部 caller なしを確認した dead def 3 本を S08_CaseBXunionY から撤去:
- `certainTypeExtension_columnSum_eq_falseHalf_sum` (参照ゼロ、T=0 falseHalf bridge の残骸)
- `exists_glue_nu_columnSum_Yset` (旧 base 専用、`exists_glue_nu_columnSum_Yset_via_map` が一般化済)
- `coherentCertainTypeSet_union_Yset` (caller なし、unprovable な hanchored=T=0 に gate された旧 base)
keep (textbook 経路が再利用): `certainTypeSet_span_apply_one_eq_intMul` / `hgen_withDiagonal_certainTypeSet` / `certainTypeSet_finite`。
**⚠ (4.9) cTE coherence 機構 (`certainType_isCoherent`/`certainTypeExtension`/`certainTypeSet_isCoherent_tau`) は孤立せず存続** — 正当な Peterfalvi (4.9)(b) 結果ゆえ unused でも残す (過剰削除しない)。full build (3840 jobs) green、axiom 不変。

**本セッションの新規 Lean は dead/garbage なし**: textbook 経路の連鎖 (xChiExtension→producer→glue→base-union) は全 used、
discharge 用 brick (`characterPsiDecomposition_X_mem_ZIrr`/`xchi_inner_eq_of_anchored`) は意図的 down-payment (docstring 明示)。
迷い (chain 経路 cont.²→撤回 cont.³) は notes/分析のみで Lean commit には出ていない。**正本 = 本 session 48 cont.⁸。**
