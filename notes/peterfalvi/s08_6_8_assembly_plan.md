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
