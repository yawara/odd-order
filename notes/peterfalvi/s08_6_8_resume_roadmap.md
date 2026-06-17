# Pf (6.8) case-B resume roadmap — 正本 (2026-06-17, 2 workflow + Plan agent + 直接 grep で code-verified)

> この note が **S08:59 `sibleySetup_is_coherent` を閉じるための現行 source-of-truth**。churn した
> `s08_6_8_assembly_plan.md`(458KB)/`s08_6_8_3_gap_resolution.md` のうち本 note と矛盾する記述は本 note を優先。
> 上位方針・FT 接続の文脈 = 記憶 [[ft-path-policy]] の 2026-06-17 検証訂正ブロック。

## ✅ 2026-06-17 セッション更新 — brick 1 COMPLETE (`caseB_member_psiDecomposition`)

**brick 1 = 着地** (`S08_CaseBEnumeration.lean` 末尾、build-green 3628 jobs・axiom-clean `[propext,
Classical.choice, Quot.sound]`)。per-member Dmem dispatcher: `x ∈ S₁ ⊆ hyp.S`(conj-closed coherent)
→ `CharacterPsiDecomposition hyp.tau x 0`。

**実装で確定した roadmap 訂正 (6-agent workflow + 直接 grep で code-verified)**:
1. **classifier は `x ∈ hyp.S` を取る (S₁ でない)** — `caseB_S_member_column_or_irreducible`
   (`S08_CaseBAssembly:1949`) は S-level。brick 1 は `hS₁sub : S₁ ⊆ hyp.S` で橋渡し。
2. **irreducible 枝の facts は `caseB_irr_*` (induce-θ 形) を使う。`xMember_*_of_irreducible_X` は NG** —
   後者は `hX : ∀ φ ∈ Xset Z, IsIrreducibleCharacter φ`(Xset 全 irreducible)を要求するが case-B は
   まさに X が reducible column を含むケースゆえ偽。正しい供給源:
   - hreal = `caseB_irr_nonreal hyp hirr`(`S08_CaseBAssembly:578`、奇位数 Burnside)
   - hdiffsupp = `caseB_irr_conj_diff_support hyp θ`(`S08_CaseBAssembly`)
   - hχχbar = `caseB_irr_conj_inner hyp hirr`(`S08_CaseBAssembly`)
   - column hagree = `caseB_column_mapagree hyp h46 hχ₂`(`:194`、roadmap 既述通り)
   - column hdeg = `(columnSum_inv_apply_one h46 χ₂).symm`、hdiffsupported = `columnDiff_support_subset`
     + `mem_zSupportedSpan_iff`。
3. **Type-vs-Prop 消去の罠 (再調査不要)**: 出力 `CharacterPsiDecomposition` は `Type`。`x ∈ S` の
   `∃`、dispatch の `∨` は `Prop` ⟹ `obtain`/`rcases` で `Type` goal に消去できない
   (`Exists.casesOn can only eliminate into Prop`)。対処:
   - column index χ₂ は `by_cases hcolumn : ∃ χ₂, …` + `hcolumn.choose`/`.choose_spec`(noncomputable
     関数、Type 消去可)。
   - irreducible 判定は `(caseB_S_member_column_or_irreducible …).resolve_left hcolumn`(Prop→Prop)。
   - inducing source θ は **top で抽出しない**(`set θ := choose` は x への循環依存を作り
     `rw [← hcol]`/`rw [hxeq]` が「revert dependencies」で失敗)。irreducible facts は各々 `Prop`-have
     内で `obtain ⟨θ, _, hxeq⟩ := (hxS の S_eq 展開)` → `rw [hxeq]`(θ は fresh、循環なし)。
   - column 主 goal の `columnSum χ₂ → x` 変換は `hcol ▸ (term)`(term-level、循環なし。`rw [← hcol]`
     は χ₂ が x 依存ゆえ NG)。
4. memberExtensionDecomposition は **x をそのまま** χ:=⟨x,hirrx⟩ で渡せる(induce 形不要)。返り値
   `CharacterPsiDecomposition (dade…) x 0` は `hyp.tau` abbrev と defeq ⟹ 変換不要。

## ✅ brick 2a COMPLETE + brick 2/3 詳細設計 (2026-06-17, 3-agent scope workflow code-verified)

**✅ brick 2a = `exists_finEnum_general`**(`S08_CaseBEnumeration.lean`、build-green・axiom-clean)。
一般有限集合 `S : Set (ClassFunction Γ ℂ)` を injective `Fin k`-family に列挙(irreducible 不要)。
= `Set.Finite.fintype` + `Fintype.equivFin` の純 formalization(数学ゼロ)。reducible column を含む
case-B coherent set の列挙プリミティブ。`exists_finEnum_irreducible`(`CorePart1:631`)の一般版。

### brick 2 full = weighted enumerator(次の大物、multi-hundred LOC)

unweighted テンプレート = **`sMember_degreeSumBound_of_not_coherent`**(`CorePart2:2650`、8 step)。
weighted 版 brick 3 = `sMember_degreeSqNormBound_of_not_coherent` はこれを mirror し step 8 で
weighted engine `coherentDegreeSqNormBound_of_not_coherentW`(`S08_CoherenceWeighted:475`、結論
`∑ deg²/mc ≤ 2a`)を叩く。**step 1-7 は generic(orthonormality 非依存)= unweighted をほぼコピー**。

weighted engine が unweighted と異なり要求する **NEW 4 inputs**(= brick 2 が供給):
- **`mc : Fin k → ℝ`** = `(⟨χmem i, χmem i⟩).re`。column = **|W₁|**(`columnFamily_mu_sum_inner`
  `S06_CertainTypeIsometry:1094` = `if χ₂=χ₂' then |W₁| else 0`)、irreducible = **1**。
  `hmempos`(全 > 0)、**`hanchorNorm : mc i₁ = 1`** ⟹ **anchor は irreducible で取る**
  (= Yset メンバー、`isIrreducibleCharacter_of_mem_Yset` + degree |W₁| `Yset_apply_one`。
  reducible column を anchor にしてはいけない)。
- **`Dmem`** = brick 1 `caseB_member_psiDecomposition`(✅ DONE)。
- **`hortho_mem : ∀ i, (Dmem i).imageFamily.Orthogonal (dadeOrthonormalCharacterImageFamilyOfDiff … ψ)`**
  = column は `certainTypeR_imageSet_orthogonal_dadeOfDiff`(`S08_CaseBHortho:44`)、
  irreducible は `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`(`CorePart1:1681`)。
- **`htau1Dmem : ∀ i, (Dmem i).tau1 (χmem i) = hS₁.extension (χmem i)`** = 両 producer とも
  tau1 = `hS₁.extension` ゆえ **rfl**。

**`hmemortho`**(`∀ i j, ⟨χmem i, χmem j⟩ = if i=j then mc i else 0`)の組立 = 全 per-pair 補題実在:
col-col 直交=`inner_columnSum_cross_eq_zero`(`CaseBAssembly:1850`)/col self=上記 Gram/
col-irr=`caseB_inner_irr_columnSum_eq_zero`(`:1801`)+ conj `:1875`/irr-irr=`irreducibleCharacter_inner_eq_ite`/
col-Y=`inner_columnSum_Yset_eq_zero`(`:250`)/irr-Y=`inner_irr_Yset_eq_zero`(`:611`)。
**統合済 X⊥Y = `caseB_Xset_orthogonal_Yset`(`CaseBAssembly:1970`)**。member を column/irr で dispatch して組む。

### brick 2/3 推奨着手順
1. brick 2 enumerator: `exists_finEnum_general` で S₁=X∪Y を列挙 → 各 member に brick 1 で Dmem、
   `mc` を `⟨χmem i,χmem i⟩.re` で定義、`hmemortho` を per-pair dispatch で組む、anchor を Yset から取る。
2. brick 3: unweighted `sMember_degreeSumBound_of_not_coherent` の step 1-7 をコピー、step 8 で
   weighted engine、最後に real-part scaling(`sMember_degreeSqReBound_of_not_coherent` `CorePart2:2738` mirror)。
3. brick 4 = c2 endgame `false_of_coherentXunionYset_caseB_of_not_coherentS`(weighted+FPF mirror)
   → S08:59 の 3-way dispatch。
**正本詳細 = この note + scope workflow result(transcript)。再調査不要: enum/orthogonality 在庫は full。**

## 結論 (一言)

bootstrap 経路は **viable**。`gap_resolution` note の「残務 = glue のみ」は誤りだが、Plan agent の
「(6.5) p-group reduction 未形式化で blocked」**も誤り**。真の残作業は **hard core 1 本 + wiring**:

- **HARD CORE (genuine new math, 未実装)**: `sMember_degreeSqNormBound_of_not_coherent` =
  **reducible 込みの重み付き member-family を break pair から列挙する補題**。unweighted 版
  `sMember_degreeSqReBound_of_not_coherent`(`S08_CoherenceCorePart2:2738`)の重み付き類似。
  これを `xSum_le_two_psi_caseB` → c2 endgame `false_of_coherentXunionYset_caseB_of_not_coherentS` に積む。
  **scope = multi-session 見込み**(unweighted 版が辿った鎖を重み付きで再構築)。
- **それ以外はすべて wiring(既存 green 補題)**。

## S08:59 discharge の構造 (3-way dispatch)

`hyp.cases : Frobenius ∨ ∃ h46 (c2 conditions)`(`S08_CoherenceCorePart1:3321`)で分岐:

1. **Frobenius 枝 (c1)** — **ほぼ完成**。`nonempty_coherent_S_caseA_of_frobenius`
   (`S08_CoherenceCore:3813`)が完全証明済(IsPGroup は内部導出: bound `CorePart2:3828` +
   `isPGroup_of_isFrobeniusGroup_of_card_le` `CorePart1:3120`)。署名 = `(hyp) [H.Normal] (hF)
   (hHnonab : commutator ↥H ≠ ⊥) {p} (hp) (hp3 : 3≤p) (hHp : IsPGroup p ↥H)`。
   ⟹ S08:59 で wiring するには `hHnonab` と `(p, hp, hp3, hHp)` を供給。
   - `hHnonab` = `commutator ↥H ≠ ⊥`: X-nonempty 枝条件 `hyp.Xset ⁅H,H⁆ ≠ ∅`(abelian 枝は既に処理済)
     から出るはず。要 helper(`Xset ⁅H,H⁆ ≠ ∅ → commutator ↥H ≠ ⊥`)or 既存補題確認。
   - `(p, hp, hp3, hHp)`: `isPGroup_of_isFrobeniusGroup_of_card_le hF …` で `∃ p, IsPGroup p ↥H`、
     `three_le_prime_of_isPGroup_of_odd`(`CorePart1:1330`)で `3≤p`。bound 導出は `CorePart2:3828` を参照。
     ※ `nonempty_coherent_S_caseA_of_card_of_frobenius`(`:3746`)が既に bound+prime を内部で組むので
     そちらを使えば `hHp`/`hp` 供給不要かも(署名要確認)。
2. **c2-math-A 枝** (`center ↥H ⊓ W₂.subgroupOf H = ⊥`) — irreducible-X route。
   `Xset_centralCommutator_isCoherent_of_c2_caseA`(`S08_CoherenceCore:1259`)+
   `isIrreducibleCharacter_of_mem_Xset_c2_caseA`(`CorePart2:1886`)で X-coherence は irreducible。
   ⟹ unweighted endgame `false_of_coherentXunionYset_of_not_coherentS`(`CorePart2:3439`)が
   そのまま効く可能性(Frobenius でなく irreducible-X で counting が通るか要確認)。IsPGroup は
   `isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator`(`CorePart1:3159`)で c2 から取れる。
3. **c2-math-B 枝** (`center ↥H ⊓ W₂.subgroupOf H ≠ ⊥`, = `W₂ ⊆ Z(H)`) — **HARD CORE**。
   X-coherence の member に reducible certain-type column が入る ⟹ weighted (5.6) break が必須。
   - X∪Y coherence seed: `coherentXunionYset_caseB_of_glued`(`S08_CaseBCoherence2:1616`)に在る。
   - weighted counting: `sum_div_normSq_induce_kernelFilter_eq`(`CorePart1:2526`, AxiomsCheck 登録)実在。
   - weighted 下端 engine: `coherentDegreeSqNormBound_of_not_coherentW`(`S08_CoherenceWeighted:475`)実在
     (X-adjoin 形)。
   - **欠落 = 中間の `sMember_degreeSqNormBound_of_not_coherent`**(break pair → 重み付き member family
     列挙、各 reducible member に Dmem 分解 data を供給)→ `xSum_le_two_psi_caseB` → c2 endgame。
   - FPF 算術破綻: `false_of_caseB_break_of_bounds`(`S08_CaseBEndgame:384`)+ `caseB_fpf_bound`(`:338`)実在。
   - dispatch: `eq_bot_or_eq_of_le_of_card_prime`(`CorePart1:3354`)で math-A/B 分岐。

## HARD CORE の解剖 (`sMember_degreeSqNormBound_of_not_coherent`)

unweighted テンプレート `sMember_degreeSumBound_of_not_coherent`(`CorePart2:2650`)の構造:
1. `exists_sMemberOrthonormalFamily`(`hF`)で `S₁` を **irreducible(norm 1)member** `χmem : Fin k →
   IrreducibleCharacter ↥L` として列挙 + 各 member の orthonormality (`⟨χmem i,χmem j⟩ = if i=j then 1 else 0`)。
2. `exists_sMemberDegreeData` で degree ratio、`sBreakPair_fields` で break pair ψ,ψ̄。
3. abstract engine `coherentDegreeSumBound_of_not_coherent` に渡す。

**weighted 版の crux** = case-B では `S₁` に **reducible certain-type column** が混ざる ⟹
- `χmem` は `IrreducibleCharacter ↥L` でなく一般 `ClassFunction ↥L ℂ`、norm `‖χmem j‖² = ⟨χmem j,χmem j⟩` 一般。
- **`exists_sMemberOrthogonalFamilyW`(未実装)** = orthonormal でなく **orthogonal** な enumerator で、
  weighted engine `coherentDegreeSqNormBound_of_not_coherentW`(`S08_CoherenceWeighted:475`)が要求する
  **各 member の `CharacterPsiDecomposition` (Dmem) + orthogonality + 重み付き degree bound** を供給する。
- **genuine new math = reducible member の per-member Dmem 構成**: certain-type column の分解は
  certain-type R(χ) 機構(`certainTypeDecompositionDa`/`certainTypeR`, §4/§5 σ-isometry)から作る。
  irreducible member は既存 `memberExtensionDecomposition`。
- counting 側 = `sum_div_normSq_induce_kernelFilter_eq`(weighted, 実在)で `∑_X χ(1)²/‖χ‖²`。

⟹ `xSum_le_two_psi_caseB`(`xSum_le_two_psi` `CorePart2:3229` の weighted mirror)→ c2 endgame に積まれる。

### ⚡ スコープ縮小 (2026-06-17, 追加 grep): per-member producer は実在 ⟹ hard core = **assembly**

`xChainCoherentW` docstring が挙げる per-member producer は **ほぼ全て実装済**(reducible Dmem を
ゼロから作る必要はない):
- **`certainTypeMemberDecomposition`**(`S06_CertainTypeCoherence:740`)= 「`memberExtensionDecomposition`
  の reducible 版」。coherent set `S₁` の reducible certain-type column に per-member
  `CharacterPsiDecomposition` を供給(`ofProjection (certainTypeR …)` 経由)。
- **`certainTypeR`**(`S06:639`)= R(μ_j) image family / `certainTypeDecompositionDa`(`S08_CaseBCoherence2:1360`)。
- **`certainTypeR_imageSet_orthogonal_dadeOfDiff`**(`S08_CaseBHortho:44`)= `hortho_mem` field。
- **`memberExtensionDecomposition`** = irreducible member 用 Dmem。
- engine `coherentDegreeSqNormBound_of_not_coherentW` の per-member 要求 = `mc`(norm)+ `Dmem` +
  `hortho_mem` + `htau1Dmem` は、上記 producer の **dispatch(reducible/irreducible で分岐)で供給可能**。

⟹ **hard core = weighted enumerator `exists_sMemberOrthogonalFamilyW` の ASSEMBLY**
(`exists_sMemberOrthonormalFamily` `CorePart2:2464` を mirror し、IrreducibleCharacter 制約を外して
per-member で `certainTypeMemberDecomposition` / `memberExtensionDecomposition` を dispatch、weight
`mc i = ⟨χmem i, χmem i⟩.re`、orthogonality は coherent set の member 間直交 + `certainTypeR_…orthogonal`)。
**ゼロからの新証明でなく既存 green producer の結線** ⟹ scope は当初見積より縮小(ただし multi-hundred LOC)。

### 次の coding action — 精密設計 (2026-06-17 確定, coding-ready)

**brick 1 (committable green, 最初に書く): per-member Dmem dispatcher `caseB_member_psiDecomposition`**
入力 = case-B coherent `hS₁coh : IsCoherent hyp.tau S₁ A`(A = supportInSubgroup (sharpImage H) L)、
`x ∈ S₁`、`x.conj ∈ S₁`、`hνZ : hS₁coh.extension x ∈ ZIrr G`。出力 = `CharacterPsiDecomposition hyp.tau x 0`。
本体 = `caseB_S_member_column_or_irreducible hyp h46 hHK (hS₁sub hxS₁)`(`S08_CaseBAssembly:1949`)で分岐:
- **column 枝** (`∃ χ₂≠1, columnSum h46 χ₂ = x`): `certainTypeMemberDecomposition h46 hχ₂ hdeg hagree hS₁coh
  hμ_S1 hμbar_S1 hνZ hdiffsupported`(`S06_CertainTypeCoherence:740`)。
  - `hdeg`(column 次数等式)= 既存 `columnDecompositionTau` 系の caller が供給する形(`S08_CaseBCoherence2:1757`
    と同型)。`hagree`/`hmapagree`(μ_j−μ̄_j 上で hyp.tau = certain-type Dade map)= `columnRFamilyTau`
    (`S08_CaseBCoherence2:1791`)が使う `hmapagree` と同源(H^#-supported + c2 K=H で両 map 一致)。
  - 必要 instance: `[NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible …] [Fintype (S06.ticVdiff h46).W] [Invertible …]`。
- **irreducible 枝** (`IsIrreducibleCharacter x`): `memberExtensionDecomposition hyp.dade hyp.hconj hS₁coh
  ⟨x,hirr⟩ hreal hdiffsupp hx_S1 hxbar_S1 hνZ hχχbar`(`S08_CoherenceCorePart1:1585`)。
  - ⚠ `hyp.tau = dadeIntegralCharacterMap hyp.dade (hyp.dade.fullDadeIsometryData hyp.hconj)`(`CorePart2:31`)
    なので memberExtensionDecomposition の τ と一致(defeq 確認要)。
  - `hreal`/`hdiffsupp`/`hχχbar` = case-B 用の member-fact から(Frobenius 専用の `sMember_characterFacts`/
    `sMember_diffSupport hF` は使えない ⟹ case-B 版 member-fact を特定 or 導出する小補題が要る。これが
    irreducible 枝の唯一の未確認点)。

**brick 2: weighted enumerator `exists_sMemberOrthogonalFamilyW`** = `exists_sMemberOrthonormalFamily`
(`CorePart2:2464`)を template に、`χmem : Fin k → ClassFunction ↥L ℂ`(IrreducibleCharacter 制約を外す)、
`mc i := (ClassFunction.inner (χmem i) (χmem i)).re`、`Dmem` = brick 1、`hortho_mem` =
`certainTypeR_imageSet_orthogonal_dadeOfDiff`(`S08_CaseBHortho:44`, column)+ irreducible 版、
`htau1Dmem` = rfl(両 producer とも tau1 = hS₁.extension)、member 間 orthogonality は coherent set の直交。

**brick 3-4**: `xSum_le_two_psi_caseB`(brick 2 + counting `sum_div_normSq_induce_kernelFilter_eq`)→
c2 endgame `false_of_coherentXunionYset_caseB_of_not_coherentS` → S08:59 の 3-way dispatch。

✅ 全部品 verified(未確認点ゼロ): brick 1 irreducible 枝の case-B member-fact は
`xMember_diffSupport_of_irreducible_X`(`S08_CoherenceCore:513`, Frobenius 非依存)+ 次数ベース
support(`sMember_diffSupport_of_charValue_eq`)で供給。`hreal` は irreducible X-member の非実性
(case-B X は奇位数ゆえ非実、既存の X-member fact)。column 枝・instance・classification・engine 側も確認済。
⟹ brick 1 から純粋に coding(新数学なし、既存 green producer の結線)。

## (6.5) p-group reduction — 完備 (Plan agent の「未形式化」は誤り)

- c1: `isPGroup_of_isFrobeniusGroup_of_card_le`(`CorePart1:3120`)
- c2: `isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator`(`CorePart1:3159`) ← c2 の
  fixed-point 条件(`C_H(x)=W₂ ⊆ ⁅H,H⁆`)+ coprime + bound から `∃ p, IsPGroup p H`。
- core: `isPGroup_of_isNilpotent_of_isFrobeniusAction_abelianization`(`:3097`)/
  `isPGroup_of_card_le_of_isFrobeniusAction`(`:2997`)。
- 唯一の入力 = bound `|Abelianization H| ≤ 4|W|²+1`(=(6.2)/(6.3),
  `theta_degree_le_index_mul_sqrt_index` `CorePart1:557`; Frobenius 版導出 `CorePart2:3828`)。

## 推奨着手順

1. **(green helper) Frobenius 枝の wiring 部品**: `hHnonab` from X-nonempty + Frobenius discharge を
   呼べる形にする(`nonempty_coherent_S_caseA_of_card_of_frobenius` の署名次第で hHp 供給要否確定)。
2. **(HARD CORE) `sMember_degreeSqNormBound_of_not_coherent`**: unweighted `sMember_degreeSqReBound_of_not_coherent`
   (`CorePart2:2738`)の証明を読み、weighted 鎖
   (`coherentDegreeSumBound` → `sMember_degreeSumBound` → `sMember_degreeSqReBound` の重み付き類似、
   下端は既存 `coherentDegreeSqNormBound_of_not_coherentW`)を構築。reducible member の Dmem は
   `certainTypeDecompositionDa`/`certainTypeR`(certain-type 分解)から、irreducible は
   `memberExtensionDecomposition` から供給。
3. `xSum_le_two_psi_caseB`(`xSum_le_two_psi` `CorePart2:3229` の weighted mirror; counting を
   `sum_div_normSq_induce_kernelFilter_eq` に差替)。
4. c2 endgame `false_of_coherentXunionYset_caseB_of_not_coherentS`(`false_of_coherentXunionYset_of_not_coherentS`
   `CorePart2:3439` の weighted+FPF mirror)。
5. S08:59 で 3-way dispatch を組み `.some` で `CoherenceTarget` 化。

## 再調査不要 (本セッション確定)

- 14 部品在庫は実在 sorry-free(gap_resolution §1)。weighted counting / weighted 下端 engine / (6.5)
  両ケース / Frobenius discharge / c2 X∪Y coherence / FPF break はすべて実在。
- 真 hard core = `sMember_degreeSqNormBound_of_not_coherent` 1 本(+ それを積む endgame)。
- (6.8) は今 FT carrier から orphaned(deferred-payoff prerequisite)= 記憶 [[ft-path-policy]]。
