# Pf (6.8) case-B resume roadmap — 正本 (2026-06-17, 2 workflow + Plan agent + 直接 grep で code-verified)

> この note が **S08:59 `sibleySetup_is_coherent` を閉じるための現行 source-of-truth**。churn した
> `s08_6_8_assembly_plan.md`(458KB)/`s08_6_8_3_gap_resolution.md` のうち本 note と矛盾する記述は本 note を優先。
> 上位方針・FT 接続の文脈 = 記憶 [[ft-path-policy]] の 2026-06-17 検証訂正ブロック。

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

⟹ **scope = sustained build**(weighted enumerator + reducible Dmem 構成が本体)。これが
`xSum_le_two_psi_caseB`(`xSum_le_two_psi` `CorePart2:3229` の weighted mirror)→ c2 endgame に積まれる。

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
