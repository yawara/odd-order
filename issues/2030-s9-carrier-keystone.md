---
id: 2030
slug: s9-carrier-keystone
title: "Pf §9 Clifford counts (9.8)-(9.10) + Section11CharacterData redesign — W3 keystone"
created: 2026-06-27
---

# Pf §9 Clifford counts + `Section11CharacterData` redesign — the W3 keystone

> lane-b (W3) *(現 owner = lane a — 2026-07-02 3 レーン再編、Pf S03–S13 は lane a。正本 `notes/meta/ft_lane_reallocation_2026_06_28.md`)*. This is the **single deep keystone** the entire W3 frontier converges on: both
> on-path obligations — (10.8)`no_typeV` (via (10.7)) and **(11.8)** (the bare `feitThompson` sorry
> residual `card_kappaHall_lt_of_isTypeIIIorIV`) — bottom out here.

## 背景: W3 が単一 keystone に de-risk された (2026-06-27)

本セッションで **(10.8) の機械的・算術 spine 全体**を実証明 (§7 入力 + line 81→83 + line-87 算術 +
ℚ chain + closer; issue 2020 / `notes/peterfalvi/s12_10_8_noncoherence.md`)。(10.8)・(11.8) の残りは
正確に §9 Clifford 指標理論のみ。

## architectural finding (精密)

`S11.Section11CharacterData data chief` (`S11_MaximalII_III_IV.lean:1479`) は **scaffold-by-design**:
- subgroup/numeric field は constrained: `C ≤ U`, `Uprime ≤ U`, `Cprime ≤ C`, `u_eq_card_quotient`。
- **character field は全て FREE** (property field 無し): `X`, `S`, `XOf`, `SOf`, `H0CprimeSupport`,
  `tau`, および `Prop` の `quotientSemidirectFrobenius`。

ゆえに §9 指標カウント定理は**全て `sorry`** で、現 carrier に対しては genuine に証明不可
(free な `chars.SOf`/`chars.S` 等に量化しているため):
- (9.8) `caseA_character_counts` — `sorry` (S11:2505)
- (9.9) `caseB_character_counts` — `sorry` (S11:2516)
- (9.10) `exceptional_case_frobenius_realization` — `sorry` (S11:2532)
- (9.11) `coherent_H0C_commutator` — (6.8) に wired (witness `sibleyTarget_H0C` が `sorry`, §14-gated)

## なぜ両 W3 obligation を塞ぐか

- **(10.8) `hB` / (10.7) `typeII_derived_frobenius`**: Pf (10.7) 証明 (04.12 line 71) は partner の
  chief factor に (9.10)/(9.8.b)/(9.9.b) を cite。`[S,S]=H⋊U` Frobenius (ゆえ `|U|≥7`,
  `|S|=|H||U|w₂`, TI-counting `hB` の `G₁ ⊆ (H#)^G ∪ V^G`) がこれを要する。
- **(11.8) `exists_zeta_residual_not_orthogonal`**: `S(HC)=S₁` の materialize (定数次数 w₁ の
  `(u−1)/q` 既約、`(U/C)⋊W₁` Frobenius) + (9.8)/(9.9)/(9.11) を要する
  (`notes/peterfalvi/s13_11_8_orthogonality.md`)。
- **(7.8.b)** ((10.8) 最後の §7 gate、`Hypothesis78` for `(M,A(M))`, `H=M'`): その *family* `T` 列挙
  (`Hypothesis76.zeta : Fin (n+1) → …` の degree-ratio 構造) 自体が同じ §9 chief-factor Clifford
  構造に支配される。

## 2026-06-27 lane-b (W3): task A の character-family 部分 COMPLETE (commit `9c41978a`)

**`Section11CharacterData` の character field を genuine 化** (full build 3884 green)。issue 冒頭の
「character field は全て FREE → §9 counts は genuine に証明不可」を直接解消した:

- **genuine families 新規** (S11, all sorry-free, `S12.inducedFamily` パターン):
  `huSub` (HU=H⊔U を ↥M 内に realise) / `hInHu` (H の HU 内表現) / `xiSet` (𝒳={χ∈Irr(HU)|H⊄Ker χ}) /
  `xiOf` (𝒳(Y)={χ∈𝒳|Y⊆Ker χ}) / `induceHU` (Ind_{HU}^M, canonical Invertible bake-in で desync 回避) /
  `induceHU_apply_one` (degree [M:HU]·χ(1)) / `sSet` (𝒮=Ind 𝒳) / `sOf` (𝒮(Y)=Ind 𝒳(Y))。
  基礎 API: `xiOf_subset_xiSet`/`mem_xiOf`/`xiOf_antitone`/`mem_sSet`/`mem_sOf`/`sOf_subset_sSet`/`sOf_antitone`。
- **carrier 再設計**: free な `X`/`S`/`XOf`/`SOf` field を削除 → genuine namespace defs
  (`X=xiSet`,`XOf=xiOf`,`S=sSet`,`SOf=sOf`) + `X_eq`/`XOf_eq`/`S_eq`/`SOf_eq` (rfl simp)。
  ⟹ (9.8)/(9.9)/(9.10) と (9.11) coherence consumer は Peterfalvi の **honest families** を参照
  (以前は free field ゆえ原理的に証明不能)。consumer (S12 `typeII_section11_coherence`,
  `sibleyTarget_H0C`) は `chars.S`/`tau`/`H0CprimeSupport` のみ使用で signature 不変、producer 不在ゆえ
  field 削除も安全。

**残 task A (carrier の部分群)**: `C=C_U(H̄)` (= U-action map `(quotientMulAutHom chief.N_aInvariant).comp
(U.subgroupOf(U⊔W1)).subtype` の `MonoidHom.ker` を G の部分群へ map-down、`u_eq_card_quotient` の range
と双対) / `Uprime=[U,U]=derivedInG U` / `Cprime=[C,C]=derivedInG C` を free field → genuine def 化。
counts が `chars.C`/`chars.Uprime`/`chars.Cprime` に量化するため、これらを pin しないと (9.8)/(9.9) は
genuine families に対しても未証明。pinning 自体は count を unlock しない (count は下記 B/C の deep Clifford)
が、count 証明の prerequisite。**fiddly だが honest-architecture prerequisite、次 brick**。

## 2026-06-27 lane-b (cont.): task A 完了 (subgroups genuine 化) + 文字基盤 (commits `153e866a`+本)

- **subgroup genuine 化** (commit `153e866a`): carrier の free な `C`/`Uprime`/`Cprime` (+ `_le_`) を
  削除し genuine def へ: `uActionHom` (U の H̄ 作用 hom) / `cSub` = C_U(H̄) = uActionHom の kernel を G へ
  map-down (`cSub_le_U`、first iso で |U:C|=u) / `uprimeSub`=derivedInG U / `cprimeSub`=derivedInG C +
  le 定理。⟹ **task A (carrier 再設計) 完了** = families + subgroups 全 genuine。
- **文字基盤** (本 commit): `induceHU_mem_ZIrr` (𝒮-member ∈ ℤ[Irr M]) + `sSet_subset_ZIrr` — counts が
  𝒮 を character として扱う foundation (`ClassFunction.induce_mem_ZIrr` cite)。
- **count 用 infra を特定**: Clifford inertia-induction が `InducedIrreducible.lean` に実在 =
  `isIrreducibleCharacter_induce_of_inertia_eq` (inertia=H ⟹ Ind irreducible) /
  `induce_eq_induce_iff_conj` (Ind 一致 ⟺ 共役) / `card_filter_induce_eq_index_inertia` /
  `sum_div_normSq_induce_image_eq`。§4 Dade は `S06_CertainType*` に (4.3)-(4.9) 実在。

## 2026-06-27 lane-b (cont.²): genuinization が露呈した count 文の imprecision (重要)

carrier を genuine 化したことで、free-field 時代に **vacuous だった (9.8)/(9.9)/(9.10) の文**が実内容を
持ち、Peterfalvi に対する **imprecision** が露呈した (build は green = `sorry` body ゆえ; ただし文が
不正確だと proof 不能)。count 証明前に Peterfalvi (`04.11`) に対し**文の再導出**が必要:

- **(9.9) conjunct 2** `∃ χ ∈ SOf Cprime, χ 1 = u` ⚠: SOf=𝒮 は induced family ゆえ member の degree は
  `[M:HU]·(source) = q·u = qu`((9.8.c) と同じ、(9.10) の "degree qu" とも整合)。Peterfalvi (9.9.a)
  「χ(1)=u」は **𝒳(H₀C')**-member (HU 文字) の degree であり、𝒮-member ではない。⟹ **`u` → `data.q*u`
  (qu)** に修正、または XOf(𝒳) を参照すべき ((9.8) は両所 qu で consistent)。
- **(9.10) hypothesis** `¬∃ χ ∈ SOf C, χ 1 = qu` ⚠: Peterfalvi (9.10) は **𝒮(H₀C')** (=Cprime) で記述。
  Lean は `SOf chars.C` (=C)。⟹ C/Cprime 要確認。
- **(9.8.c)/(9.8.d)/(9.9) の `SOf` 引数が H₀ join を省略** ⚠ (systematic): Peterfalvi は 𝒮(H₀C)/
  𝒮(H₀U')/𝒮(H₀C') (H₀ との join) を使うが、Lean は `SOf chars.C`/`SOf chars.Uprime`/`SOf chars.Cprime`
  (C/U'/C' 単独)。`sOf data Y` = {χ | Y⊆Ker} ゆえ H₀⊆Ker を要求しない → 別物。⟹ `SOf (chief.H0 ⊔ chars.C)`
  等に修正すべき (`chief.H0`/`chars.C` は共に `Subgroup G` ゆえ `⊔` 可)。((9.8.b) の `SOf chief.H0` は
  H₀ 単独で正しい。)
- 一般に SOf(𝒮, degree q·src) と XOf(𝒳, degree src) の使い分け・H₀ join・C/Cprime 引数を Peterfalvi
  (9.5)-(9.10) に対し総点検すること。これは genuine carrier 化の正の副産物 (scaffold 時代は検出不能)。
  **A' は count 証明 (B/C) の前提**: 文が正確になって初めて Clifford/Dade 証明が意味を持つ。

## やること (research-grade, multi-session)

- [x] **A': count 文監査 COMPLETE** (2026-06-28, commit `c170dd32`) — (9.8)/(9.9)/(9.10) を Peterfalvi
      忠実化 (H₀-join / C/C' / `IsIrreducibleCharacter` / 3 vacuity trap 除去)。下記「2026-06-28」節。
- [x] **A**: carrier 再設計 = families (commit `9c41978a`) + subgroups (commit `153e866a`) 全 genuine。
      残 free field = u (pin 済) / tau・H0CprimeSupport (S12-Dade layer) / quotientSemidirectFrobenius
      ((9.10) output) / CliffordCaseBData.field_model・Ubar_cyclic (下記、struct instance plumbing で True 据置)。
- [x] **B: case-(b) (9.9) COMPLETE** (2026-07-06 検証、下記「2026-07-06 lane-a (β)」節): `caseB_character_counts`
      (S11:9838) は **全 4 conjunct sorry-free** (旧「Clifford 次数が次の大ピース」は stale)。(9.10) は type-II
      HU-Frobenius clause のみ 1 sorry 残 (S11:9893、H₀=1 gated via (11.7)←(10.8))。詳細は末尾 β 節。
- [x] ~~**B (旧記述、達成済)**: case-(b) (9.9)/(9.10)~~ — Singer field model。**✅✅ (9.9.a) inertia `I_U(θ)⊆C` 完全 proven**
      (2026-06-28 cont.⁴⁻⁶、全 axiom-clean): `chiefFactor_caseB_action_fpf` (FPF) →
      `chiefFactor_caseB_char_inertia` (抽象 char inertia) → `compHom_typeP_conjAction_inflation` +
      `caseB_char_inertia_inflation` (inflation 還元) → `hInHuEquivH`/`conjBy_compHom_hInHuEquivH` (realization)
      → `caseB_inertia_realized` (capstone: concrete g∈I_{HU}(θ) ⟹ φU=1)。**残 = Clifford 次数のみ**:
      χ∈Irr(HU) の Res_H から realized-inflation 形 constituent θ 取り出し + 誘導次数 χ(1)=u (general Clifford
      correspondence、inertia=HC from 誘導、新規構築要)。+ `|𝒮(H₀)| reducible-count = p−1` = (4.5)/(4.7) Dade、
      (9.9.c) 例外含意。
- [ ] **C: case-(a) (9.8)** — (9.8.b,c) = (8.4.d)+(4.5)/(4.7) Dade for L=M/H₀ + θ=θ₁…θ_q1_C 構成;
      (9.8.d) = degree-qa 構成 + inertia counting (`card_filter_induce_eq_index_inertia`)。
      case-(a) factor 構造 (`CliffordCaseAData.Hpart`/`a`) を使う。
- [ ] **D: (9.11) `sibleyTarget_H0C`** 構造 witness (現状 (6.8)/Sibley 経由で §14-gated)。

## 2026-06-28 lane-b (W3): A' count 文監査 COMPLETE + B 構造核 (FPF) landed

**A' 完了** (commit `c170dd32`、full build 3884 green): carrier genuine 化で露呈した (9.8)/(9.9)/(9.10) の
imprecision を Peterfalvi (04.11) に対し総点検・修正。**consumer 0 ゆえ statement 改変は安全** (grep 確認)。
- **H₀-join (systematic)**: `𝒮(H₀C)`/`𝒮(H₀U')`/`𝒮(H₀C')` を `chars.SOf (chief.H0 ⊔ ·)` に修正。
- **C/C'**: (9.10) hypothesis を `C`→`Cprime` (Pf は 𝒮(H₀C') 記述)、(9.9.c) も C' 統一。
- **`IsIrreducibleCharacter`**: 「irreducible」「contains an irreducible」箇所に導入 (9.8.c/9.8.d/9.9.c/9.10)。
- **vacuity trap 除去**: (9.9) 恒真 `u∣qu` → genuine (9.9.a)「∀φ∈𝒮(H₀C'), φ(1)=qu」(定数次数=(5.7) 入力);
  偽 `(𝒮(H₀)).ncard=p−1` → `{φ∈𝒮(H₀)|¬irred}.ncard=p−1` (reducible-count); 恒偽傾向 `ncard=0` trigger →
  「contains no irreducible」(exceptional case で 𝒮(H₀C')=𝒮(H₀)≠∅)。

**B 構造核 = FPF (Frobenius `H̄⋊Ū`) landed** (本 commit、両 axiom-clean+AxiomsCheck 登録):
- **`fixedPointFree_of_aInvariant_irreducible_comm`** (一般、S11): A が K に φ:A→*MulAut K で作用し
  **像可換** (`Commute (φ a)(φ b)`) + irreducible (A-invariant は ⊥/⊤) なら φa≠1 ⟹ FPF (φa x=x→x=1)。
  証明 = Fix(φa) は A-invariant 部分群 (φa,φb 可換) ⟹ ⊥/⊤、⊤ なら φa=1。**Singer field model 不要・純群論**。
  像可換が仮説ゆえ U 非可換でも適用可 (Ū=U/C は可換)。
- **`chiefFactor_caseB_action_fpf`** (case-(b) 系、S11): case-(b) (hcaseB irreducible) で φU g≠1 (g∉C) ⟹
  H̄ 上 FPF。`hComm` (像可換、`chiefFactor_caseB_image_cyclic` と同じ `⁅a,b⁆∈[U,U]⊆C(H)`) + hcaseB を
  一般補題に渡す。これが (9.9) の degree-u Clifford 解析 (I(θ)∩U=C) の構造的入力。

**character-side FPF engine landed** (commit `4efc27ae` の次 commit、axiom-clean+AxiomsCheck 登録):
- **`eq_one_of_invariant_of_fixedPointFree`** (S11): FPF automorphism α (mathlib `MonoidHom.FixedPointFree`)
  が有限 abelian K に作用するとき、α-invariant な character θ:K→*M' (`∀x, θ(αx)=θx`) は trivial。
  証明 = displacement `x↦x/αx` が surjective (mathlib `commutatorMap_surjective`) ⟹ θ は im=K 上で
  消える。**これが inertia I_U(θ)=C の character-side 核**: nontrivial θ∈Irr(H̄) と g∉C で φU(g) FPF
  (`chiefFactor_caseB_action_fpf`) ⟹ θ は φU(g)-invariant でない ⟹ g∉I_U(θ) ⟹ I_U(θ)⊆C。
## 2026-06-28 (cont.): (9.9.a) inertia path 完全 mapping — **全 infra 存在を確認** (de-risked)

(9.9.a) の inertia `I_U(θ)=C` を repo infra で組む経路を完全に特定。**全部品が既存**と確認 (新規証明 0):
- **abelian fixed-class bridge = 既存** `ConjugationBrauer.card_fixedPoints_conjClassPerm_eq_one_of_commute_of_centralizer_inf_eq_bot`
  (H̄ abelian `hcomm` + `C_G({g})⊓H̄=⊥` `hbot` ⟹ `#fixedClasses=1`)。**コメントが「(6.8)(c2) replacement for
  the full Frobenius condition、abelian 商 H̄ 用」と明記** = まさに (9.9) 用に作られている。
- **inertia 除外 = 既存** `not_mem_inertia_of_ne_trivial_of_card_fixedClasses_eq_one` (#fixedClasses=1 +
  nontrivial θ̄ ⟹ g∉inertia(θ̄))。
- **商 inflation 移送 = 既存** `mem_inertia_compHom_iff` (θ=θ̄∘q の inertia in G ⟺ mk' M g の inertia in G/M)。
- **Clifford 誘導次数 = 既存** `InducedIrreducible.isIrreducibleCharacter_induce_of_inertia_eq` /
  `card_filter_induce_eq_index_inertia` (Ind from inertia irreducible、degree=index)。

**∴ 残 (9.9.a) = 純 assembly (新 math 0、intricate な realization)**: (1) G'=HU/H₀ 実現 (H̄=H/H₀⊴G'、
q:H→*H̄)、(2) **`hbot` を FPF から**: u∉C で `C_{HU/H₀}({mk' u})⊓H̄=⊥` ⟺ φU(u) FPF (mk' h∈C(mk' u) ⟺
φU(u)(h̄)=h̄、`chiefFactor_caseB_action_fpf` で =1) — φU を HU/H₀ の conjugation に同定する realization が核、
(3) bridge→not_mem_inertia→mem_inertia_compHom_iff で I(θ)∩U=C、(4) χ=Ind_{HC}^{HU}(θλ) degree u → Ind^M qu。
これは multi-session の **assembly** (各 step は既存補題、繋ぎが realization-heavy)。

## 2026-06-28 (cont.²): §9 degree infrastructure landed (上記 (4) の足回り)

assembly step (4) の degree 計算の足回りを実証明 (axiom-clean+AxiomsCheck 登録、full build green):
- **`huSub_index_eq_q`**: `[M:HU] = q` = `|W₁|`。`HU = H⊔U = M' = derivedInG M` (型P 相補性
  `derivedInG_eq_fitting_sup_U`+`H_eq`) + `[M:M']=|W₁|` (`M_complement.index_eq_card`)。
- **`induceHU_apply_one_eq_q_mul`**: `(Ind_{HU}^M χ)(1) = q·χ(1)` (`induceHU_apply_one` の index を q に解決)。

⟹ **全 §9 count の degree 文 (μ_j(1)=qu、(9.8.c) qu、(9.8.d) qa、(9.9.a) qu) が `φ∈𝒮(Y) ⟹ φ(1)=q·χ(1)`
で `χ(1)=u`/`a` (Clifford 部) に reduce 可能**。(9.9.a) なら `induceHU_apply_one_eq_q_mul` で
`φ(1)=qu ⟺ χ(1)=u` に縮小 (χ(1)=u は inertia/Clifford = 残 assembly)。degree 側は完全に塞いだ。

**route 訂正 (honest)**: 上記 (2) の `hbot` 経路 (centralizer-inf-bot) が repo の inertia API と直結で、
本セッションの `eq_one_of_invariant_of_fixedPointFree` (char-as-Hom engine) は **不要**になる見込み
(後者は Irr(H̄)↔Hom(H̄,ℂˣ) bridge を要し遠回り; centralizer route は bridge 不要)。`eq_one_of_invariant_of_fixedPointFree`
は valid な汎用 lemma として残すが (9.9) critical path 上では centralizer route を使う。**FPF 構造核
`chiefFactor_caseB_action_fpf` は (2) `hbot` に必須**ゆえ critical path 上。

- **残 (9.9.a) = inertia API wiring + Clifford degree** (上記 de-risked plan で実行可能): engine
  (FPF) → centralizer-inf-bot `hbot` → `card_fixedPoints_...` → `not_mem_inertia_...` →
  `mem_inertia_compHom_iff` → I(θ)∩U=C → (1.7.a) χ=Ind_{HC}^{HU}(θλ) degree u → Ind_{HU}^M degree qu。

## 2026-06-28 (cont.³): abelian Irr↔Hom bridge landed — char-engine route が realization-free に

**`exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative`** (S11、axiom-clean+AxiomsCheck):
有限 abelian Γ の irreducible character (`IsIrreducibleCharacter`) は linear character `θ:Γ→*ℂˣ`
(`(θ g:ℂ)=φ g`)。証明 = 既約表現が 1 次元 (`finrank_eq_one_of_isMulCommutative`) ⟹ 各 ρg は scalar
`θ g` (`exists_smul_eq_of_finrank_eq_one`) ⟹ `φ g = trace(ρ g) = θ g`。

**route 再訂正 (cont. の訂正を更新)**: cont. で「char-engine は不要・遠回り」としたが、本 bridge で
**Irr(H̄)↔Hom bridge を実装したので char-engine route が viable かつ realization-free に**。
- char-engine route: θ̄∈Irr(H̄) を bridge で Hom 化 → `eq_one_of_invariant_of_fixedPointFree` (FPF φU(u) +
  invariant ⟹ trivial) で「nontrivial θ̄ は φU(u)-invariant でない」。**H̄ を subgroup に realize せず、抽象
  quotient ↥data.H⧸chief.N + 抽象 φU のまま**動く (conjByPerm/centralizer-inf-bot の realize 不要)。
- ⟹ 2 route が並立: (A) centralizer-inf-bot (conjByPerm、要 H̄-as-subgroup realize) / (B) char-engine+bridge
  (realization-free)。**(B) が realize plumbing を避けるぶん有利見込み**。
- **両 route 共通の残接続** = 「u∈I(θ) (ClassFunction.conjBy in HU) ⟺ θ̄∘φU(u)=θ̄ (inflation)」= θ が H̄
  経由 (H₀⊆ker) であることの conjBy↔φU 接続。これ + Clifford degree (Ind from inertia) が残 assembly。

⟹ **char-engine (commit 25ee31ba) は off-path でなく on-path に昇格** (bridge で接続)。FPF 核も degree infra も
on-path。残 = inflation 接続 (conjBy↔φU) + Clifford 誘導次数。

## 2026-06-28 (cont.⁴): char-side inertia `I_U(θ) ⊆ C` を実証明 (realization-free) — 核心 landed

**`chiefFactor_caseB_char_inertia`** (S11、axiom-clean+AxiomsCheck): case-(b) で θ∈Irr(H̄) nontrivial が
φU(g)-invariant (`∀x, θ(φU(g)x)=θ x`) ⟹ **φU(g)=1** (= g∈C)。= Peterfalvi (9.9.a) の character-side
inertia `I_U(θ)⊆C`。全 engine 統合 (背理法 φU(g)≠1 → FPF `chiefFactor_caseB_action_fpf` → bridge で θ を
Hom 化 → char-engine `eq_one_of_invariant_of_fixedPointFree` で θ trivial → nontrivial に矛盾)。
**抽象 quotient ↥data.H⧸chief.N + 抽象 φU のまま、H̄-as-subgroup realize 完全不要**。char-engine を
`[CommGroup K]`→`[Group K]` に緩和 (商の CommGroup instance 構成を回避、証明は abelian 不要だった)。

⟹ **(9.9.a) の inertia 核 (I_U(θ)⊆C) は完全に proven**。残 (9.9.a) = (i) (9.9) の χ∈Irr(HU) の Res_H
component θ が H̄ 経由 (nontrivial) であることの取り出し + 「u∈I_HU(θ) ⟺ θ̄ φU(u)-invariant」の inflation
接続 (この char_inertia が後者の右辺を閉じる)、(ii) Clifford 誘導次数 χ=Ind_{HC}^{HU}(linear) degree u →
Ind^M qu (degree infra 済)。**inertia の数学核は終わり、残は Clifford 取り出し/誘導の formalization**。

**carrier genuinization の保留** (honest-architecture note): `CliffordCaseBData.field_model`/`Ubar_cyclic`
(True placeholder) を FPF/IsCyclic に genuine 化しようとしたが、**struct field type が
`typeP_quotientCoprimeAction` を参照 → `[Finite G]` + `[chief.N.Normal]` instance を要し、structure 宣言
コンテキストで供給不能** (haveI 不可)。⟹ True 据置、FPF は standalone lemma で供給。B の (9.9) 証明では
`caseB_character_counts` に hcaseB を追加引数する (or clifford_dichotomy 経由) ことで `chiefFactor_caseB_action_fpf`
を cite して FPF を得る (struct plumbing を避ける pragmatic な access pattern)。

## 2026-06-28 (cont.⁵): abstract inertia reduction landed — (9.9.a) inertia が単一 step に縮小 (commit `599c9dad`)

cont.⁴ の inertia 核 `chiefFactor_caseB_char_inertia` (abstract: θ̄ φU(g)-invariant ⟹ φU(g)=1) を、
concrete な χ∈Irr(HU) の inertia 解析へ繋ぐ抽象側の bridge を 2 補題で締めた (両 sorry-free +
axiom-clean + AxiomsCheck 登録、full build 3884 green):

- **`compHom_typeP_conjAction_inflation`** (Lemma A、純代数、証明 `rfl`): 膨張
  `compHom (mk' N) : ClassFunction(↥H/N) → ClassFunction ↥H` が共役作用 `typeP_conjAction a` (↥H 上) と
  降下作用 `quotientMulAutHom a` (chief factor ↥H/N 上) を **intertwine** する
  (`compHom (typeP_conjAction a) (compHom (mk' N) θ̄) = compHom (mk' N) (compHom (quotientMulAutHom a) θ̄)`)。
  `quotientMulAutHom_apply_mk'` (`mk' N (a·h) = a·(mk' N h)`、rfl) が核。
- **`caseB_char_inertia_inflation`** (Lemma B): case-(b) で nontrivial irreducible θ̄ の膨張が
  `typeP_conjAction ((act.U.subtype) g)`-invariant ⟹ **φU(g)=1** (g∈C)。Lemma A で invariance を
  `compHom (mk' N) (φU(g)·θ̄) = compHom (mk' N) θ̄` に書換 → `compHom_injective_of_surjective` (mk' N 全射) で
  θ̄ が φU(g)-invariant → `chiefFactor_caseB_char_inertia` で φU(g)=1。

**∴ (9.9.a) の character-side inertia `I_U(θ)⊆C` は単一の残 step に縮小**: concrete HU-conjugation inertia
(`ClassFunction.conjBy in HU` 上、χ∈Irr(HU) の Res_H constituent θ の inertia) から Lemma B の入力
(`typeP_conjAction`-invariance of the inflation) を生む **conjBy↔typeP_conjAction realization**
(= H-in-HU `(H.subgroupOf M).subgroupOf HU` ≅ ↥data.H の同定 + conjBy(u:HU) = typeP_conjAction(u) の照合)。
S08 `inertia_eq_H_of_c2` が (6.8)(c2) で同型の realization を `mem_inertia_compHom_iff` 経由で実装済 = template。

**残 (9.9.a)** = (i) conjBy↔typeP_conjAction realization (上記、唯一の plumbing 残)、(ii) χ∈Irr(HU) の
Res_H から nontrivial constituent θ (H₀⊆ker) を取り出す + Clifford 誘導次数 χ=Ind_{HC}^{HU}(linear) degree u →
Ind^M qu (degree infra `induceHU_apply_one_eq_q_mul` 済)。**inertia 数学核は完了、残は realization + Clifford 取り出し**。

## 2026-06-28 (cont.⁶): (9.9.a) realization + capstone — inertia 部分が完全に proven (commits `260b4926`+`d55be36f`)

cont.⁵ で「唯一の残 plumbing」とした conjBy↔typeP_conjAction realization を締め、inertia 全 chain を完結
(全 sorry-free + axiom-clean + AxiomsCheck 登録、full build 3884 green):

- **`hInHu_normal`** (instance): H ⊴ HU (`maxNilpotentNormalHall_subgroupOf_normal` + `Normal.subgroupOf`)。conjBy に必須。
- **`hInHuEquivH`** (def): realization iso `↥(hInHu) ≃* ↥H` = 2 つの `subgroupOfEquivOfLe` 合成 (H.subgroupOf M ≤ HU, H ≤ M)。
- **`hInHuEquivH_coe`** (rfl): iso は underlying G-元を保存。
- **`conjBy_compHom_hInHuEquivH`** (realization 核): iso の下で concrete `conjBy g` (g∈HU) ↔ abstract
  `typeP_conjAction a` (a∈UW₁, ↑g=↑a)。両者とも同じ G-元共役ゆえ `g·h·g⁻¹=a·h·a⁻¹` に帰着。
- **`caseB_inertia_realized`** (capstone): case-(b) で g∈HU (↑g=↑a, a∈U) が nontrivial θ̄∈Irr(H̄) の
  realized inflation `compHom (hInHuEquivH) (compHom (mk' N) θ̄)` を固定 ⟹ φU(a)=1 (a∈C)。
  = **Peterfalvi (9.9.a) の character-side inertia `I_U(θ)⊆C`、完全に concrete & axiom-clean**。
  証明 = realization で conjBy→typeP_conjAction-inv → inflation injectivity (hInHuEquivH surjective) で
  compHom 剥がし → `caseB_char_inertia_inflation` で φU=1。

**∴ (9.9.a) の inertia `I_U(θ)⊆C` は完全に proven** (FPF → 抽象 char inertia → inflation 還元 → realization
→ capstone の全 chain が axiom-clean)。

**残 (9.9.a) = Clifford 次数のみ** (inertia 終了): χ∈Irr(HU) の Res_H から `caseB_inertia_realized` が要求する
realized-inflation 形の nontrivial constituent θ (H₀⊆ker θ) を取り出す (`exists_liesOver` + θ̄ への factoring) +
**Clifford 誘導次数** χ=Ind_{HC}^{HU}(ψ), χ(1)=[HU:HC]·ψ(1)=u·1=u → Ind^M で qu。これは **general Clifford
correspondence** (inertia=HC からの誘導 + ψ linear extension) を要し、repo は `isIrreducibleCharacter_induce_of_inertia_eq`
(inertia=H 特殊形) のみ所持 = 一般形 (誘導 from 一般 inertia + degree formula + extension) は新規構築要。次の大ピース。

## 2026-06-29 lane a (α): (9.9.a) 第1文 COMPLETE — `u ∣ χ(1)` on `𝒳(H₀)` + 共有 helper 抽出

`caseB_degree_qu` ((9.9.a) 第2文 `χ(1)=u` on `𝒳(H₀C')`) の chief-factor constituent 抽出 (旧
obligation 1) を共有 helper に切り出し、(9.9.a) **第1文** `χ ∈ 𝒳(H₀) ⟹ u ∣ χ(1)` を実証明
(両 sorry-free + axiom-clean [3 標準公理のみ]、full build 3886 green)。

- **`caseB_exists_chiefFactorConstituent`** (S11、新 helper): case (b) で `χ∈𝒳`・`H₀⊆Ker χ` から
  chief-factor constituent `θ₀` (inflation 形、`inertia_HU(θ₀)=HC`=`inertia_eq_hcInHu`、linear
  `θ₀(1)=1`) を抽出。`caseB_degree_qu` を rewire (旧 obligation 1 をこの helper 呼び出しに置換、
  ~70 行 → 5 行) + 新 divisibility が共有。型に `IrreducibleCharacter.LiesOver`/`inertia` を出すため
  `hInHu` の `[Fintype]`/`[Invertible]` を binder 化 (`huSub` 側は body haveI、`unusedFintypeInType`
  linter 準拠)。
- **`caseB_xi_H0_degree_dvd_u`** (S11、(9.9.a) 第1文): `∀ χ∈𝒳(H₀), ∀ d:ℕ, χ(1)=d → u ∣ d`。Clifford
  degree formula `χ(1)=⟨Res χ,θ₀⟩·[HU:HC]·θ₀(1)`
  (`apply_one_eq_restrictionMultiplicity_mul_index_inertia`) + `[HU:HC]=u` (`index_hcInHu_…`) で
  `χ(1)=e·u·θ₀(1)` (e=restriction mult を `restrictionMultiplicity_natCast` で ℕ 化、θ₀(1) も ℕ
  degree)。**θ₀(1)=1 すら不要** — `e·θ₀(1)` が ℕ ゆえ `u ∣ χ(1)` 直接 (degree_qu の e=1 sandwich より弱く広い)。
- ⟹ **(9.9.a) は両文とも形式化済** (第2文=`caseB_degree_qu`、第1文=新 `caseB_xi_H0_degree_dvd_u`)。

**残 §9 (headline sorry) = (4.5)/(4.7) Dade reducible-count に gated** (真の上流 blocker、精密化):
(9.8) `caseA_character_counts` / (9.9.b) `{φ∈𝒮(H₀)|¬irred}.ncard=p−1` + degree/membership /
(9.9.c) exceptional / (9.10) は全て「𝒮(H₀) contains exactly p−1 reducible μ_j」を要し、これは
§4 Dade (Pf (4.5)/(4.7)、S06 `CertainTypeHypothesis A L` でパラメタ化) を **L=M/H₀ の商**に適用する
必要がある (Pf (8.4.d): Hypothesis (4.2) holds for L=M/H₀ and L=M/H₀C with `W₂` → `W̄₂`)。
**この M/H₀ への (4.2)/(4.6) bridge は未構築** = §9 reducible-count の唯一の genuine multi-session
blocker。S12 は §4 Dade を群 M に直接適用 (`dadeData` on A_0(M)) するのみで商版は無い。次の lane-a
genuine target = この quotient-Dade bridge の構築。

## 完了条件

(9.8)/(9.9)/(9.10) が genuine な carrier に対し sorry-free。これで (10.7)→(10.8)`hB` と (11.8) の
§9 依存が外れ、W3 の両 on-path obligation が char-content 的に閉じうる状態になる。

## 参照

- carrier: `OddOrder/Peterfalvi/S11_MaximalII_III_IV.lean` `Section11CharacterData` (~1578);
  genuine families `xiSet`/`xiOf`/`sSet`/`sOf` (~1486-1570); counts `caseA_character_counts`(~2626)/
  `caseB_character_counts`(~2638)/`exceptional_case_frobenius_realization`(~2651);
  case-(b) Singer infra `chiefFactor_caseB_image_*` (~2092/2189/2376); `ChiefFactorData` producer
  `exists_chiefFactorData` (~1406)。
- consumers: `S12.typeII_derived_frobenius` (5765), `S12.exists_zeta_residual_not_orthogonal` (~6580),
  S13 type III/IV。
- 原典: Pf §9 = `references/peterfalvi/04.11` + (9.7)-(9.11); (10.7) 証明 = `04.12` line 71。
- 関連: issue 2020, `notes/peterfalvi/s13_11_8_orthogonality.md`,
  `notes/peterfalvi/s12_10_8_noncoherence.md`。

## 2026-07-06 lane-a /loop — (10.8) scoping が本 keystone への収束を再確認 + frontier 明確化

`/loop Aレーンを進めます` で (10.8) `typeII_coherence_contradiction_estimate` (S12:453) を subagent 精査 →
**本 2030 keystone に bottom out することを再確認** (notes/s12_10_8_noncoherence.md, commit a3f5baa3):
- (10.8) の `∃u≥7` goal は type-II partner の `|U|` を existential bundle → **(10.7) `typeII_derived_frobenius`
  に gated**。(10.7) の Coq `Frob_der1_type2` は partner chief factor に (9.8.b)/(9.9.b)/(9.10) を cite
  (= 本 issue の §9 counts) **加えて** prime-TI-reducible apparatus (`primeTIred`/`FTtypeP_subcoherent`/
  `cyclicTIiso`, Coq §3/§4) を T2 4-member family coherence 用に要する (repo 不在)。
- ∴ (10.7) は **本 issue の §9 counts (task B/C) + 別途 prime-TI foundation** の両方を要する。
- **一方 (11.8) 側** (gate-2 `coherent_Sset_of_column_identities`) は (9.11) `sibleyTarget_H0C` (§14-gated)
  + carrier bridge。§9 counts (B/C) は両 obligation の共通 prerequisite。
- **stale 訂正**: issue 1017 の「§5 uniform_degree_coherence 不在」は誤り (= `coherent_of_constant_degree`
  完遂済)。issue 1017 RE-DIAGNOSIS 節参照。

**⟹ 現 ungated lane-a frontier = task B (case-(b) §9 count) の Clifford 次数 assembly** (本 issue 上記
task B: χ∈Irr(HU) の Res_H → realized-inflation constituent θ + 誘導次数 χ(1)=u)。infra 全存在
(`caseB_inertia_realized` ✓ / `isIrreducibleCharacter_induce_of_inertia_eq` / `card_filter_induce_eq_index_inertia`)、
「新 math 0・intricate realization」。次 subagent (2026-07-06 lane-a) がこの Clifford 次数 brick を build 中。

## 2026-07-06 lane-a (β) — 検証: Clifford 次数 brick は既に landed、(9.9) 全体 COMPLETE (map 是正)

subagent が「Clifford 次数 brick を build」しようとしたが、**読み込み検証の結果 (9.9) 全体が既に sorry-free と判明**
(leaf build 3849 green、S11 の real sorry は 3 個のみ: 6353/9820/9893、いずれも (9.9) 外)。冒頭 task B の
「Clifford 次数が次の大ピース・新規構築要」記述は **stale**。新規 landing 無し (誠実 = 既存を再構築しない)。

**(9.9) `caseB_character_counts` (S11:9838-9856) = 全 4 conjunct sorry-free** (依存 chain 全て S11:4699-8556、
caseA sorry 9820 より上流、build で確認):
- **(9.9.a)** degree-qu = `caseB_degree_qu` (S11:6157)。**これが prompt の言う "Clifford-degree brick"、既に genuine**:
  `caseB_exists_chiefFactorConstituent` (chief-factor constituent θ₀ を `exists_constituent_not_subset_characterKernel`
  + inflation `exists_compHom_eq_of_subset_characterKernel` + inertia `inertia_eq_hcInHu`←`caseB_inertia_realized` で
  抽出) → Clifford 次数 `apply_one_eq_index_of_liesOver_linear_inertia` で χ(1)=[HU:HC]=u → `induceHU_apply_one_eq_q_mul`
  で qu。hoisting/false-hyp 無し。第1文 `u∣χ(1)` も `caseB_xi_H0_degree_dvd_u` で別途済。
- **(9.9.b)** = `reducible_count_sOf_H0` (S11:5489、§9↔§6 bijection、**M/H₀ quotient-Dade bridge は已構築** — issue
  末尾で「唯一の genuine multi-session blocker」とした M/H₀ (4.2)/(4.6) bridge は完了、これも stale) +
  `reducible_mem_sOf_H0C` (S11:6312、cardinality 論法) + `forall_mem_sOf_H0C_apply_one_eq_qu` (S11:6274)。
- **(9.9.c)** = `caseB_no_irreducible_forces_C_bot` (S11:7256、C=⊥ pair-character) + `caseB_no_irreducible_u_formula`
  (S11:8430、u=(p^q−1)/(p−1)、caseB oXtheta を二重に数える genuine proof、C=⊥ で join collapse)。

**S11 に残る 3 sorry (全て本 subagent の scope 外 = prompt が「別 deep brick、attempt するな」と指定した類)**:
1. **S11:6353** `sibleyTarget_H0C` — (9.11) task D、明示的に §14-gated (Sibley/(6.8) witness)。
2. **S11:9820** `caseA_character_counts` (9.8) conjunct **(d)**: `((p−1)/a)·(|U|/(a|U'|)) ≤ #{irr χ∈𝒮(H₀U'), deg qa}`.
   = case-(a) の degree-**qa** count。infra **不在** (grep 確認: degree-qa/𝒳(H₀U') 用の補題は皆無、case-(b) の
   `caseB_inertia_realized`/degree-u とは別物、parameter `a` = `CliffordCaseAData.a` 絡みの Dade 下界)。task C
   (case-(a) Dade brick) 本体、multi-session。他 3 conjunct (b count/b deg+mem/c) は landed。
3. **S11:9893** `exceptional_case_frobenius_realization` (9.10) の **type-II HU-Frobenius clause**
   `IsFrobeniusGroup ↥(H⊔U) H U`。他 2 conjunct (FPF `chiefFactor_caseB_action_fpf` / u-formula
   `caseB_no_irreducible_u_formula`) は landed。残 clause は Pf (9.10)/(10.7) が **H₀=1 を要する** (H̄=H に
   collapse して初めて HU が kernel H で Frobenius; H₀=1 は (11.7)←(10.8) downstream)。docstring 9873 が正しく
   gated と記述。ungated route 無し。

**⟹ lane-a §9 の ungated frontier は task B ではなく尽きている** (case-(b) 完了)。次の genuine §9 work = task C
(case-(a) (9.8.d) degree-qa Dade count、新規 infra 構築) か task D ((9.11) §14 witness、gated)。(10.7)/(10.8)・
(11.8) の §9 依存のうち **case-(b) 分 ((9.9)/(9.9.b)/(9.9.c)) は解消済**; 残依存は (9.8.b) [済] + (9.8.d) [task C] +
(9.10) type-II Frobenius [H₀=1 gated] + prime-TI foundation (repo 不在)。

## 2026-07-06 lane-a /loop — (9.8.d) case-(a) degree-qa count 大幅前進 (6 verified landings)

`/loop Aレーンを進めます` 継続セッション。task C = (9.8.d) `caseA_character_counts` conjunct (d)
(case-(a) degree-qa Dade count) を substrate から系統的に build。**6 commit landed (全 exit-0 green,
no new sorry/axiom, AxiomsCheck OK)**:
- `23424b59`: **de-hoist** `CliffordCaseAData.a` (free field → genuine cardinality) + degree-index
  substrate (`cuSub`/`cuInHu`=C_U(S₀), `index_hcuInHu_eq_caseA_a`=[HU:H·C_U(S₀)]=a)。
- `6c8734ef`: hard inertia direction `inertia_inf_uInHu_le_cuInHu`。
- `62d1879e`: **full inertia** `inertia_eq_hcuInHu` (I_{HU}(θ₁₀)=H·C_U(S₀), S₀-summand decomp via
  operator Maschke) + source char `exists_source_char_caseA`。
- `ddfb4d0e`: λ-lift channel `hcuLambdaHom` + `hInHu_inf_cuInHu_eq_bot`。**構造訂正**: H·C_U(S₀)=
  H⋊C_U(S₀) は**半直積** (C_U(S₀) 非正規)→θ₁ は extension (inflation でない)。
- `3668e556`: **degree-qa irreducible char capstone** `caseA_exists_irreducible_source_degree_qa`
  (∃ζ, irreducible ∧ ζ(1)=a ∧ Ind_{HU}^M ζ(1)=qa)、θ₀-extension via `SemidirectProduct.lift`。
- `936771c0`: count 前提 `uprimeSub_le_cuSub` (U'≤C_U(S₀)) + `realizedH0supUprime_normal_huSub` (H₀U'◁M)。

**残 (9.8.d) = count の hard research core** (subagent a80c2a1e が着手中):
- (iii) membership ∈𝒮(H₀U'): **tractable** plumbing (前提 landed、mirror hcZetaPair_mem_xiSet)。
- (iv) Ind_{HU}^M irreducibility: **hard-absent** = **single-summand** S₀-supported θ₁ の W₁-free-orbit
  propagation (既存 clifford_caseA は full regular seed 用)。
- (v) count bijection: **hard-absent** = U-orbit descent (`OrbitOnIrr.card_image_induce_eq_div` は
  normality 要、C_U(S₀) 非正規ゆえ不適 → U-orbit (size a) conjugation-descent 補題 要)。

⟹ (9.8.d) は source-char + degree 完成、残は **count の (iv)/(v) research infra** (single-summand
orbit propagation + U-orbit count descent)。iii が landing すれば substrate は count 直前まで完備。
