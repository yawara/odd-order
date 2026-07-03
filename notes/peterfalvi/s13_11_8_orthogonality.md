# Peterfalvi (11.8) — the main orthogonality calculation (lane-b W3 handoff) (現 lane a)

> ⚠ S12 は 2026-07-02 prefix-split (95fc7ade): 凍結 decl の旧 S12:NNNN (≲6100) は
> `S12_MaximalIII_IV_V_Core.lean` (+~8 行ずれ)、active (11.8) は 2768 行の
> `S12_MaximalIII_IV_V.lean` (`exists_zeta_residual_not_orthogonal` は現 :~2645)。

> repo `S13_MaximalIII_IV.lean` = **Pf §11** (file 番号 = §番号 −2)。(11.8) は `card_kappaHall_lt_of_isTypeIIIorIV`
> (FeitThompson:426, Pf (11.9.b)) の唯一の deep gate。**(10.9)-half + reduction spine は landed**
> (commits 257f9b45 / dcc00462)、残 = この (11.8) discharge + carrier bridge。
> mmd `04.13` の (11.8.1)-(11.8.4) は `[MISSING_PAGE_FAIL:3]` (p.66) で欠落 → 本ノートに PDF から復元
> ([[nougat-missing-page-recovery]]、references は gitignore ゆえ repo notes が durable home)。

## (11.8) statement

Hypothesis (11.2) (= (10.1) + M Type III/IV、`p=|W₂|`, `q=|W₁|`、`S(X)={χ∈S | X⊆Ker χ}`)。
ζ ∈ S(HC) に対し、`(μ₀−ζ)^τ − ∑_{0≤i<q} ω_{i0}^σ` は (Irr W)^σ に**直交しない**。

## 証明の骨格 (by contradiction)

**S₁ = S(HC)** と置く。`u = |U/C|`。(U/C)⋊W₁ は abelian kernel U/C の Frobenius 群ゆえ、
**S₁ は degree q の既約指標 (u−1)/q 個から成る** (= 定数次数 q!)。τ₁ = τ の Z[S₁] への拡張、
**(5.7) で存在** (定数次数 ⟹ coherent = `S07.coherent_of_constant_degree` ✅ 形式化済)。
α_{ij} = μ_{ij} − δμ_{i0} − nζ (0≤i<q, 0<j<p)。

### (11.8.1) d=u, δ=1, n=|S₁|=(u−1)/q
(9.8)/(9.9) で μ_j(1)=qu (j≠0) ⟹ d=μ_{ij}(1)=u。(U/C)⋊W₁ Frobenius ⟹ u≡1 (mod q) ⟹ δ=1,
n=(d−δ)/q=(u−1)/q。**gate**: (9.8)/(9.9) (§9=repo S11、char)。

### (11.8.2) α_{ij}^τ = X − nζ^{τ₁} + a·∑_{λ∈S₁} λ^{τ₁}, X ⊥ S₁^{τ₁}, a∈{0,1,2}; a=0 or 2 ⟹ X = ω_{ij}^σ − ω_{i0}^σ
(10.5) で α_{ij} 定義。λ∈S₁, λ≠ζ ⟹ (α_{ij}^τ,(ζ−λ)^τ)=(α_{ij},ζ−λ)=−n。∴ ∃ a∈ℤ, X⊥S₁^{τ₁} で
α_{ij}^τ=X−nζ^{τ₁}+a∑λ^{τ₁}。CS: (a−n)²+(|S₁|−1)a² = ‖−nζ^{τ₁}+a∑λ^{τ₁}‖² ≤ ‖α_{ij}^τ‖² = n²+2。
⟹ |S₁|a²−2an ≤ 2 ⟹ n(a²−2a)≤2 ⟹ 0≤a≤2。a=0 or 2 ⟹ ‖X‖²=2 ⟹ X=ω_{ij}^σ−ω_{i0}^σ ((10.5) と同様)。
**gate**: (10.5) (α image、repo S12 char)、‖α_{ij}^τ‖²=n²+2 (`muGridAlpha_tau_inner_self` ✅)。

### (11.8.3) β = α_{ij}^τ − (ω_{ij}^σ−ω_{i0}^σ) + nζ^{τ₁} は i,j 独立 (j≠0)、かつ β は real
(4.8): (α_{ij}−α_{ik})^τ=(μ_{ij}−μ_{ik})^τ=ω_{ij}^σ−ω_{ik}^σ ⟹ β_{ij} は j 独立。
(4.10): (α_{ij}−α_{0j})^τ=ω_{ij}^σ−ω_{i0}^σ−ω_{0j}^σ+ω_{00}^σ ⟹ β_{ij}=β_{0j}、i,j 独立。
real: (3.9.a)+(4.3.b)+(5.9) で β̄_{0j}=β_{0j}。**gate**: (4.8)/(4.10)/(3.9.a)/(4.3.b)/(5.9) (§4/§5、char)。

### (11.8.4) [背理法の仮定] (μ₀−ζ)^τ が (Irr W)^σ に直交すると仮定 ⟹ (μ₀−ζ)^τ = ∑_{0≤i<q} ω_{i0}^σ − ζ^{τ₁}
(μ₀−ζ)^τ=∑_i ω_{i0}^σ−χ と置くと ‖χ‖²=‖μ₀−ζ‖²−q=1 (← **これは coherence-free (10.9) `…residual…`
が与える直交補 + ‖μ₀−ζ‖²=q+1**)。⟨(μ₀−ζ)^τ,(ζ̄−ζ)^τ⟩ を見て χ=ζ^{τ₁} or −ζ̄^{τ₁}。|S₁|=2 ∧ χ=−ζ̄^{τ₁}
なら ζ^{τ₁}↔−ζ̄^{τ₁} を swap して χ=ζ^{τ₁} に正規化。**ここで landed (10.9) が直接効く** (χ⊥(Irr W)^σ, ‖χ‖²=1)。

### (11.8.5) a=0
((μ₀−ζ)^τ,α_{ij}^τ) を 2 通り計算: G 側 = (∑ω_{r0}^σ−ζ^{τ₁}, β+ω_{ij}^σ−ω_{i0}^σ−nζ^{τ₁}) =
(∑ω_{r0}^σ,β)−1−a+n; M 側 = (μ₀−ζ,α_{ij}) = −1+n。⟹ a=(∑ω_{r0}^σ,β)。(β,1_G)=(α_{ij},1_M)=0 (i≠0)
+ β real ⟹ a even。(11.8.2) X=ω_{ij}^σ−ω_{i0}^σ ⟹ β=a∑_{λ∈S₁}λ^{τ₁}、(5.3.b) で a=0。

### (11.8.6) 結論 (矛盾の導出)
(11.8.2)+(11.8.5): α_{ij}^τ=ω_{ij}^σ−ω_{i0}^σ−nζ^{τ₁} (∀i)。⟹ (μ_j−dζ)^τ=∑_i ω_{ij}^σ−dζ^{τ₁} (0<j<p)。
**S₂ = S(C)−S(HC)**。(9.11) で S(H₀C')−S(HC') coherent ⟹ (11.7) で S₂ coherent、(9.8.b)/(9.9.b) で
μ_k∈S₂ (k≠0)。τ₂ = τ の Z[S₂] 拡張。(5.3.b)/(5.5) で S₁^{τ₁}⊥S₂^{τ₂}。
**μ_j^{τ₂}=∑_i ω_{ij}^σ を示せば S(C)=S₁∪S₂ coherent ⟹ (11.3) `S_H0C_not_coherent` (✅ proven) と矛盾**。
μ_j^{τ₂}=∑_i ω_{ij}^σ: S₂∩Irr M=∅ なら (4.9) で τ₂ をそう定義可; λ∈S₂∩Irr M なら
((λ(1)μ_j−μ_j(1)λ)^τ,(μ_j−dζ)^τ)≠0 + (5.8)。

## 形式化プラン (next session, deep multi-step)

**foundation (available)**:
- (5.7) `S07.coherent_of_constant_degree` ✅ — S(HC) (定数次数 q) の coherence τ₁。
- (10.9) coherence-free `inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2` +
  `residual_alignedOmegaSigma_inner_eq_zero_of_w1_lt_w2` ✅ (本 W3 landed) — (11.8.4) の直交補核。
- (11.3) `S13.S_H0C_not_coherent` ✅ (cite-reduced) — 矛盾の到達先。
- ‖α_{ij}^τ‖²=2+n² `S12.muGridAlpha_tau_inner_self` ✅。
- (4.8)/(4.9)/(4.10) (§4 Dade)、(5.3.b)/(5.5)/(5.8)/(5.9) (§5)、(3.9.a) — 大半 formalized (要 grep 確認)。

**gate (char、未形式化 or sorried)**:
- (9.8)/(9.9)/(9.11) (§9=repo S11、char) — (11.8.1) μ_j(1)=qu, (11.8.6) S₂ coherence/μ_k∈S₂。
- S(HC)/S(C)/S₂ の carrier 材料化 (現 S13 `SOf` は opaque field)。
- §11 Hypothesis の τ₁ (S(HC)-coherent extension) と §10 carrier (muGrid/tau) の bridge (`hyp.base`)。

**攻略順 (上流優先)**: (11.8.1)→(11.8.2)→(11.8.3) は σ/α 算術 (§4/§5 cite)、(11.8.4) は landed (10.9) 直結、
(11.8.5)/(11.8.6) は矛盾導出 ((9.11)+(11.3))。**最大の負荷 = §9 (9.8/9.9/9.11) carrier + S(HC)/S₂ 材料化**。

## carrier bridge (card_kappaHall への翻訳、調査済)

- **|K| = w₁** ✅ available: `card_kappaHall_eq_derived_index` (|K|=[S:S']) + `TypePData.card_W1_eq_derived_index`
  (|W₁|=[S:S']) ⟹ |K|=|W₁|=w₁ (両者 M' を complement)。
- **|Kstar| = w₂**: `card_kappaHall_sup_Kstar` (|K⊔Kstar|=|K|·|Kstar|) + 要 |K⊔Kstar|=|W|=w₁·w₂
  (type-P duality、`typeP_duality`/BG 14.7(4)(5))。⟹ |K|=w₁ より |Kstar|=w₂。bridge は BG §14 duality。
- ∃ ζ∈S(HC) (degree w₁): S(HC) は (u−1)/q≥1 個の degree-q 既約 (Frobenius (U/C)⋊W₁) ⟹ nonempty + degree w₁ 自動。

## 結論

`card_kappaHall_lt_of_isTypeIIIorIV` = [build §10 carrier] + [∃ζ∈S(HC)] + [**genuine (11.8) = 本ノートの deep proof**]
+ [reduction spine ✅] + [|K|=w₁ ✅, |Kstar|=w₂ via duality]。**唯一の deep 残 = (11.8)** (multi-step char、
(5.7)/(10.9)/(11.3) foundation 上、§9 carrier が最大負荷)。

## 2026-06-26 update — carrier translation + reduction fully wired; sole gate = genuine (11.8)

The carrier bridge and reduction are now **landed and wired** into the FT consumer. **The bare
`feitThompson` sorry `card_kappaHall_lt_of_isTypeIIIorIV` (FeitThompson:426) is gone**; its proof
assembles:
- `|K| = w₁` (`card_kappaHall_eq_derived_index` + `TypePData.card_W1_eq_derived_index`, both = derived index);
- `|K*| = w₂` = **`card_Msigma_inf_centralizer_eq_card_W2`** (FeitThompson.lean, **axiom-clean**, AxiomsCheck-
  registered). The old "via type-P duality `card_kappaHall_sup_Kstar`+|K⊔Kstar|=|W|" route was replaced by a
  more direct centralizer argument: `W₂ = M' ⊓ C(W₁)` sandwiched by `W₂ ≤ M_F ≤ M_σ ≤ M'`, plus κ-Hall ↔ W₁
  Schur–Zassenhaus conjugacy (no need to identify `K ⊔ K*` with the type-data `W`);
- `w₂ < w₁` = `S12.w2_lt_w1_of_hypothesis` = `S12.exists_zeta_residual_not_orthogonal` (genuine (11.8))
  + `S12.w2_lt_w1_of_residual_not_orthogonal` (coherence-free reduction, already landed).

**Sole remaining W3 gate** = `S12.exists_zeta_residual_not_orthogonal`: ∃ `ζ ∈ inducedFamily M` (degree `w₁`,
Peterfalvi's `ζ ∈ S(HC)`) with the residual `(μ₀−ζ)^τ − ∑ω_{i0}^σ` **not** ⊥ `(Irr W)^σ`. This is the deep
(11.8.1)–(11.8.6) calculation documented above (needs `τ₁` from (5.7) on `S(HC)`, `τ₂` from (11.7)/(9.11),
the α-grid σ-identities, contradiction with (11.3)). The whole §9-char + `S(HC)`/`τ₁` materialization remains
the genuine multi-step load.

## 2026-06-29 update (lane-a) — ζ witness landed; 残 = orthogonality 計算のみ

`exists_zeta_residual_not_orthogonal` (S12:6762) の bare sorry を「**実 ζ witness 供給 + 3/4 conjunct
実証明**」へ還元 (commit 47158295)。
- ζ = `exists_zeta_in_inducedFamily_degree_w1 hyp.typeP hG.odd (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)`。
- ∈ inducedFamily / IsIrreducibleCharacter / ζ(1)=w₁ (defeq `hyp.w1=Nat.card hyp.typeP.W1`) 実証明。
- **残 sorry = (11.8.1)-(11.8.6) の orthogonality 計算のみ** (背理法本体)。

**確認済 available infra (次反復の grind 用、S12)**:
- ζ witness ✅ (上記)。τ₁ = `tau1` (S12:2716)。
- α^τ inner: `muGridAlpha_tau_inner_self` (3172, =2+n²)、`_zeta_sub_conj` (3396)、`_muColumn_sub_conj`
  (3489)、`_muColumn_self_sub_conj` (3523)。τ=τ₁ bridge: `tau_zeta_sub_conj_eq_tau1` (3552)、
  `tau_muColumn_sub_conj_eq_tau1` (3576)。τ₁ inner: `muGridAlpha_tau1_inner_muColumn` (3674)、
  `_self_sub_conj` (3716)、`muColumn_tau1_inner_self` (3743)。
- (10.9): `residual_alignedOmegaSigma_inner_eq_zero_of_w1_lt_w2` (6685)、
  `inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2` (6545)。矛盾先 (11.3): `S13.S_H0C_not_coherent`。
- aligned grid: `exists_intCast_alignedOmegaSigmaGrid_zero_column` (1312)、`alignedOmegaSigmaGrid_zero_zero` (1391)、
  `exists_rowInv_alignedOmegaSigma_conj` (1459)、`muGrid_column_sum_mem_inducedFamily` (2179)。

**次の攻略点**: by_contra h_orth → (11.8.1) n=(u−1)/q (要 μ_j(1)=qu = §9 counts cite) → (11.8.2) α^τ
CS bound a∈{0,1,2} (上記 inner lemmas) → (11.8.4) landed (10.9) 直結 → (11.8.5) a=0 → (11.8.6) S(C)
coherent ⟹ (11.3) 矛盾。§9 counts ((9.8)/(9.9)) は S11 で sorried、signature-contract で cite。

## 2026-06-29 update² (lane-a) — (11.8) assembly 精密 map; tractability 上方修正

(11.8) infra を deep dive した結果、当初の「§9 multi-session gated」は**過度に悲観的**と判明:
- **degree facts available (≠§9-gated)**: `muGrid_apply_one_eq` (S12:1852, μ_{ij}(1) 独立 j≠0)、
  `muGrid_apply_one_within_column` (1554)/`_cross_column` (1794) — CharacterParameters.degree_independent の source。
- **δ available**: `muColumnSign` (1865, columnFamily.sign) = CharacterParameters.delta の source。
- **核心 decomposition (S-coherent ⟹)**: `tau_muColumnZero_sub_zeta_eq` (5039, PROVEN):
  `coh : CoherentHypothesis` + params 条件下で `τ(μ₀-ζ) = ∑ω_{i0}^σ - ζ^{τ₁}` ⟹ residual = -ζ^{τ₁}。
  **向き注意**: これは「S coherent ⟹ decomposition」。(11.8) は**逆**「residual ⊥ ⟹ S coherent」が要点。
- **α^τ/τ₁ inner 群** (3172-3911): muGridAlpha_tau_inner_self (=2+n²) 他、CS bound (11.8.2) の source。
- **(11.3) target**: `S13.S_H0C_not_coherent` (S13:209)。

**`CoherentHypothesis hyp params` = full `S07.IsCoherent hyp.tau hyp.Sset hyp.A0`** (S=hyp.Sset 全体の
coherence)。⟹ (11.8) 証明構造 = by_contra (residual ⊥) → **S-coherence を構成** (CharacterParameters +
CoherentHypothesis を build) → (11.3) `S_H0C_not_coherent` と矛盾。

### concrete 攻略順 (次反復から、available infra で)
1. **`CharacterParameters hyp` 構成** (noncomputable def): zeta=exists_zeta、mu=muGrid、omegaSigma=
   alignedOmegaSigmaGrid、delta=muColumnSign、degree_independent=muGrid_apply_one_eq、d=共通 degree、
   n_formula/two_le_n=parity (d odd ∵ d∣|M| odd; δ=±1; w1 odd ⟹ n even>0)、alpha_support=muGrid_alpha_support、
   w2_prime/d_gt_one。**大半 available、parity と w2_prime が要 sourcing**。
2. **CoherentHypothesis (S(HC)=S₁ coherence τ₁)**: (5.7) `S07.coherent_of_constant_degree` (S(HC) 定数次数 q)。
   但し hyp.Sset = 全 S か S(HC) か要確認 (full S coherence が contradiction target)。
3. residual ⊥ ⟹ μ_j^{τ₂}=∑ω_{ij}^σ (11.8.5 の a=0) → τ₂ glue (S₂ from (9.11)/(11.7)) → S(C) coherent → (11.3) 矛盾。

**評価修正**: (11.8) は「最難 multi-session」だが §9 char counts に gated ではない (degree は muGrid 機構が供給済)。
available infra で assembly 可能な multi-step。次反復 = CharacterParameters 構成から。

## 2026-06-29 update³ (lane-a) — (11.8) construction 完全 recipe; 全 infra 確認済

(11.8) の全 building blocks を S07/S12 で確認。**blocked でなく、執行可能な large multi-step**:

**available (確認済)**:
- params + 全 (10.6.b) 条件: `exists_charParameters_full` (S12:3002)。
- norms: `inner_muColumnZero_sub_zeta_self` (‖μ₀-ζ‖²=w₁+1, S12:6625 で使用)、
  `muGrid_column_sum_inner_self` (‖∑μ_{ij}‖²=w₁, S12:2234)。
- σ-coefficient machinery: `sigmaCoeff_trichotomy` (S05 (3.8))、(10.9) 証明内で完全運用 (S12:6643)。
- S₁=S(HC)-coherence: (5.7) `coherent_of_constant_degree` (COMPLETE)。
- **union 構成 API** (S07_Coherence): `coherentPair` (3415)、`coherentUnion_of_glued` +variants (4407-4581)、
  `coherentPairChain`/`coherentOfPairChainCover` (4803/4841, (6.6) chain)、`coherentPair_fromDade` (5913,
  Dade base で {χ,χ̄} pair の IsCoherent)、`int_eq_zero_of_sq_mul_le_of_two_mul_lt` (5.6.2 core)。
- (11.3) target: `S13.S_H0C_not_coherent` (S13:209)。

**残執行 (large multi-step、新 infra 要)**:
1. **α-identities を S₁-τ₁ で再導出** (= 最大の負荷): 既存 `muGridAlpha_tau_*` (S12:3172-3947) は
   `coh : CoherentHypothesis` = **full S coherence** を要求するので by_contra (full coh 未取得) では使えない。
   (11.8.2)-(11.8.5) の α^τ CS bound・a=0 を **(5.7) の S₁-τ₁** で再導出する新 lemma 群が要る。
2. union 適用: 1 の identity (μ_j-dζ)^τ=∑ω_{ij}^σ-dζ^{τ₁} → `coherentUnion_of_glued`/`coherentPairChain` で
   S(C)=S₁∪S₂ の IsCoherent 構成。
3. τ₂ (S₂=S(C)-S(HC)): (9.11)/(11.7)。(9.11)=`coherent_H0C_commutator` (S11、sibleyTarget_H0C sorry、
   signature-contract で cite 可)。
4. by_contra: residual ⊥ ⟹ 1-3 で full S coherent 構成 → (11.3) `S_H0C_not_coherent` と矛盾。

**状態 (honest)**: (11.8) は完全に scope 済・全 infra 確認済で feasible。執行は **§11 char 終盤の最大の山** =
α-identities-with-S₁-τ₁ の新 lemma 群 (forward 版の S₁-coherence 版) を起点とする large multi-iteration。
ζ witness + params/by_contra 足場は landed (commits 47158295/25ad0aec)。次 = α-identity-with-S₁-τ₁ 起点。

## 2026-06-29 update⁴ (lane-a) — 執行 stack の build 順確定 (foundational bridge は未構築)

(11.8) 執行 = §10-11 coherence-construction infra stack の build。各層を確認した結果の build 順:

1. **§10 hyp → S07.Hypothesis bridge** (未構築・foundational): `S07.Hypothesis S A` は tau_isometry/
   conjugate_closed/no_real_characters/pairwise_orthogonal/difference_image/difference_images_orthogonal
   を要求。現状 `inducedFamily_closedUnderConjugate` (S12:83) のみ。残 (no_real/pairwise_orthogonal/
   difference_image 等) を inducedFamily/Dade tau から build。
2. **S(HC) materialization**: S_HC = {φ∈inducedFamily M | degree w₁} subfamily + constant-degree 条件。
3. **(5.7) 適用** → S₁=S(HC)-coherence τ₁ (`coherent_of_constant_degree`、Nonempty IsCoherent)。
4. **(11.8.x) identities を τ₁ で**: 一部 coh-free 済 (`muGridAlpha_tau_inner_self` =2+n², coh 不要)、
   τ₁ 絡み (`muGridAlpha_tau1_zeta_eq_neg_n`/`zeta_tau1_inner_self`) は full-coh 版あり→S₁-τ₁ 版が要る。
5. **union** (`coherentUnion_of_glued`/`coherentPairChain`) で S(C)=S₁∪S₂ coherence。
6. **τ₂** (S₂): (9.11) `coherent_H0C_commutator` (S11、sibleyTarget_H0C sorry、cite 可) + (11.7)。
7. **contradiction**: by_contra (residual ⊥) → 1-6 で full S coherent → (11.3) `S_H0C_not_coherent` 矛盾。

**honest 評価**: (11.8) は §11 char 終盤の最大の山で、執行は **layer 1 (S07.Hypothesis bridge) から始まる
深い未構築 infra stack** = major multi-iteration。setup (ζ witness/params/by_contra) + 完全 scope は landed。
**次 = layer 1: inducedFamily の S07.Hypothesis 性質 (no_real/pairwise_orthogonal/difference_image) を build**。

## 2026-06-29 update⁵ (lane-a) — assessment 修正: (11.8) infra は完備、no_real は組立で feasible

deep dive で update³/⁴ の「深い再帰未構築 stack」評価が**悲観的すぎた**と判明。layer 1 の核心
`no_real_characters (inducedFamily M)` の build に要る infra は**ほぼ全て available**:
- **Mackey ✅**: `card_mul_inner_induce` (two-fn, InducedIrreducible:135) `|H|⟨Ind θ,Ind ψ⟩=∑⟨θ,ψ^{x⁻¹}⟩`、
  `card_smul_restrict_induce` (99)、`card_mul_inner_self_induce` (120)。
- `ClassFunction.induce_conj` ✅ (S12:107 で使用)。
- conjByOrbit 機構 ✅: `card_conjByOrbit_eq_index_inertia` (227)、`mem_conjByOrbit`/`conjBy_mem_conjByOrbit`
  (Clifford:745/750)、Brauer perm (`ConjugationBrauer.lean`: conjByPerm 30、card_fixedPoints 186)。
- `not_isReal_of_ne_trivial_irreducible_of_odd_card` (S03:155) ✅。

**no_real の証明** (組立、feasible): χ=Ind θ∈inducedFamily, θ≠1。χ.IsReal ⟹ χ.conj=χ ⟹ Ind θ̄=Ind θ ⟹
⟨Ind θ,Ind θ⟩=⟨Ind θ,Ind θ̄⟩。Mackey: |H|⟨Ind θ,Ind θ̄⟩=∑⟨θ,θ̄^{x⁻¹}⟩。θ̄∉conjByOrbit(θ) なら全項 0 ⟹
⟨Ind θ,Ind θ̄⟩=0 だが ⟨Ind θ,Ind θ⟩≥1、矛盾。**θ̄∉conjByOrbit(θ)** = odd-orbit involution 論法:
conjByOrbit(θ) 奇数 card (=[M':I_θ]∣|M'| odd)、σ:η↦η̄ involution が θ̄∈orbit なら orbit を保ち、
**involution on odd-card set ⟹ fixed pt η** (η̄=η ⟹ η real ⟹ η=1 ⟹ 1∈orbit(θ) ⟹ θ=1 矛盾)。

**残る唯一の fiddly piece** = `involution on odd-card finite set has a fixed point` (mathlib に
`Function.Involutive`+odd card であるか要確認、無ければ「非不動点は 2 元 orbit ⟹ 偶数、total 奇数 ⟹ fixed 奇数≥1」で小 helper)。+ `conjBy_conj` (conj が conjBy と可換、ext+simp)。

**評価**: no_real は **available pieces + 2 小 helper (involution-fixed-pt, conjBy_conj) の組立**で feasible。
(11.8) は「最難だが blocked でない」。layer 1 → 7 を incremental commit で積める (commit は persist)。
次 = involution-fixed-pt helper + no_real 組立。

## 2026-06-29 update⁶ (lane-a) — no_real_characters 完成 + S07.Hypothesis character-side 3/6

(11.8) construction layer 1 (S07.Hypothesis for S=inducedFamily) を incremental build:
- **`inducedFamily_hasNoRealCharacters`** ✅ (9-lemma 集大成: conjBy_conj / conjPerm_conjBy_comm /
  conjPerm_mem_conjByOrbit / conjBy_trivial / trivial_not_mem_conjByOrbit /
  conjPerm_ne_self_of_mem_conjByOrbit / conjPerm_conjPerm / conjPerm_not_mem_conjByOrbit / assembly)。
  奇数位数 orbit-involution 論法 (`card_fixedPoints_modEq` p=2 + Brauer `conjPerm` + Mackey
  `card_mul_inner_induce` + `inner_induce_eq_zero_of_not_conj`)。
- **`inducedFamily_pairwiseOrthogonal`** ✅ (induce_eq_induce_iff_conj + inner_induce_eq_zero_of_not_conj)。

**S07.Hypothesis 進捗**: tau / tau_isometry / conjugate_closed ✅ (既存 inducedFamily_closedUnderConjugate) /
no_real_characters ✅ / pairwise_orthogonal ✅ / difference_image / difference_images_orthogonal。
⟹ **character-side 3/6 完了** (conjugate_closed, no_real, pairwise_orthogonal)。残 tau-side
(tau_isometry, difference_image, difference_images_orthogonal) = §10 hyp.tau (Dade isometry, S04) 依存
= 要調査の bridge。

**重要 gotcha** [[lean-induce-transport-instance-desync]]: induce 絡みは **`open scoped FiniteInduce`**
(finiteSubFintype/natCardInvC) で instance を carrier (hreal) と統一せよ。explicit haveI
(Fintype.ofFinite/invertibleOfNonzero) は instance diamond で induce 項が syntactic に非一致になり
congrArg/trans が type mismatch。

**次**: tau-side S07.Hypothesis 性質を §10 Dade isometry (hyp.tau, hyp.dadeData) から build →
full S07.Hypothesis 組立 → (5.7) S(HC)-coherence → (5.6) union → (11.8.1)-(11.8.6) calc。

## 2026-06-29 update⁷ (lane-a) — ⚠ honest reassessment: (11.8) coherence は Dade-based、global S07.Hypothesis でない

update⁵/⁶ で「S07.Hypothesis for inducedFamily を layer 1 として組む」とした approach を **修正**:
- **S07.Hypothesis.tau_isometry = `IsIntegralIsometry` (全 φ,ψ で等長 = global)**。だが Dade map は
  **supported のみ等長** (S07_Coherence:1573 docstring + S08:1452-1454 「global IsIntegralIsometry は
  FT に存在せず Dade-based に置換」)。⟹ inducedFamily + hyp.tau(Dade) で **global S07.Hypothesis は
  構成不可** (tau_isometry が偽)。
- (11.8) coherence の正しい機構 = **Dade-based `SibleyDadeHypothesis`** (S08:3265: dade datum + TI 条件
  のみ、family の character 性質は不要) → **`sibleySetup_is_coherent`** ((6.8) capstone, S08)。
- ⟹ 私の `inducedFamily_hasNoRealCharacters` / `inducedFamily_pairwiseOrthogonal` は **family の真の事実
  (build-green) だが coherence-construction path ではない**。これらは (11.8.x) の **inner-product 計算**
  (⟨μ_j,ζ⟩=0、family 直交性) が消費する genuine な補助事実として残る (orphaned でない、[[feedback-orphaned-not-reason-to-defer]])。

**(11.8) construction の修正版 path**:
1. S(HC)=S₁ coherence: Dade-based (sibleySetup_is_coherent or (5.7) の Dade 版) — **要再調査** ((5.7)
   coherent_of_constant_degree は global S07.Hypothesis を取るので FT 直適用は不可、Dade 版が要る)。
2. S₂=S(C)−S(HC) coherence: (9.11) coherent_H0C_commutator (S11、sibleyTarget_H0C sorry) + (11.7)。
3. (11.8.1)-(11.8.5) α-grid calc (no_real/pairwise_orthogonal + α^τ inner lemmas を消費)。
4. full S(C) coherence → (11.3) `S_H0C_not_coherent` 矛盾。

**教訓** [[verify-port-state-by-number-not-coq-name]]: coherence framework の機構 (global vs Dade-based)
を先に確認すべきだった。S07.Hypothesis の名前から global isometry path と誤読した。

**次**: (11.8) coherence の Dade-based path を S08 framework (SibleyDadeHypothesis/sibleySetup_is_coherent)
で再調査し、§11 hyp の S(HC)/S(C) にどう適用するか特定する。

## 2026-06-29 update⁸ (lane-a) — (11.8) coherence path 確定: §8 Dade machinery 適用

(11.8) coherence の Dade-based machinery は §8 に **substantially built**:
- `SibleyDadeHypothesis.certainTypeSet_isCoherent_tau_canonical` (S08_CaseBAssembly:170)、
  `nonempty_coherent_S_*` (S08_PGroupReduction:159/215/298/343)、`sibleySetup_is_coherent` ((6.8) capstone)、
  `coherentYset_extension_*` (S08_CaseBCoherence)。
- §13 (S13:198-226) は coherence を **hypothesis input** (`(hcoh : Nonempty (S07.IsCoherent ...))`) として取る。
  S12 `CoherentHypothesis` (2886) が `IsCoherent hyp.tau hyp.Sset hyp.A0` を束ねる。

**(11.8) construction の確定 path**:
1. S(HC)=S₁ / S(C) coherence: §8 Dade machinery (sibleySetup_is_coherent / certainTypeSet_isCoherent) を
   §11 hyp の S(HC)/S(C) に適用 — **SibleyDadeHypothesis for §11 setup を構築** (dade datum=hyp.dadeData,
   TI 条件) して coherence を得る。§8 capstone は citeable infra (lane 跨ぎ signature-contract 可)。
2. (11.8.1)-(11.8.5) α-grid calc: no_real/pairwise_orthogonal (built ✅) + α^τ inner lemmas (built) +
   τ₁=coh.tau1 を消費。
3. full S(C) coherence → (11.3) `S_H0C_not_coherent` 矛盾。

**残作業 = §11-specific な SibleyDadeHypothesis 構築 + §8 coherence 適用 + (11.8.x) calc**。深い multi-session
endgame だが機構は確定 (global S07.Hypothesis の誤読を是正済)。foundation (ζ witness/no_real/pairwise) は landed。

## 2026-06-29 update⁹ (lane-a) — S(HC) coherence の concrete path = coherentEqualDegree_fromDade

S₁=S(HC) coherence (FT-correct, Dade-based) の concrete API 確定:
- **`coherentEqualDegree_fromDade`** (S07_Coherence:5968): `(hyp:S04.Hypothesis G A L) (hconj) (χ:Fin n→Irr(↥L))
  (n≥2) (hχinj) (hdeg: 全 equal-degree) (hsuppdiff: χⱼ−χ₀ supported on A) (1∉A) →
  IsCoherent (dadeIntegralCharacterMap hyp ...) (Set.range χ) (supportInSubgroup A L)`。
- これが FT版 (5.7) (global S07.Hypothesis 不要、Dade base map で直接 coherent)。

**S(HC) coherence の構築 path**: S(HC) = inducedFamily の degree-q 既約族を **χ:Fin n→Irr(↥M) として
enumerate** (n=(u−1)/q≥2、Frobenius (U/C)⋊W₁ から) + equal-degree(全 q)/injective/supported-diff を示し
coherentEqualDegree_fromDade 適用 → IsCoherent hyp.tau (range χ=S(HC)) A0。**= S(HC) materialization** (§11
char work、substantial)。

**(11.8) 全 path 確定 (機構レベル)**: 
1. S(HC) coherence = coherentEqualDegree_fromDade + S(HC) materialization (上記)。
2. S(C) coherence = (9.11)/(11.7) + S₂ glue。
3. (11.8.1)-(11.8.5) α-grid calc (no_real/pairwise_orthogonal + α^τ inners + τ₁ 消費)。
4. (11.3) 矛盾。

機構は完全確定。残 = S(HC) materialization (次) → S₂ → calc。深い multi-session endgame だが各 API は特定済。

## 2026-06-29 update¹⁰ (lane-a) — 🛑 honest stall flag: (11.8) endgame は dedicated effort 要

**正直な評価 (要ユーザー判断)**: この session で (11.8) の **foundation (9 feat commits) + 完全機構確定**を
達成したが、endgame の core = **S(HC) full materialization** (degree-q 既約族を Frobenius (U/C)⋊W₁ /
§6 columnFamily から enumerate + coherentEqualDegree_fromDade の preconditions 確立) を **~7 反復 build
できず** (investigation/mapping に終始)。これは §6/Frobenius char theory の深い construction で、bloated な
loop 反復では production 不能。[[feedback-flag-poor-progress]] に従い churning を止め flag する。

**完了済 (build-green, committed)**:
- (11.8) `exists_zeta_residual_not_orthogonal`: 実 ζ witness 供給 + params/by_contra 構造。
- `inducedFamily_hasNoRealCharacters` (9-lemma chain) + `inducedFamily_pairwiseOrthogonal` (inducedFamily の
  真の character 事実、(11.8.x) calc が消費)。
- 全機構確定 (Dade-based、global S07.Hypothesis でない): coherence=coherentEqualDegree_fromDade /
  α^τ inners (muGridAlpha_tau_*) / 矛盾=S13.S_H0C_not_coherent。

**残 (deep multi-session、dedicated effort 推奨)**:
1. **S(HC) materialization** (bottleneck): degree-q 既約族 χ:Fin n→Irr(↥M) を §6 columnFamily /
   Frobenius count から enumerate。coherentEqualDegree_fromDade (S07:5968) に χ + equal-degree +
   supported-diff + n≥2 を渡す。**§6 framework (typePData_toS06Hypothesis 経由) との bridge が要点**。
2. S₂=S(C)−S(HC) coherence: (9.11)/(11.7)。
3. (11.8.1)-(11.8.6) α-grid calc: 上記 coherence の τ₁ + α^τ inners + no_real/pairwise (✅) で。
4. (11.3) 矛盾。

**要判断**: (11.8) endgame に dedicated focused session を割く (fresh /loop) か、lane-a を別 FT-path 作業へ
redirect するか。foundation + roadmap は本ノートに完備。

## 2026-06-29 update¹¹ (lane-a) — S(HC) coherence bridge **landed** (churn 脱却); 残 = enumeration のみ

update¹⁰ の「investigation churn」を脱し、**build-green な 2 commit** で S(HC) coherence の assembly を
materialize。coq `PFsection11.v` 併読で機構を確定 → 旧評価の「§6/Frobenius の深い再帰 stack」は**過大**と判明。

**landed (build-green, committed; leaf S12 3847 jobs)**:
1. **`Hypothesis.inducedFamily_sub_support`** (commit 3dede22f): `inducedFamily M` の任意の**等次数 2 元**
   `ζ₁,ζ₂` (ζ₁(1)=ζ₂(1)) の差 `ζ₁−ζ₂` が `A₀`-supported。`zeta_sub_conj_support` を一般化 (後者は
   conjugate-pair 特例として本補題に還元)。`coherentEqualDegree_fromDade` の `hsuppdiff` 前提そのもの。
2. **`Hypothesis.inducedFamily_isCoherent_of_equalDegreeFamily`** (commit 27481ebd): 等次数単射族
   `χ:Fin n→Irr(M)` (n≥2, 各 χⱼ∈inducedFamily, 同次数) → `IsCoherent hyp.tau (range χ) hyp.A0` を構成する
   `noncomputable def`。`coherentEqualDegree_fromDade` の**全前提を §10 Hypothesis から opaque field なしで
   discharge** (基底 map=hyp.tau 定義的一致 / support=hyp.A0 定義的一致 / hsuppdiff=上記① / 1∉A₀=
   `S04.Hypothesis.ne_one`)。

**coq 併読で確定した機構** (`PFsection11.v`):
- L607 `cohS1 : coherent S1 M^# tau := uniform_degree_coherence scohS1` — **S1=S(HC) coherence は uniform
  (equal) degree から直接**。= 本 Lean bridge `inducedFamily_isCoherent_of_equalDegreeFamily` (機構一致確認)。
- L206-208 `FTtype34_noncoherence` ((11.3)): S(H₀C) coherent ⟹ full S(1) coherent ⟹ `FTtype345_noncoherence`
  ((10.8)) と矛盾。⟹ (11.8) の contradiction target は **(10.8) full-S non-coherence** に bottom-out。
- L660 `cohS2 := subset_coherent (Ptype_core_coherence …)` — S2=S(C)−S(HC) coherence。

**残 = S(HC) enumeration のみ** (genuine だが scope 明確、bridge に渡すだけ):
- S(HC) = inducedFamily M の **degree-w₁ かつ既約**な元 = `{Ind θ | θ∈Irr(M') linear, θ≠1, θ が全 chiRestrict
  column を avoid}` を M-conjugacy で割った代表系を `Fin n→Irr(↥M)` に並べる。⚠ **inducedFamily は reducible な
  Ind θ も含む** (Ind θ 既約 ⟺ θ が column avoid、`exists_zeta_in_inducedFamily_degree_w1` の `havoid` 論法)、
  S(HC) は既約 degree-w₁ 元のみ。injective には M-orbit 代表系が要 (Clifford: Ind θ_i=Ind θ_j ⟺ θ_j∈orbit(θ_i))。
- n≥2 は conjugation-closure (ζ̄∈S(HC), 奇数位数で ζ̄≠ζ) で自動。
- S07 coherence producer は全て **Fin n-indexed** (set-level uniform-degree 版は repo に無し、確認済) ゆえ
  enumeration は回避不能。これが genuine な残工。

**次**: S(HC) enumeration (degree-w₁ 既約 subfamily の Fin n 化)。bridge は landed ゆえ、enumerate さえ
すれば S(HC) coherence が出る。その後 S₂ + glue + α-grid calc + (10.8) 矛盾。

## 2026-06-29 update¹² (lane-a) — 🎉 S(HC)=S₁ coherence **完全 materialized** (bottleneck 突破)

update¹⁰ で「deep multi-session, dedicated effort 要」と flag した **S(HC) materialization を sorry-free で
landed** (commit 5fdc6f12)。enumeration の「Clifford 数え上げ」評価は**過大**だった — **束ね型 IrreducibleCharacter
は単なる subtype** `{φ // IsIrreducibleCharacter φ}` ゆえ bundling は自由、**Finset.equivFin で injective Fin n 化が
自動** (M-orbit 明示不要)。

**`Hypothesis.SHC_isCoherent`** (S12, sorry-free):
`IsCoherent hyp.tau {φ | φ∈inducedFamily M ∧ IsIrreducibleCharacter φ ∧ φ(1)=w₁} hyp.A0`。
- degree-w₁ 既約 ∩ inducedFamily の Finset を `Finset.univ.filter` で取り `equivFin` で Fin n 化。
- bridge `inducedFamily_isCoherent_of_equalDegreeFamily` (前 commit) に渡す。
- n≥2 = {ζ,ζ̄} (`exists_zeta_in_inducedFamily_degree_w1` + `inducedFamily_hasNoRealCharacters` で distinct)。
- range = S₁ identity を Set.ext で示し transport。Prop ∃-elim は hcard (Prop) 内に閉込め (goal=Type)。
= coq `cohS1 := uniform_degree_coherence scohS1` (PFsection11 L607)。

**残 (11.8) endgame (S₁ coherence は供給済)**:
1. **S₂=S(C)−S(HC) coherence** (unconditional、coq L660 `cohS2 := subset_coherent (Ptype_core_coherence)`):
   Lean (9.11) `coherent_H0C_commutator` (S11) + (11.7)。S₁ と同様の materialization を S₂ にも。
2. **union glue** S(C)=S₁∪S₂: `coherentUnion_of_glued`/`coherentPairChain` (S07)。glue 条件は α-grid calc が供給。
3. **α-grid calc** (11.8.1)-(11.8.6): by_contra (residual⊥) → glue 条件確立 (α^τ inner lemmas `muGridAlpha_tau_*`
   消費)。これが残る genuine multi-step character calc。
4. **矛盾**: S(C) coherent → S(H₀C) coherent → (11.3)/(10.8) 矛盾。

本 session = 4 commit (3 Lean: inducedFamily_sub_support / _isCoherent_of_equalDegreeFamily / SHC_isCoherent
+ note)。update¹⁰ の churn (0 commit/7 反復) を脱し flagged bottleneck を突破。

## §9 char-gate 前進 (2026-07-02, lane-a) — 11.8.1/11.8.6 の μ_j(1)=qu gate クリア
lane-a が §9 (repo S11) の (11.8.1)/(11.8.6) char-gate を landing (全 axiom-clean):
- **(11.8.1) d=u gate**: `caseA_reducible_induceHU_apply_one_eq_qu` (9.8.b) + `caseB_degree_qu` (9.9.a) で
  μ_j(1)=qu 確立。μ_{ij}(1)=u (q 個の和) は §10 carrier 側で d=μ_{ij}(1) に接続要。
- **(11.8.6) μ_k∈S₂ gate**: `caseA_character_counts` conjunct(b) + `caseB_character_counts` conjunct(b)
  (= `reducible_mem_sOf_H0C` case-agnostic) で reducible μ_k ∈ 𝒮(H₀C) 確立 (9.8.b/9.9.b)。
- **9.8.c 存在**: `caseA_exists_irreducible_sOf_H0C` (𝒮(H₀C) に irr degree-qu) landed — 例外(9.10) trigger の
  否定側 (non-exceptional) を caseA で供給。

**∴ 11.8 の §9-char gate は substantially cleared** (残 §9 = 9.11 coherence = §14/lane-b gated、
9.8.d/9.9.c = hub-frozen Galois = 11.8 本体には不要)。

### 11.8 残 gate (次 iteration frontier、carrier 側)
1. **S(HC)/S₂ carrier 材料化**: S13 `OrthogonalityData` の S1/S2 + `hyp.SOf` opaque field を §9 の
   `sOf`/`xiOf` (S11、materialized) と bridge。§10 muGrid/tau carrier ↔ §11 Hypothesis の `hyp.base`。
2. **(11.8.1) d=u 接続**: §10 `CharacterParameters.d` = μ_{ij}(1) を §9 μ_j(1)=qu / μ_{ij}(1)=u に接続。
   δ=1,n=(u−1)/q は Frobenius (U/C)⋊W₁ の u≡1 mod q (要 carrier)。
3. **(11.8.2)-(11.8.3)** σ/α 算術: `muGridAlpha_tau_inner_self` (‖α^τ‖²=2+n² ✅) + §4/§5 cite。
4. **(11.8.4)** landed (10.9) 直結 (`residual_alignedOmegaSigma_inner_eq_zero_of_w1_lt_w2` ✅)。
5. **(11.8.5)-(11.8.6)** 矛盾導出: a=0 + S₂ coherence (9.11=§14 gate) + (11.3) `S_H0C_not_coherent` ✅。

**次 iteration 着手** = carrier bridge (S(HC)/S₂ 材料化) or (11.8.1) d=u 接続 (§9 landed ゆえ最短)。

## 2026-07-02 cont.²⁴ (lane-a) — 🎯 concrete next-build target pinned = `muGrid i j 1 = u`

S10 §8 structural work (8.2.a/8.6.b II) landed this session; re-examined (11.8) frontier and pinned
the **exact next buildable lemma** (次 iteration = BUILD、survey しない):

**(11.8.1) d=u connection reduces to `hyp.muGrid hG hodd i j 1 = u` (j≠0)**:
- `params.d := μ_{ij}(1)` (via `degree_independent`, producer `exists_charParameters_full` S12:3179 sets
  `d` from `exists_charParamArith`). `muGrid_apply_one_eq` (S12:2029) proves μ_{ij}(1) は **constant** across
  (i,j) j≠0 — but NOT the value.
- 残 = **value bridge**: §9 landed `μ_j(1)=qu` (column sum, `caseA_reducible_induceHU_apply_one_eq_qu` /
  `caseB_degree_qu`, S11) を §10 muGrid 表現に接続。column μ_j=∑_i μ_{ij}, 各項 constant=d ⟹ μ_j(1)=w₁·d.
  w₁=q (type III/IV, |W₁|=q) ⟹ q·d=qu ⟹ d=u。要: (a) μ_j(1)=w₁·d の §10 muGrid 形、(b) μ_j(1)=qu の §9→§10
  carrier 接続 (muGrid_apply_one_within_column/_cross_column S12 ↔ §6 columnFamily ↔ §9 sOf degree)、(c) w₁=q。
- trace 起点: `muGrid` def S12:1308 (§10→§6 bridge via `toCertainTypeHypothesis`→`columnFamily`);
  `muGrid_apply_one_within_column`/`_cross_column` (2029 の内部) が §6 columnFamily degree に接続する箇所。

**(11.8) 全体の gate 再確認** (post SHC_isCoherent + §9 gate landing):
- S₁=S(HC) coherence ✅ (`SHC_isCoherent` landed)。
- S₂=S(C)−S(HC) coherence = (9.11)`coherent_H0C_commutator`(S11 sibleyTarget_H0C sorry)+(11.7) = **§14/lane-b gated**。
- α-grid calc (11.8.2-3) = S₁-τ₁ 版 α-lemma 群が要 (既存 `muGridAlpha_tau_*` は full-S coh 要求で by_contra 不可)。
- ∴ (11.8) full closure は S₂ leg で §14-gated。だが d=u / α-grid S₁-τ₁ lemma は ungated で先行 build 可。

**教訓 (honest)**: cont.²⁴ は survey 過多 (0 code)。次 iteration は本ノートの `muGrid i j 1 = u` から
**即 build 着手** (再 survey 禁止)。carrier trace は muGrid_apply_one_within_column の §6 接続を読むところから。

## 2026-07-02 cont.²⁵ (lane-a) — ユーザー裁定「α-grid S₁-τ₁ を継続 grind」; cont.²⁴ muGrid pin は dead-end

**cont.²⁴ の `muGrid i j 1 = u` pin は dead-end 確認**: `columnFamily := (exists_columnSignedFamily χ₂).choose`
(S06_CertainTypeCharacters:432) = **existential-choice**。`.mu` の絶対次数は construction で pin されず
(`columnFamily_difference_apply_one` は差=0 のみ)。∴ d=u は existential 次数を u に接続する deep 別論法要 =
単一 lemma 不可。→ このルートは凍結。

**ユーザー裁定 (AskUserQuestion)**: 「**α-grid S₁-τ₁ を継続 grind**」。SHC_isCoherent で unblock された
未着手 piece を反復 build。payoff は §14-gated (S₂ coherence) だが on-cluster prerequisite として積む。

**pinned 次 build target = S(HC)-coherence 版 α^τ 分解 (11.8.2)**:
- **foundation available ✅**:
  - `muGridAlpha_tau_inner_self` (S12:3349): `‖α_{ij}^τ‖² = 2 + n²` — **coh-FREE** (hyp.tau のみ、full-coh 不要)
    ゆえ by_contra で直接使える。
  - `SHC_isCoherent` (S12, landed): `IsCoherent hyp.tau {φ∈inducedFamily|irr∧φ(1)=w₁} A0` = S₁=S(HC) の
    τ₁ coherent 拡張。ζ (degree w₁ 既約 ∈ inducedFamily) ∈ この S(HC) family。
- **target lemma** (新規、S₁-τ₁ 版): `tau_muGridAlpha_eq` (S12:4359、**full-coh 要求**の分解
  `α^τ = δ·(ω_{ij}^σ−ω_{i0}^σ) − n·coh.tau1 ζ`) の **SHC-coherence 版**。by_contra では full `coh` 無 →
  SHC_isCoherent の τ₁ (S(HC) 上) で `α_{ij}^τ = X − n·ζ^{τ₁} + a·∑_{λ∈S₁}λ^{τ₁}` (X⊥S₁^{τ₁}, a∈{0,1,2})
  を導出 ((11.8.2))。‖α^τ‖²=2+n² (coh-free) + S(HC) 直交性 (`inducedFamily_pairwiseOrthogonal` ✅) で
  a=0 or 2、a=0 ⟹ X=ω_{ij}^σ−ω_{i0}^σ ((11.8.5))。
- **next iteration = BUILD** this α-decomposition (survey 済、foundation 確認済)。SHC_isCoherent の τ₁ API
  (`CoherentHypothesis.tau1` 相当の SHC 版) を読み、ζ^{τ₁} と α^τ の inner を muGridAlpha_tau_inner_self の
  proof 構造で組む。§14-gate (S₂) は最後の union でのみ効く (α 分解自体は ungated)。

## 2026-07-02 cont.²⁶ (lane-a) — 🔨 first α-grid S₁-τ₁ building blocks LANDED (grind 実行)

ユーザー裁定「α-grid S₁-τ₁ grind」を実行、build-light 連続を脱し **2 lemma landed** (S12、leaf green):
- **`Hypothesis.SHC_extension_inner_self`**: `‖ζ^{τ₁}‖²=1` for `S(HC)`-coherence τ₁
  (`SHC_isCoherent.extension`)。full-coh `zeta_tau1_inner_self` の SHC 版 (by_contra で full coh 無でも使える)。
  proof = `extension_inner_eq` (isometry) + `irr_cf_inner`。
- **`Hypothesis.muGridAlpha_tau_inner_SHC_extension_mem_int`**: `⟨α_{ij}^τ, ζ^{τ₁}⟩ ∈ ℤ` (integrality)。
  coh-free `muGridAlpha_tau_mem_ZIrr` (α^τ∈ZIrr) + `extension_mem_ZIrr` (ζ^{τ₁}∈ZIrr) + `inner_mem_ZIrr_int`。
- **⚠ instance gotcha 解決** ([[lean-induce-transport-instance-desync]]): `open scoped FiniteInduce in` で
  Fintype↥M/Invertible を carrier (SHC_isCoherent 内部 = `FiniteInduce.finiteSubFintype`) と統一。explicit
  `[Fintype ↥M]` は "synthesized ≠ inferred" mismatch。open は docstring の**前**に置く。

**axiom profile (honest)**: 両 lemma は literal sorry 無 (honest 完全証明) だが **transitive sorryAx あり** —
`muGrid`/`SHC_isCoherent` が S12 自身の §10→§6 carrier bridge sorry (`typePData_toS06Hypothesis` S12:1113、
`typePData_WEquiv_mem_W2` S12:1011) に依存。これは genuine な deferred lane-a prerequisite (vacuous scaffold
でない) ゆえ cite 正当 ([[feedback-cite-sorried-lemmas-if-signature-correct]])。§8.2.a/8.6.b II の clean 群論と
違い、char endgame は sorried carrier 上に積む (回避不能)。

**次 = (11.8.2) a=0 導出** (これらを消費): `‖α^τ‖²=2+n²` (`muGridAlpha_tau_inner_self` coh-free ✅) +
上記 integrality + S(HC) 直交 (`inducedFamily_pairwiseOrthogonal` ✅) で α^τ を S₁^{τ₁} basis に分解、
a∈{0,1,2}、a=0 or 2、a=0 ⟹ X=ω_{ij}^σ−ω_{i0}^σ ((11.8.5))。μ_k^{τ₁} 経由 (S(HC) 外) を避ける新 CS 論法。

## 2026-07-02 cont.²⁷ (lane-a) — S(HC)^{τ₁} orthonormal basis API 完成 (pairwise-orth landed)
- **`Hypothesis.SHC_extension_inner_of_ne`** landed (S12, leaf green): distinct S(HC) 既約 φ≠ψ で
  `⟨φ^{τ₁},ψ^{τ₁}⟩=0` (extension_inner_eq isometry + irr_cf_inner + if_neg)。
- ∴ **{φ^{τ₁} : φ∈S(HC)} は orthonormal** (norm 1 = cont.²⁶ `SHC_extension_inner_self` + pairwise 0 = 本 lemma)。
  (11.8.2) の α^τ 分解が projection する S₁^{τ₁} basis。integrality (cont.²⁶) と合わせ **α-grid S₁-τ₁ の
  inner-product API 3 本完備**。transitive sorryAx は SHC_isCoherent 経由 (cont.²⁶ と同、genuine deferred)。

**次 = (11.8.2) a=0 projection** (orthonormal API を消費):
- α^τ = X − nζ^{τ₁} + a∑_{λ∈S₁}λ^{τ₁}, X⊥S₁^{τ₁}, a∈{0,1,2}。projection 係数 = ⟨α^τ,λ^{τ₁}⟩ (orthonormal ゆえ)。
- 要 **ω^σ ⊥ S₁^{τ₁}**: full-coh は (5.5) `ofProjection` (coh.tau1, ψ=0) で ω^σ⊥coh.tau1 (S12:4869)。
  SHC 版は SHC.extension に対する ofProjection 適応が要 (§5 (5.5)/(5.3.b) が SHC-coherence で効くか確認)。
- 要 **‖α^τ‖²=2+n²** (`muGridAlpha_tau_inner_self` coh-free ✅) + norm 展開で a²·|S₁|+… ≤ 2 → a∈{0,1} → integrality で a=0。
- 次 iteration = ω^σ ⊥ SHC.extension (5.5 ofProjection) の tractability 確認 → a=0 projection。

### cont.²⁷ 追記 — (5.5) ofProjection は SHC に transfer しない; a=0 は fixed-vector projection
scoped (5.5) `ofProjection`/`eq_sum_of_psi_eq_zero` (S07:1224/1561): `μ_j^{tau1}` を R(μ_j) image family
に projection。**tau1 が μ_j に定義要** ⟹ full-coh (coh.tau1 on all S) は可、**SHC.extension (S(HC) 上のみ、
μ_j∉S(HC)) は不可**。∴ full-coh a=0 machinery (`columnImageFamily`+ofProjection) は SHC 非適応 (plan 既知障害を code 確認)。

**SHC a=0 の正しい形** = fixed vector `α^τ = hyp.tau α` (coh-free, α supported ゆえ定義) を **S₁^{τ₁} 部分空間
(span{λ^{τ₁}:λ∈S(HC)}, orthonormal API 完備) に projection**:
`α^τ = (⊥S₁^{τ₁} 成分) + ∑_{λ∈S(HC)} ⟨α^τ,λ^{τ₁}⟩·λ^{τ₁}`。
(11.8.2) 主張 = ⟨α^τ,ζ^{τ₁}⟩=-n+a、⟨α^τ,λ^{τ₁}⟩=a (λ≠ζ、**uniform**)。
- **crux = ⟨α^τ,λ^{τ₁}⟩ の λ 一様性**: なぜ全 λ∈S(HC)\{ζ} で同値 a か (Peterfalvi 構造論拠、要精読 04.11 (11.8.2))。
- norm: ‖α^τ‖²=2+n² = ‖⊥成分‖² + ‖-nζ^{τ₁}+a∑λ^{τ₁}‖² (orthonormal) = ‖⊥‖² + (n²·? + a²·|S₁| + cross) → a bound。
- 次 iteration = 04.11 (11.8.2) 原文で uniformity 論拠を確認 → projection lemma。orthonormal API (norm1/pairwise0/int) は消費準備済。

## 2026-07-02 cont.²⁸ (lane-a) — (11.8) 原文精読 + SHC (5.3.b) bridge landed
04.13 (11.8) 原文精読 ([MISSING_PAGE_FAIL:3] = 11.8.2-11.8.4 は落丁だが 11.8.5/11.8.6 は取得):
- **(11.8.5) a=0 構造**: `((μ_0−ζ)^τ,α_{ij}^τ)` を τ-isometry で source ((μ_0−ζ,α_{ij})=−1+n) と等置
  → `a=(∑ω_{r0}^σ,β)`。β=a∑_{λ∈S₁}λ^{τ₁} (11.8.2 の X=ω_{ij}^σ−ω_{i0}^σ 後)。**(5.3.b) ω^σ⊥S₁^{τ₁}**
  ⟹ a=(∑ω^σ,a∑λ^{τ₁})=0。β real ⟹ a even も併用。
- **key tool 発見**: `inner_left_eq_zero_of_inner_sub_eq_zero` (S12:4214、汎用): norm-1 ZIrr a,b,s で
  a⊥b ∧ (a−b)⊥s ⟹ a⊥s (integral geometry ‖s−xa−xb‖²=1−2x²≥0 ⟹ x=0)。(5.3.b) を R(ζ) machinery
  回避で出す。full-coh `tau1_zeta_vanishes_on_typePV` (4269) が内部で ⟨ζ^{τ₁},ω^σ⟩=0 をこれで出す。

**landed (S12, leaf green)**: **`Hypothesis.tau_zeta_sub_conj_eq_SHC_extension`** — SHC 版
`hyp.tau(ζ−ζ̄) = SHC.extension ζ − SHC.extension ζ̄` (extends_on_supported、ζ−ζ̄∈ℤ[S(HC),A₀] supported)。
full-coh `tau_zeta_sub_conj_eq_tau1` の SHC 版。**SHC (5.3.b) の必須 ingredient** (a−b=ζ^{τ₁}−ζ̄^{τ₁}=hyp.tau(ζ−ζ̄))。

**次 = SHC (5.3.b) 完成** `⟨ω^σ, SHC.extension λ⟩=0`: `inner_left_eq_zero_of_inner_sub_eq_zero`
(a=SHC.ext λ, b=SHC.ext λ̄, s=ω^σ) + orthonormal API (norm1/pairwise0 ✅) + 本 bridge +
coh-free `tau_zeta_sub_conj_vanishes_on_typePV`/sigmaNC≤2 (tau1_zeta_vanishes の SHC 複製)。
これで (11.8.5) a=0 が組める。(11.8.6) は S₂ coherence (§14-gated) 残。

## 2026-07-02 cont.²⁹ (lane-a) — 🎯 SHC (5.3.b) LANDED — `⟨ω^σ, ζ^{τ₁}⟩=0` (11.8.5 a=0 の core)
**`Hypothesis.SHC_extension_inner_alignedOmegaSigma_eq_zero`** landed (S12, leaf green):
`⟨SHC.extension ζ, alignedOmegaSigmaGrid i j⟩=0` (ζ∈S(HC) degree-w₁ 既約)。
`tau1_zeta_vanishes_on_typePV` の中間 (vanishing-on-V の手前) を SHC に port:
- `exists_alignedOmegaSigmaGrid_chiFam_family` で ω_{ij}^σ=chiFam(P j) (同一 tic/canonicalFullDadeApp)。
- 差 ζ^{τ₁}−ζ̄^{τ₁}=(ζ−ζ̄)^τ (cont.²⁸ bridge) の σ-coeff は sigmaNC≤2<min(w₁,w₂) (各 norm-1 で ≤1、
  `ncard_inner_chiFam_ne_zero_le_one`) ⟹ `sigmaCoeff_eq_zero_of_sigmaNC_lt` で ⟨差,χ_{P j}⟩=0。
- `inner_left_eq_zero_of_inner_sub_eq_zero` (orthonormal API: norm1/pairwise0) で ⟨ζ^{τ₁},χ_{P j}⟩=0。
transitive sorryAx は SHC/muGrid 経由 (genuine deferred)。

**これで (11.8.5) a=0 の (5.3.b) 依存が解消**。残 a=0 pieces:
- (11.8.2) α^τ 分解 `α_{ij}^τ = X − nζ^{τ₁} + a∑λ^{τ₁}` (X⊥S₁^{τ₁}, a∈{0,1,2}) — projection + norm。
- τ-isometry reduction `((μ_0−ζ)^τ,α_{ij}^τ)=(μ_0−ζ,α_{ij})=−1+n` → `a=(∑ω^σ,β)`。
- β real ⟹ a even、+ (5.3.b) ⟹ a=0。
**次 iteration = (11.8.2) 分解 or a=(∑ω^σ,β) の isometry reduction を組む** (5.3.b 済で a=0 に王手)。

## 2026-07-02 cont.³⁰ (lane-a) — 📄 MISSING PAGE 復元: (11.8.2)-(11.8.6) 完全 proof (PDF p.66-67)
04.13 mmd の `[MISSING_PAGE_FAIL:3]` (= 11.8.2-11.8.4) を PDF `04.13...pdf` p.66-67 から復元
([[nougat-missing-page-recovery]])。**(11.8) 完全 proof roadmap 確定**:

**(11.8.1)** d=u,δ=1,n=|S₁|=(u−1)/q。μ_j(1)=qu (9.8/9.9)→d=μ_{ij}(1)=u。(U/C)⋊W₁ Frobenius→u≡1 mod q→δ=1,n=(u−1)/q。

**(11.8.2)** α_{ij}^τ = X − nζ^{τ₁} + a∑_{λ∈S₁}λ^{τ₁}, X∈ℤ[Irr G]⊥S₁^{τ₁}, a∈{0,1,2}; a=0 or 2 ⟹ X=ω_{ij}^σ−ω_{i0}^σ。
proof: λ∈S₁,λ≠ζ で (α_{ij}^τ,(ζ−λ)^τ)=(α_{ij},ζ−λ)=−n [isometry+source]。∴ ∃a∈ℤ,X⊥S₁^{τ₁} で分解。
norm: **(a−n)²+(|S₁|−1)a² = ‖−nζ^{τ₁}+a∑λ^{τ₁}‖² ≤ ‖α_{ij}^τ‖²=n²+2**。→ |S₁|a²−2an≤2 → n(a²−2a)≤2 (11.8.1) → 0≤a≤2。
a=0 or 2 → ‖−nζ^{τ₁}+a∑λ^{τ₁}‖²=n² → ‖X‖²=2 → (10.5 と同様) X=ω_{ij}^σ−ω_{i0}^σ。

**(11.8.3)** β=α_{ij}^τ−(ω_{ij}^σ−ω_{i0}^σ)+nζ^{τ₁} は i,j 独立 (j≠0)、real。
proof: (α_{ij}−α_{ik})^τ=(μ_{ij}−μ_{ik})^τ=ω_{ij}^σ−ω_{ik}^σ [(4.8)] → β_{ij} j 独立。
(α_{ij}−α_{0j})^τ=ω_{ij}^σ−ω_{i0}^σ−ω_{0j}^σ+ω_{00}^σ [(4.10)] → β_{ij}=β_{0j} i,j 独立。real: β̄_{0j}=β_{0k}=β [(3.9.a),(4.3.b),(5.9)、ω̄_{0j}=ω_{0k}]。

**(11.8.4)** [背理法: residual⊥(Irr W)^σ 仮定下] (μ_0−ζ)^τ=∑_{0≤i<q}ω_{i0}^σ−ζ^{τ₁} と仮定してよい。
proof: (μ_0−ζ)^τ=∑ω_{i0}^σ−χ と置く。‖χ‖²=‖μ_0−ζ‖²−q=1。((μ_0−ζ)^τ,(ζ̄−ζ)^τ) 考察 → χ=ζ^{τ₁} or −ζ̄^{τ₁}。
|S₁|>2,λ∈S₁−{ζ,ζ̄} で ((μ_0−ζ)^τ,(λ−ζ)^τ)=1 → χ=ζ^{τ₁}。|S₁|=2,χ=−ζ̄^{τ₁} なら ζ^{τ₁},ζ̄^{τ₁} を −ζ̄^{τ₁},−ζ^{τ₁} に置換。

**(11.8.5)** a=0。((μ_0−ζ)^τ,α_{ij}^τ)=(∑ω_{r0}^σ−ζ^{τ₁}, β+ω_{ij}^σ−ω_{i0}^σ−nζ^{τ₁})=(∑ω_{r0}^σ,β)−1−a+n。
(μ_0−ζ,α_{ij})=(∑μ_{r0}−ζ,μ_{ij}−μ_{i0}−nζ)=−1+n。isometry で等置 → a=(∑ω_{r0}^σ,β)。
(β,1_G)=(α_{ij}^τ,1_G)=(α_{ij},1_M)=0 (i≠0)。β real → a even。(11.8.2) → X=ω^σ diff → β=a∑λ^{τ₁}。
(5.3.b) → a=(∑ω_{r0}^σ,β)=0。 ✅ **(5.3.b)=cont.²⁹ landed**。

**(11.8.6)** [結論] α_{ij}^τ=ω_{ij}^σ−ω_{i0}^σ−nζ^{τ₁} (∀i, by 11.8.2+11.8.5)。→ (μ_j−dζ)^τ=∑_iω_{ij}^σ−dζ^{τ₁}。
S₂=S(C)−S(HC)。(9.11)→S₂ coherent (11.7)、μ_k∈S₂ (9.8.b/9.9.b)。τ₂ extends τ to ℤ[S₂]。(5.3.b)+(5.5)→S₁^{τ₁}⊥S₂^{τ₂}。
(μ_j−dζ)^τ=μ_j^{τ₂}−dζ^{τ₁} なら S(C)=S₁∪S₂ coherent → (11.3) 矛盾。∴ μ_j^{τ₂}=∑_iω_{ij}^σ を示せば十分 [(4.9)/(5.8)]。
**⚠ (11.8.6) は S₂ coherence=(9.11)=§14/lane-b gated**。

### 攻略順 (次 iteration〜、ungated 部)
1. **(11.8.2)** 分解+norm (最大): source inner (α_{ij},ζ−λ)=−n / ‖α^τ‖²=2+n² (✅) + orthonormal projection + a∈{0,2}→X=ω^σ diff。
2. **(11.8.3)** β 独立+real: (4.8)/(4.10) 系 + (3.9.a)/(4.3.b)/(5.9)。
3. **(11.8.4)** residual 仮定→(μ_0−ζ)^τ 形: norm+isometry。
4. **(11.8.5)** a=0: 1-3 + (5.3.b ✅) + source inner (μ_0−ζ,α_{ij})=−1+n + (β,1_G)=0。
5. **(11.8.6)** = §14-gated (S₂), 前倒し skeleton 可。

## 2026-07-02 cont.³¹ (lane-a) — (11.8.2) source input landed: ⟨α_{ij}, ζ−η⟩=−n (∀η∈S(HC),η≠ζ)
**`Hypothesis.muGridAlpha_inner_zeta_sub_irr`** landed (S12, leaf green): 任意の degree-w₁ 既約
η∈S(HC), η≠ζ で `⟨α_{ij}, ζ−η⟩ = −n` (coh-free source)。既存 `muGridAlpha_inner_zeta_sub_conj`
(η=ζ̄ 特例) の一般化 — η(1)=ζ(1) ゆえ μ_{ij},μ_{i0}⊥η (degree distinctness
`muGrid_inner_eq_zero_of_apply_one_ne`)、(ζ,η)=0 (η≠ζ)、−nζ 項のみ残る。
(11.8.2) projection の ζ^{τ₁}-係数を −n に pin (isometry lift 後)。

**次 = (11.8.2) 残**: isometry lift `⟨α_{ij}^τ,(ζ−η)^τ⟩=−n` (tau_inner_eq_of_supported、ζ−η supported)
+ orthonormal projection (α_{ij}^τ = X−nζ^{τ₁}+a∑λ^{τ₁}、係数 a、X⊥S₁^{τ₁}) + norm bound
((a−n)²+(|S₁|−1)a²≤n²+2 → a∈{0,1,2}) + a∈{0,2}→X=ω^σ diff (‖X‖²=2)。

## 2026-07-02 cont.³² (lane-a) — (11.8.2) 係数構造 landed (general bridge + coefficient relation)
2 lemma landed (S12, leaf green):
- **`Hypothesis.tau_sub_eq_SHC_extension`**: 一般 `(ζ−η)^τ = ζ^{τ₁}−η^{τ₁}` (ζ,η∈S(HC) degree-w₁ 既約)。
  cont.²⁸ bridge (η=ζ̄) の一般化 (inducedFamily_sub_support で同次数差 A₀-supported)。
- **`Hypothesis.muGridAlpha_tau_inner_SHC_extension_sub`**: `⟨α^τ,ζ^{τ₁}⟩−⟨α^τ,η^{τ₁}⟩=−n` (∀η∈S(HC),η≠ζ)。
  = general bridge + tau_inner_eq_of_supported (isometry) + muGridAlpha_inner_zeta_sub_irr (cont.³¹ source −n)。
  ⟹ **projection 係数構造**: c_η:=⟨α^τ,η^{τ₁}⟩=a (η≠ζ で constant)、c_ζ=a−n。
  ∴ α^τ = X − nζ^{τ₁} + a∑_{λ∈S₁}λ^{τ₁} (X⊥S₁^{τ₁})。

**次 = (11.8.2) 残 = orthonormal projection + norm bound**:
- projection: X:=α^τ−∑_λ c_λ λ^{τ₁} ⊥ S₁^{τ₁} (orthonormal API); ‖α^τ‖²=‖X‖²+∑|c_λ|² (Parseval)。
- norm: ‖α^τ‖²=2+n² (`muGridAlpha_tau_inner_self` coh-free ✅) ⟹ (a−n)²+(|S₁|−1)a²≤2+n² ⟹ |S₁|a²−2an≤2
  ⟹ n(a²−2a)≤2 (n=|S₁|=(u−1)/q, 11.8.1) ⟹ a∈{0,1,2}。a∈{0,2}⟹‖X‖²=2⟹X=ω^σ diff (‖X‖²=2、10.5 同様)。

## 2026-07-02 cont.³³ (lane-a) — 🔑 (11.8.2) 鍵機構発見 `exists_intProjection_of_orthonormal_ZIrr` + injectivity
**鍵機構**: `ClassFunction.exists_intProjection_of_orthonormal_ZIrr` (InducedCharacter.lean):
`φ∈ZIrr, R:Finset(ZIrr) orthonormal → ∃ (c:·→ℤ)(Y), (∀α∈R,⟨φ,α⟩=c α) ∧ φ=∑_{α∈R}(c α)•α+Y ∧ ∀α∈R,⟨Y,α⟩=0`。
= **(11.8.2) 分解そのもの** (φ=α^τ, R={λ^{τ₁}:λ∈S(HC)})。整数係数 c + 直交剰余 Y=X を供給。
∴ (11.8.2) の「biggest load」= 手製 Bessel は不要、この機構に R を渡すだけ。

**landed**: `Hypothesis.SHC_extension_inj` — SHC.extension は S(HC) 上単射 (orthonormal: 像一致なら 1=⟨⟩=0 矛盾)。
R (={λ^{τ₁}} Finset) materialization の injectivity 要件。

**(11.8.2) 残 build plan (次〜)**:
1. **R materialization**: S(HC) Finset (SHC_isCoherent の `s=univ.filter p` 再利用) → `s.image SHC.extension` = R。
   hZ (extension_mem_ZIrr)、horth (SHC_extension_inner_self/of_ne + inj で if α=β then 1 else 0)、|R|=|S₁|=n。
2. **exists_intProjection** で φ=α^τ → c, Y。係数: c(ζ^{τ₁})=a−n, c(η^{τ₁})=a (cont.³² coefficient relation)。
3. **norm**: ‖α^τ‖²=∑_{α∈R}|c α|²+‖Y‖² (Y⊥R orthonormal Parseval) = (a−n)²+(n−1)a²+‖Y‖²。=2+n² (coh-free ✅)。
   ⟹ (a−n)²+(n−1)a²≤2+n² ⟹ n(a²−2a)≤2 (n≥2) ⟹ a∈{0,1,2}。
4. **a∈{0,2}⟹X=ω^σ diff** (‖X‖²=2、10.5 同様の grid_trichotomy)。

## 2026-07-02 cont.³⁴ (lane-a) — R materialization landed (11.8.2 projection 準備完了)
**`Hypothesis.exists_SHC_extension_orthonormal`** landed (S12, leaf green): S(HC)^{τ₁}={λ^{τ₁}:λ∈S(HC)}
を orthonormal ZIrr Finset R として materialize。∃R, hZ (∀β∈R,∈ZIrr) ∧ horth (∀α,β∈R,⟨α,β⟩=if α=β then 1 else 0)
∧ membership (λ∈S(HC)⟹SHC.ext λ∈R) ∧ reverse (β∈R⟹∃λ∈S(HC),β=SHC.ext λ)。
= S(HC) IrreducibleCharacter Finset (SHC_isCoherent と同 filter) の SHC.extension image。
orthonormal = SHC_extension_inner_self/of_ne + SHC_extension_inj (cont.³³)。
**⟹ exists_intProjection_of_orthonormal_ZIrr に R を渡す準備完了**。

**次 = exists_intProjection 適用 + norm bound**:
1. `exists_intProjection_of_orthonormal_ZIrr (α^τ∈ZIrr) hZ horth` → c:·→ℤ, Y, α^τ=∑_{β∈R}(c β)•β+Y, Y⊥R。
2. 係数: c(SHC.ext ζ)=a−n, c(SHC.ext η)=a (η≠ζ) — cont.³² coefficient relation + cont.²⁶ integrality。
3. norm: ‖α^τ‖²=∑_{β∈R}(c β)²+‖Y‖² (Parseval, Y⊥R orthonormal) = (a−n)²+(|R|−1)a²+‖Y‖²。
   |R|=|S(HC)|=n (image injective via SHC_extension_inj)。=2+n² (coh-free) ⟹ n(a²−2a)≤2 ⟹ a∈{0,1,2}。

## 2026-07-02 cont.³⁵ (lane-a) — ⚠ (11.8) は DOUBLY-gated 判明 + 算術核 landed (axiom-clean)
**重要な finding**: (11.8.2) の `a∈{0,1,2}` 結論は **(11.8.1) `|S(HC)|=n`** を要す (norm ineq
`(a−n)²+(|S₁|−1)a²≤n²+2` → `|S₁|a²−2an≤2` を `n(a²−2a)≤2` に変換するのに |S₁|=n が必要)。
`exists_charParamArith` (S12:2954) は n を **abstract** に産出 (n·w₁=d−δ, 2≤n のみ、n=|S(HC)| は baked-in でない)。
∴ |S₁|=n = (11.8.1) d=u,δ=1 = **§9↔§10 carrier bridge gated** (cont.²⁴ の muGrid-degree existential dead-end)。

**∴ (11.8) は DOUBLY-gated**:
- **§9↔§10** (11.8.1 |S₁|=n / d=u): μ_j(1)=qu (§9 landed) を §10 muGrid μ_j(1)=w₁·d に接続 = carrier 材料化 (deep)。
- **§14** (11.8.6 S₂ coherence = 9.11 sibleyTarget_H0C): lane-b/§14 gated。
ungated middle (11.8.2-11.8.5 の projection/norm/5.3.b machinery) は cont.²⁶-³⁴ で build 済 (11 lemmas)。

**landed (axiom-clean [propext,Classical.choice,Quot.sound]、sorryAx 無)**: `charParam_a_mem_of_norm_ineq`
— `n(a²−2a)≤2 ∧ 2≤n → a∈{0,1,2}` (整数算術核、char machinery 非依存ゆえ clean)。(11.8.2) の a∈{0,1,2} の数値核。

**次 iteration frontier 判断**: ungated norm decomposition (Parseval `‖α^τ‖²=∑c_β²+‖Y‖²` + inequality、
|S₁|=n を hypothesis 化して endpoint skeleton) を build 続行 (deferred-payoff) or §9↔§10 bridge (d=u) 攻略。
d=u = μ_j(1) の §9↔§10 接続で cont.²⁴ existential を回避できるか要再検 (μ_j(1)=w₁·d は symbolic、existential は
individual μ_{ij} value)。

## 2026-07-02 cont.³⁶ (lane-a) — Parseval-with-remainder landed (11.8.2 norm identity, axiom-clean)
**`inner_self_eq_sum_sq_add_of_intProjection`** landed (S12, leaf green): φ∈ZIrr を orthonormal ZIrr
family R に射影 (`exists_intProjection`) → c, Y (Y⊥R)、`‖φ‖² = ∑_{α∈R}(c α)² + ‖Y‖²` (Parseval)。
= `ZIrrFourier.inner_self_orthonormalSum_eq_sum_sq` + cross term 消去 (Y⊥R、inner_conj_symm)。
**general/reusable、axiom-clean** (φ,R を hypothesis 化ゆえ char machinery 非依存)。

**次 = (11.8.2) 組立**: φ=α^τ, R=exists_SHC_extension_orthonormal に本 Parseval 適用 →
‖α^τ‖²=∑c_β²+‖Y‖²。‖α^τ‖²=2+n² (coh-free)。∑c_β² 分割: c(SHC.ext ζ)=a−n (cont.²⁶ int + cont.³²),
c(SHC.ext η)=a (η≠ζ) ⟹ ∑c_β²=(a−n)²+(|R|−1)a²。⟹ (a−n)²+(|R|−1)a²≤2+n² ⟹ |R|a²−2an≤2。
|R|=n (=11.8.1 |S₁|=n、§9↔§10 gated) + `charParam_a_mem_of_norm_ineq` (cont.³⁵) ⟹ a∈{0,1,2}。

## 2026-07-02 cont.³⁷ (lane-a) — sum-split landed; (11.8.2) support 完備、次は full assembly
**`sum_sq_eq_of_split`** landed (S12, leaf green): e∈R, f e=x, ∀β∈R,β≠e→f β=y ⟹
`∑_{β∈R}(f β)²=x²+(|R|−1)y²` (general Finset、axiom-clean)。(11.8.2) の
`∑c_β²=(a−n)²+(|S₁|−1)a²` 評価用 (c(ζ^{τ₁})=a−n, 他=a)。

**(11.8.2) support 全部 landed** — full assembly の材料完備:
- Parseval-with-remainder (cont.³⁶): ‖α^τ‖²=∑c_β²+‖Y‖²。
- sum-split (本): ∑c_β²=(a−n)²+(|R|−1)a²。
- 算術核 (cont.³⁵): n(a²−2a)≤2 → a∈{0,1,2}。
- R materialization (cont.³⁴)、coefficient relation (cont.³²)、integrality (cont.²⁶)、‖α^τ‖²=2+n² (coh-free)。

**次 = full (11.8.2) assembly**: R+α^τ に Parseval → c,Y。coeff 同定 c(SHC.ext ζ)=a−n (cont.²⁶ int
+ cont.³² relation), c(SHC.ext η)=a (η≠ζ)。sum-split → ∑c_β²=(a−n)²+(|R|−1)a²。‖Y‖²≥0 (real part) +
‖α^τ‖²=2+n² ⟹ (a−n)²+(|R|−1)a²≤2+n² ⟹ |R|a²−2an≤2。|R|=n (11.8.1 gated) + 算術核 ⟹ a∈{0,1,2}。
⚠ 残 fiddly = ℂ→ℤ/ℝ 変換 (‖Y‖².re≥0)、|R|=n は §9↔§10 gated (hypothesis 化)。

## 2026-07-02 cont.³⁸ (lane-a) — ℂ→ℤ helper landed; (11.8.2) 全 support + helper 完備
**`int_le_of_add_inner_self_eq`** landed (S12, leaf green): `(A:ℂ)+⟨Y,Y⟩=(B:ℂ)` (A,B∈ℤ) ⟹ A≤B
(`inner_self_re_nonneg` で ⟨Y,Y⟩.re≥0、real part 取り)。Parseval 等式 ∑c_β²+‖Y‖²=‖α^τ‖² を
∑c_β²≤‖α^τ‖² に変換。⚠ `open scoped FiniteInduce in` 要 (inner over G の Fintype)。

**(11.8.2) full assembly の材料 全 landed**:
- Parseval-with-remainder (cont.³⁶)、sum-split (cont.³⁷)、算術核 (cont.³⁵)、ℂ→ℤ helper (本)。
- R materialization (cont.³⁴)、coefficient relation (cont.³²)、integrality (cont.²⁶)、‖α^τ‖²=2+n² (coh-free)。

**次 = full (11.8.2) assembly (一気に組む)**:
1. R := exists_SHC_extension_orthonormal。α^τ∈ZIrr (muGridAlpha_tau_mem_ZIrr)。
2. Parseval → c, Y, ‖α^τ‖²=∑c_β²+‖Y‖², ∀β∈R,⟨α^τ,β⟩=c_β。
3. a := c(SHC.ext ζ)+n。coeff 同定: c(SHC.ext ζ)=a−n (def)、∀η∈S(HC),η≠ζ→c(SHC.ext η)=a (cont.³² relation)。
4. sum-split (e=SHC.ext ζ, x=a−n, y=a): ∑c_β²=(a−n)²+(|R|−1)a²。
   ⚠ sum-split の hy: ∀β∈R,β≠SHC.ext ζ→c_β=a は reverse (β=SHC.ext η) + inj (η≠ζ) + cont.³² で。
5. ‖α^τ‖²=2+n² (coh-free) → (a−n)²+(|R|−1)a²+‖Y‖²=2+n² → ℂ→ℤ helper → (a−n)²+(|R|−1)a²≤2+n²。
6. |R|=n (11.8.1、hypothesis 化 or S(HC) Finset card=n) → n(a²−2a)≤2 → 算術核 → a∈{0,1,2}。

## 2026-07-02 cont.³⁹ (lane-a) — **full (11.8.2) `a∈{0,1,2}` assembly LANDED (sorry-free body)**
**`Hypothesis.muGridAlpha_tau_proj_a_mem`** landed (S12:7512, leaf green 3850 jobs). 上記 6 段を一気に
組んだ全 (11.8.2) 核。署名: α-params + `{R : Finset (ClassFunction ↥M ℂ)} (hRn : R.card = n)` +
`hZ`(⊆ZIrr)/`horth`(orthonormal, `if β=β' then 1 else 0`)/`hRmem`(SHC.ext ζ∈R)/`hRrev`(∀β∈R,∃η∈S(HC)
degree-w₁, β=SHC.ext η) → `∃ a:ℤ, (a=0∨a=1∨a=2) ∧ ⟨α^τ, SHC.ext ζ⟩ = (a:ℂ)−(n:ℂ)`。
- 証明: `exists_intProjection_of_orthonormal_ZIrr` で Parseval (c,Y,hcoeff,hnorm,hYorth) → `set a := c(SHC.ext ζ)+n`
  → hcζ (c(ζ^{τ₁})=a−n, def) + hcη (∀β∈R,β≠SHC.ext ζ→c β=a, hRrev+inj+`muGridAlpha_tau_inner_SHC_extension_sub`
  cont.³² relation を `linear_combination`) → `sum_sq_eq_of_split hζR hcζ hcη` + `rw [hRn]` → `muGridAlpha_tau_inner_self`
  (‖α^τ‖²=2+n²) → `int_le_of_add_inner_self_eq` (ℂ→ℤ, cont.³⁸) → `nlinarith` (n(a²−2a)≤2) → `charParam_a_mem_of_norm_ineq`。
- **honest 状態**: body は **sorry-free**。transitive dep = SHC_isCoherent / muGrid の §10→§6 bridge (既知 sorried carrier) のみ。
  `hRn : R.card = n` (=|S₁|=n = (11.8.1)) は §9↔§10-gated ゆえ **hypothesis 化**して caller に供給させる (deferred-payoff)。
- ⚠ Lean 固有ハマり: 署名の `horth` の `if β=β' then 1 else 0` は `open scoped Classical` 要 (Decidable);
  `int_le_of_add_inner_self_eq` の `linear_combination -hnorm` は goal と hnorm 両方 `push_cast at hnorm ⊢`
  で `(a−n:ℤ):ℂ` vs `(a:ℂ)−(n:ℂ)` の atom 不一致を解消。

**次 = (11.8.2) 残 + (11.8.3)–(11.8.5)**: α^τ=X−nζ^{τ₁}+a∑λ^{τ₁} 分解 (X=ω^σ diff, a=0/2 case) →
(11.8.3) β real → (11.8.4) residual form → (11.8.5) a=0 assembly。(11.8) closure は依然 doubly-gated
(§9↔§10 の (11.8.1) |S₁|=n、§14 の (11.8.6) S₂ coherence)。

## 2026-07-02 cont.⁴⁰ (lane-a) — **(11.8.2) residual decomposition + norm LANDED; ‖X‖²=2 (a∈{0,2})**
**`Hypothesis.muGridAlpha_tau_residual_norm`** landed (S12:7514, leaf green 3850 jobs, sorry-free body)。
`muGridAlpha_tau_proj_a_mem` (cont.³⁹) を包含する rich 版に昇格 (proj_a_mem は 3 行 projection に refactor、重複なし)。
署名 = proj_a_mem と同一 hyp。結論 (residual X = Parseval remainder Y を露出):
`∃ (a:ℤ)(Y:ClassFunction G ℂ), (a=0∨1∨2) ∧ (∀β∈R,⟨Y,β⟩=0) ∧ ⟨α^τ,ζ^{τ₁}⟩=(a:ℂ)−n ∧`
`⟨Y,Y⟩=(2:ℂ)+n²−((a−n)²+(n−1)a²) ∧ ((a=0∨a=2)→⟨Y,Y⟩=2)`。
- 証明追加分 (proj_a_mem 比): `hnormY` (hnorm を `push_cast`+`linear_combination -hnorm` で ⟨Y,Y⟩=norm式に),
  `a∈{0,2}→⟨Y,Y⟩=2` は `rw[hnormY]; rcases; rw[h]; push_cast; ring` (a=0: 2+n²−n²=2; a=2: (2−n)²+(n−1)4=n²)。
- **honest**: body sorry-free。transitive dep = SHC/muGrid §10→§6 bridge のみ。`hRn:R.card=n`(=(11.8.1)) は hypothesis 化。
- **意義**: `‖X‖²=2` (a∈{0,2}) + `X⊥S₁^{τ₁}` は Peterfalvi の `X=ω_{ij}^σ−ω_{i0}^σ` ((10.5)-類似) の直接 input。
  X (=Y) を露出したので (11.8.5) の ((μ₀−ζ)^τ,α_{ij}^τ) 2-way calc で消費可能。

**次 = X=ω_{ij}^σ−ω_{i0}^σ (norm-2 characterization) or (11.8.3) β**: X⊥S₁^{τ₁} + ‖X‖²=2 + X∈ℤ[ω-grid]
((10.5) Dade-image) ⟹ X=±(ω_a−ω_b)。ω-grid infra は `alignedOmegaSigmaGrid`(+`_inner` orthonormal) 既存。
(11.8) closure は依然 doubly-gated (§9↔§10 の (11.8.1)、§14 の (11.8.6))。

## 2026-07-02 cont.⁴¹ (lane-a) — **SHC ζ^{τ₁} vanishes on V LANDED (X=ω^σ diff の鍵入力)**
frontier map: **(10.5) の X=ω^σ diff 機構 (`alpha_tau_image` S12:4464) は full `coh:CoherentHypothesis` 依存**
→ (11.8.2) の by-contra (SHC only) では直接使えず **SHC-port が必要**と確定。既 landed の SHC-port:
- `SHC_extension_inner_alignedOmegaSigma_eq_zero` (7209) = (5.3.b) SHC 版 `⟨ζ^{τ₁},ω_{ij}^σ⟩=0` (既存)。

**本 landed**: `Hypothesis.SHC_tau1_zeta_vanishes_on_typePV` (S12:7298, leaf green, sorry-free)。
= (10.5) `tau1_zeta_vanishes_on_typePV` (4307, full-coh) の **SHC-port**: degree-w₁ irreducible ζ∈S(HC),
ζ̄≠ζ で `(SHC.ext ζ) v = 0` (∀v∈V=typePV)。証明 = full-coh 版の機械的 port (coh.tau1→SHC.extension):
(ζ−ζ̄)^τ=ζ^{τ₁}−ζ̄^{τ₁} (`tau_zeta_sub_conj_eq_SHC_extension`) が V で消え NC≤2<min(w₁,w₂) →
`sigmaCoeff_eq_zero_of_sigmaNC_lt` → 各 χ_{pq} で ⟨ζ^{τ₁}−ζ̄^{τ₁},χ⟩=0 → `inner_left_eq_zero_of_inner_sub_eq_zero`
で ⟨ζ^{τ₁},χ⟩=0 → `eq_zero_of_mem_V_of_inner_chiFam_eq_zero` (3.2.d)。**ζ̄∈S(HC)** (conj は degree-w₁+irr 保存)
ゆえ SHC API (`SHC_extension_inner_self/of_ne`, `extension_mem_ZIrr`) が両方に効く。**一発 green** (port 精確)。

**次 = SHC-port of `muGridPsi_vanishes_on_typePV` (4195) → ψ=X−δ(ω^σ diff) が V で消える**:
本 vanishing + `tau_muGridAlpha_apply_eq_on_typePV` (α^τ=δ(ω^σ diff) on V) で ψ vanish → norm-2 trichotomy
`eq_smul_chiFam_diff_of_vanishOnV` で X=δ(ω^σ diff) (SHC 版 `alpha_tau_image`)。(11.8) closure は依然
doubly-gated (§9↔§10 の (11.8.1)、§14 の (11.8.6))。
- ⚠ **general-a 注意**: (10.5) `muGridPsi` は a=0 前提 (X_{10.5}=α^τ+nζ^{τ₁})。(11.8.2) の residual X (=Parseval Y)
  は X=α^τ+nζ^{τ₁}−a∑λ^{τ₁} で a∈{0,2} 両方要 (a=0 は (11.8.5) の結論、先取り不可)。ψ(v)=0 には
  **∑_{λ∈S₁}λ^{τ₁}(v)=0** も要 → 各 λ∈S(HC) (degree w₁) に `SHC_tau1_zeta_vanishes` 適用 (λ̄≠λ 要;
  odd order ⟹ degree>1 は non-real で成立、但し per-λ に λ̄≠λ の供給要)。a=0 mainline を先に組んで a=2 を別扱いも可。

## 2026-07-02 cont.⁴² (lane-a) — **SHC ψ vanishes on V LANDED (a=0 form)**
`Hypothesis.SHC_muGridPsi_vanishes_on_typePV` (S12:7381, leaf green, sorry-free): a=0 form
`ψ = (α_{ij}^τ+n·ζ^{τ₁}) − δ(ω_{ij}^σ−ω_{i0}^σ)` が V で消える。証明 4 行 = `tau_muGridAlpha_apply_eq_on_typePV`
(α^τ=δ(ω^σ diff) on V, coh-free) + cont.⁴¹ `SHC_tau1_zeta_vanishes` → `rw; simp`。muGridPsi (4195) の
機械 port (coh.tau1→SHC.ext)。**一発 green**。

**次 = norm-2 Dade-image trichotomy → X=δ(ω^σ diff) (SHC `alpha_tau_image`)**:
`eq_smul_chiFam_diff_of_vanishOnV` (§5 の (4.8) endgame 一般化) に ‖X‖²=2 (cont.⁴⁰) + ψ vanish (本) を
食わせて X=δ(ω_{ij}^σ−ω_{i0}^σ)。⚠ (10.5) endpoint `alpha_tau_image` (4464) は full-coh gerekli の完成形;
SHC 版は本 chain (cont.⁴¹→⁴²→trichotomy) で組む。a=0: X=residual Y 直結。a=2: X=Y+2∑λ で ∑λ^{τ₁} vanish 要
(general-a 注意 above)。trichotomy lemma の署名確認 → X の norm-2/vanish/ZIrr を渡す。
(11.8) closure は依然 doubly-gated (§9↔§10 の (11.8.1)、§14 の (11.8.6))。

## 2026-07-02 cont.⁴³ (lane-a) — **SHC alpha_tau_image (a=0) LANDED — X=ω^σ diff 完成**
2 lemma landed (leaf green 3850 jobs, both sorry-free):
1. **`SHC_muGridAlpha_tau_X_inner`** (S12:7407): a=0 で `⟨X,ζ^{τ₁}⟩=0 ∧ ‖X‖²=2` (X=α^τ+n·ζ^{τ₁})。
   仮定 `hα0:⟨α^τ,ζ^{τ₁}⟩=−n` (=(11.8.2) a=0)。証明 = `muGridAlpha_tau_X_inner` (4146) の SHC port:
   `muGridAlpha_tau_inner_self` (‖α^τ‖²=2+n², coh-free) + `SHC_extension_inner_self` (‖ζ^{τ₁}‖²=1) +
   `inner_conj_symm` → `simp; ring`。**一発 green**。
2. **`SHC_tau_muGridAlpha_eq`** (S12:7454): a=0 で **`α_{ij}^τ = δ(ω_{ij}^σ−ω_{i0}^σ) − n·ζ^{τ₁}`** (SHC)。
   = full-coh `tau_muGridAlpha_eq` (4397) の SHC port: X∈ZIrr + ‖X‖²=2 (lemma 1) + ψ vanish (cont.⁴²) →
   `eq_smul_chiFam_diff_of_vanishOnV` trichotomy → X=δ(ω^σ diff)。`exists_alignedOmegaSigmaGrid_chiFam_family`
   で ω^σ=chiFam(P j)。**一発 green** (4416-4448 の機械 port)。

**意義**: (10.5) Dade-image identity の SHC 版が a=0 で完成 → (11.8.6) の `α^τ=ω^σ diff−nζ^{τ₁}` を SHC のみで
入手可能に。**次 = (11.8.3) β real/independence or (11.8.5) a=0 の 2-way calc**。(11.8.5) は本 SHC identity
+ `SHC_extension_inner_alignedOmegaSigma_eq_zero` (5.3.b) で β=a∑λ→a=0。a=2 case は ∑λ^{τ₁} vanish (per-λ,
general-a 注意) が要 → `SHC_extension_vanishes_on_typePV` (∀λ∈S(HC), λ̄≠λ) を先に組むと汎用。
(11.8) closure は依然 doubly-gated (§9↔§10 の (11.8.1)、§14 の (11.8.6))。

## 2026-07-02 cont.⁴⁴ (lane-a) — **非実性 helper + ∀λ∈S(HC) vanishing LANDED (a=2 path 準備)**
2 lemma landed (leaf green, both sorry-free):
1. **`inducedFamily_degree_w1_conj_ne`** (S12:3153): degree-w₁ irreducible χ∈M ⟹ χ̄≠χ (Pf (1.1) 非実性)。
   = `zeta_conj_ne` (3154) を一般 χ に汎化 (M odd ⟹ non-trivial=degree>1 は non-real、`not_isReal_of_ne_trivial_of_odd_card'`)。
   `zeta_conj_ne` は本 helper を cite する 1 行 corollary に refactor (重複除去)。
2. **`SHC_extension_vanishes_on_typePV`** (S12:7386): degree-w₁ irreducible χ∈inducedFamily M ⟹ `(SHC.ext χ) v=0` (v∈V)。
   = `SHC_tau1_zeta_vanishes` (cont.⁴¹) の hζne を helper 1 で discharge (χ∈S(HC) だけで OK)。∑λ^{τ₁} correction 消去用。

**次 = 一般 (11.8.2) X=ω^σ diff (a∈{0,2})**: residual Y (residual_norm) に Y∈ZIrr + Y=α^τ−∑c_β·β
(Parseval 分解式) + ∀β∈R β vanish (helper 2 を hRrev の各 λ に) を渡し、ψ=Y−δ(ω^σ diff) vanish →
trichotomy → Y=δ(ω^σ diff)。⚠ residual_norm を Y∈ZIrr + 分解式露出に拡張要 (exists_intProjection 直呼び)。
または (11.8.3) β real (document-order 次、(4.8)/(4.10)/(5.9) cite) を先行も可。
(11.8) closure は依然 doubly-gated (§9↔§10 の (11.8.1)、§14 の (11.8.6))。

## 2026-07-02 cont.⁴⁵ (lane-a) — **一般 (11.8.2) X=ω^σ diff (a∈{0,2}) LANDED — (11.8.2) 完成**
3-part refactor+payoff (leaf green 3850 jobs, all sorry-free):
1. **root lemma 拡張** `inner_self_eq_sum_sq_add_of_intProjection` (S12): 結論に `φ=∑c•α+Y ∧ Y∈ZIrr` 追加
   (hdecomp は exists_intProjection が既に供給; Y∈ZIrr = φ−∑(c•α), `Int.cast_smul_eq_zsmul`+`zsmul_mem`)。
2. **`residual_norm` 拡張** (S12): 結論に `Y∈ZIrr ∧ (∀v∈typePV, Y v = α^τ v)` 追加。hYV = hdecomp で Y=α^τ−∑c•β,
   各 β=SHC.ext λ (hRrev) が V で消える (`SHC_extension_vanishes_on_typePV` cont.⁴⁴) → ∑c•β(v)=0 →
   Y v=α^τ v。`ClassFunction.finset_sum_apply` で sum-apply。proj_a_mem の destructure も +2 更新。
3. **`SHC_residual_eq_omegaSigma_diff`** (S12:7875, **payoff**): residual_norm から a,Y 取得 → a∈{0,2} で
   ψ=Y−δ(ω^σ diff) が V で消える (hYV + `tau_muGridAlpha_apply_eq_on_typePV`) → trichotomy
   `eq_smul_chiFam_diff_of_vanishOnV` → **Y=δ(ω_{ij}^σ−ω_{i0}^σ)**。**一発 green**。

**意義**: (11.8.2) の residual characterization が a∈{0,2} 一般で完成 (a=0 は cont.⁴³ の
`SHC_tau_muGridAlpha_eq` = full identity、本 cont.⁴⁵ は a∈{0,2} で Y=ω^σ diff)。**次 = (11.8.5) a=0**:
本 Y=ω^σ diff + β 定義 (β=α^τ−(ω^σ diff)+nζ^{τ₁}) ⟹ β=a∑λ^{τ₁} → `SHC_extension_inner_alignedOmegaSigma_eq_zero`
(5.3.b) で a=0。あるいは (11.8.3) β real 先行。(11.8) closure は依然 doubly-gated (§9↔§10、§14)。

## 2026-07-02 cont.⁴⁶ (lane-a) — **residual 分解式 α^τ=Y−nζ^{τ₁}+a∑β 露出 (11.8.5 ingredient)**
`residual_norm` に第 8 conjunct追加 (S12, leaf green, sorry-free):
`hyp.tau(...) = Y - (n:ℂ)•ζ^{τ₁} + (a:ℂ)•∑_{β∈R}β`。証明 = hdecomp (α^τ=∑c•β+Y) + hkey
(∑c•β=−n•ζ^{τ₁}+a•∑β)。hkey は `Finset.add_sum_erase` で ζ^{τ₁} を split + hcζ (c_ζ=a−n) +
hcη (c_β=a, β≠ζ) の `Finset.sum_congr` → `push_cast; module` (smul 線形結合)。**一発 green** (module 有効)。
proj_a_mem + SHC_residual_eq_omegaSigma_diff の destructure も +1 更新。

**次 = (11.8.5) a=0 の 2-way calc**: ⟨(μ₀−ζ)^τ, α^τ⟩ を 2 通り。G側 = ⟨∑ω_{r0}^σ−ζ^{τ₁} ((11.8.4) landed),
Y−nζ^{τ₁}+a∑β (本分解式)⟩ を展開 (5.3.b で ⟨ω^σ,ζ^{τ₁}⟩=0・⟨ω^σ,β⟩=0、orthonormal R、alignedOmegaSigmaGrid_inner)。
M側 = ⟨μ₀−ζ, α_{ij}⟩ (Dade τ isometry) = μ inner products。等値 ⟹ a=⟨∑ω_{r0}^σ,β⟩、β=a∑λ (Y=ω^σ diff cont.⁴⁵)
⟹ a=a·0=0 (5.3.b)。⚠ 大 lemma: M側 μ-grid inner products (⟨μ_{r0},μ_{ij}⟩ 等) の材料要。
(11.8) closure は依然 doubly-gated (§9↔§10 の (11.8.1)、§14 の (11.8.6))。

## 2026-07-02 cont.⁴⁷ (lane-a) — **(11.8.5) M-side ⟨α_{ij}, μ₀−ζ⟩ = n−δ LANDED**
`muGridAlpha_inner_zeroColumnSum_sub_zeta` (S12, leaf green, sorry-free): μ₀=∑_{i'}μ_{i'0} (col-0 sum) で
`⟨α_{ij}, μ₀−ζ⟩ = (n:ℂ)−(δ:ℂ)`。証明 = `muGridAlpha_inner_muColumn_self_sub_conj` (3519) と同型:
⟨α,μ_{i'0}⟩ = −δ[i=i'] (`muGrid_inner_cross_column` j≠0・`muGrid_inner_self`/`_within_column` col-0 orthonormal・
`muGrid_inner_eq_zero_of_apply_one_ne` ζ degree-distinct)、Σ_{i'} = −δ (`Finset.sum_ite_eq`); ⟨α,ζ⟩=−n
(degree-distinct + ⟨ζ,ζ⟩=1)。M-side は既存 μ-grid inner infra で完全に組めた (新 μ 材料不要)。

**次 = (11.8.5) G-side + 等値 → a=0**: ⟨(μ₀−ζ)^τ, α^τ⟩ を Dade isometry で M-side (本=n−δ) と結合。
(11.8.4) hypothesis (μ₀−ζ)^τ=∑ω_{r0}^σ−ζ^{τ₁} の下で G-side を分解式 (cont.⁴⁶) + 5.3.b/orthonormal で
展開 → n−δ と等値 → a=0。⚠ (11.8.4) は by-contra 仮定なので (11.8.5) は仮定パラメータ化 or by-contra 内で。
(11.8) closure は依然 doubly-gated (§9↔§10 の (11.8.1)、§14 の (11.8.6))。

## 2026-07-02 cont.⁴⁸ (lane-a) — **(11.8.5) M-side → Dade image transport LANDED**
2 lemma landed (S12, leaf green, both sorry-free):
1. **`zeroColumnSum_sub_zeta_support`**: `(∑_{i'}μ_{i'0} − ζ).support ⊆ A0`。= `muColumn_sub_conj_support`
   (3720) の k=0/d=1/ζ (not ζ̄) 版 mirror。μ₀, ζ とも M'-induced で M' 外消滅、(μ₀−ζ)(1)=w₁−w₁=0 → M'^#⊆A0。
   ⚠ `open scoped FiniteInduce in` 要 (∑ ClassFunction の apply に Fintype ↥M)。
2. **`muGridAlpha_tau_inner_zeroColumnSum_sub_zeta`**: `⟨α^τ, (μ₀−ζ)^τ⟩ = n−δ`。= `tau_inner_eq_of_supported`
   (Dade isometry、α supported=`muGrid_alpha_support`, μ₀−ζ supported=lemma 1) で M-side (cont.⁴⁷ の
   `muGridAlpha_inner_zeroColumnSum_sub_zeta`=n−δ) を G-level に transport。3 行 (`muGridAlpha_tau_inner_muColumn_sub_conj` 3783 と同型)。

**次 = (11.8.5) 完成 (a=0)**: by-contra 仮定 (11.8.4) `(μ₀−ζ)^τ=∑ω_{r0}^σ−ζ^{τ₁}` を本 τ-transport に代入
→ `⟨α^τ, ∑ω_{r0}^σ−ζ^{τ₁}⟩ = n−δ`。G-side を分解式 (α^τ=δ(ω^σ diff)−nζ^{τ₁}+a∑β, a∈{0,2}, cont.⁴⁵/⁴⁶) +
`alignedOmegaSigmaGrid_inner` (ω orthonormal) + `SHC_extension_inner_alignedOmegaSigma_eq_zero` (5.3.b,
⟨ω^σ,ζ^{τ₁}⟩=⟨ω^σ,β⟩=0) で展開 → n−δ−a → 等値で a=0。a=1 除外は β real (11.8.3, 別途)。
(11.8) closure は依然 doubly-gated (§9↔§10 の (11.8.1)、§14 の (11.8.6))。

## 2026-07-02 cont.⁴⁹ (lane-a) — **(11.8.5) G-side ω-inner-product 材料 3 本 LANDED**
G-side 展開の inner-product 部品を 3 本 landed (S12, leaf green, all sorry-free、いずれも一発 green):
1. **`alignedOmegaSigma_diff_inner_zeroColumnSum`**: `⟨ω_{ij}^σ−ω_{i0}^σ, ∑_r ω_{r0}^σ⟩ = −1`。
   `alignedOmegaSigmaGrid_inner` (⟨ω_{ij},ω_{r0}⟩=[i=r∧j=0]) で ⟨ω_{ij},Σ⟩=0 (j≠0)・⟨ω_{i0},Σ⟩=1 → 0−1。
   (`Finset.sum_const_zero`/`sum_ite_eq`)。
2. **`SHC_extension_inner_zeroColumnOmegaSigma_sum`**: `⟨ζ^{τ₁}, ∑_r ω_{r0}^σ⟩ = 0` (5.3.b 各項 sum)。
3. **`R_sum_inner_zeroColumnOmegaSigma_sum`**: `⟨∑_{β∈R}β, ∑_r ω_{r0}^σ⟩ = 0` (各 β=λ^{τ₁} に helper 2、
   λ̄≠λ は `inducedFamily_degree_w1_conj_ne`)。

**次 = (11.8.5) full assembly (a=0)**: τ-transport (cont.⁴⁸=n−δ) + (11.8.4) 代入 + 分解式 (cont.⁴⁶) +
本 3 部品で ⟨α^τ, ∑ω_{r0}^σ−ζ^{τ₁}⟩ = n−δ−a を計算 → 等値 → a=0。⚠ 分解式は α^τ が第 1 引数 (inner_*_left,
star scalar) or conj-symm で第 2 引数化。SHC_residual_eq_omegaSigma_diff を hdecompA 露出に拡張すると
a,Y 一貫取得可。(11.8) closure は依然 doubly-gated (§9↔§10、§14)。

## 2026-07-02 cont.⁵⁰ (lane-a) — **★ (11.8.5) a=0 完成 (charParam_a_eq_zero_of_residualEq)**
`charParam_a_eq_zero_of_residualEq` (S12:8136, leaf green, **sorry-free**, **一発 green**)。
(11.8.4) hypothesis `h114 : (μ₀−ζ)^τ = ∑ω_{r0}^σ − ζ^{τ₁}` を取り、`∃ a, a∈{0,1,2} ∧ ⟨α^τ,ζ^{τ₁}⟩=a−n
∧ ((a=0∨a=2)→a=0)` を結論 (a=1 除外は 11.8.3 β real で別途 → 完全 a=0)。証明:
- SHC_residual_eq_omegaSigma_diff (hdecompA 露出に拡張) で a,Y,hbound,hinner,hYeq,hdecompA 一貫取得。
- τ-transport (cont.⁴⁸) に h114 代入 → `htrans : ⟨α^τ, ∑ω_{r0}^σ − ζ^{τ₁}⟩ = n−δ` (M-side)。
- G-side `hαω : ⟨α^τ, ∑ω_{r0}^σ⟩ = −δ`: `rw[hdecompA, hYd]` (α^τ=δ(ω^σ diff)−nζ^{τ₁}+a∑β) →
  `simp only [inner_add/sub/smul_left, 3 部品 (cont.⁴⁹), star_nat/intCast]; ring`。
- `rw[inner_sub_right, hαω, hinner] at htrans` → `−δ−(a−n)=n−δ` → `linear_combination -htrans` → (a:ℂ)=0 → a=0。

**意義**: **(11.8.2)+(11.8.5) 完成** — residual-orthogonal 仮定下で全列係数 a=0。これは (11.8.6) の
`μ_j^{τ₂}=∑ω_{ij}^σ` coherence 矛盾の鍵入力。**次 = (11.8.3) β real (a even, a=1 除外)** or (11.8.6)
assembly (S₂ coherence=§14 gate、S(C) coherent → (11.3) 矛盾)。h114 (11.8.4) は landed (10.9) から
by-contra 内で establish (residual⊥ 仮定)。(11.8) closure は依然 doubly-gated (§9↔§10 の (11.8.1)、§14 の (11.8.6))。

## 2026-07-02 cont.⁵¹ (lane-a) — **源泉照合 (11.8.5/6 verified) + (11.8.6) opening identity LANDED**
mmd 04.13 (11.8.5)/(11.8.6) を精読 (l.49-70, 復元済)。**自作 (11.8.5) lemma が Peterfalvi と一致確認**:
M-side (μ_0−ζ,α_{ij})=−1+n (δ=1 で n−δ に一致)、G-side (∑ω_{r0}^σ,β)−1−a+n → a=0。⚠ **a-even (a=1 除外)**:
Pf は "(β,1_G)=0 + β real ⟹ a even" (§1 一般 parity 参照、詳細略) → a∈{0,2} → (11.8.2) → a=0。**これが未実装の
残ピース** (β real=(11.8.3): (4.8)/(4.10)/(5.9) + 一般 parity)。自作 lemma は a∈{0,2}→a=0 を直接与えるので
a-even だけ別途要。

**本 landed**: `tau_muColumnSum_sub_zeta_eq_of_alphaImage` (S12, leaf green, sorry-free) = (11.8.6) opening:
`(μ_j − dζ)^τ = ∑_i ω_{ij}^σ − dζ^{τ₁}` (δ=1, d=w₁n+1)。halpha (a=0 image ∀i、SHC_tau_muGridAlpha_eq δ=1) +
h114 ((11.8.4)) を仮定パラメータ化。証明 = M-level identity `μ_j−dζ=(μ_0−ζ)+∑α_{ij}` を τ 線形 (`map_add`,
`map_sum`、hyp.tau=IntegralCharacterMap linear) で写し → 3 image 代入 → `module`。full-coh 版
(5462-5510 の (10.6.a) column-sum τ) と同型。⚠ `←Finset.smul_sum` が δ-scalar 無で nζ 項を先取り → `(n*w₁)`
順 → `mul_comm` 追加で解消。

**次 = (11.8.6) full**: μ_j^{τ₂}=∑ω_{ij}^σ ((4.9) or (5.8)) → S(C)=S₁∪S₂ coherent → (11.3) `S_H0C_not_coherent`
矛盾。⚠ S₂ coherence (§14 gate: (9.11)+(11.7))、μ_k∈S₂ ((9.8.b)/(9.9.b))、τ₂ 拡張。or (11.8.3) β real 先行。
(11.8) closure は依然 doubly-gated (§9↔§10 の (11.8.1)、§14 の (11.8.6))。

## 2026-07-02 cont.⁵² (lane-a) — **(11.8.5) 結論を `Even a → a=0` に強化 (a-even を明示 hypothesis 化)**
`charParam_a_eq_zero_of_residualEq` の結論を `((a=0∨a=2)→a=0)` → **`(Even a → a=0)`** に強化 (leaf green,
sorry-free)。a-even (Pf の "β real ⟹ a even") を明示 threaded hypothesis 化 → 下流 (endpoint) が
consume する自然形。証明: Even a + a∈{0,1,2} で a≠1 (`obtain ⟨k,hk⟩:=heven; omega`) → a∈{0,2} → 既存 2-way calc。

**★ a-even の中身 (未実装、次の ungated piece)** — mmd 04.13 l.59 + 04.9 l.109 照合で判明:
Pf の一般 parity lemma = 「**odd-order G の real virtual char Δ₁,Δ₂ (⊥1_G) に対し ⟨Δ₁,Δ₂⟩ は even**」
((1.1) 非実性で Irr∖{1} が χ↔χ̄ で対、Δ real で係数対等 → ∑=2·(pairs))。a=(∑ω_{r0}^σ,β) に適用: β real
((11.8.3)) + ∑ω_{r0}^σ real + 両者⊥1 で a even。⚠ 一般 parity lemma は involved (`conjPerm` involution
+ cross-Parseval `⟨φ,ψ⟩=∑_χ⟨φ,χ⟩·conj⟨ψ,χ⟩` の pairing、~80 行)。infra: `IrreducibleCharacter.conjPerm`
(BrauerPermutationUnconditional)、ZIrrFourier Parseval 既存。(11.8.3) β real は (4.8)/(4.10)/(5.9)。

**(11.8) 残 ungated = 一般 parity lemma + (11.8.3) β real → a-even; (11.8.6) full は §14-gated**。
(11.8) closure は依然 doubly-gated (§9↔§10 の (11.8.1)、§14 の (11.8.6))。

## 2026-07-02 cont.⁵³ (lane-a) — **a-even parity の組合せ核 `even_sum_of_involution` LANDED**
`even_sum_of_involution` (S12, leaf green, sorry-free、汎用 Finset lemma): 固定点自由 involution `g` on `s`
+ 不変重み `f(g a)=f a` ⟹ `Even (∑_{a∈s} f a)`。証明 = **ZMod 2 経由**: `(f a:ZMod 2)+(f(g a):ZMod 2)=2·(f a)=0`
(`CharTwo.add_self_eq_zero`) → `Finset.sum_involution` で ∑ mod 2 = 0 → `ZMod.intCast_zmod_eq_zero_iff_dvd`
+ omega で Even。**一発 green (API fix 1 回: Int.even_iff_two_dvd 無 → obtain+omega)**。

これは a-even の**組合せ核** (Irr∖{1} の χ↔χ̄ 対、(1.1) で固定点自由)。**次 = 一般 parity lemma**
`⟨Δ₁,Δ₂⟩ even (real Δ_i ⊥1_G, odd G)`: cross-Parseval `⟨Δ₁,Δ₂⟩=∑_χ c₁(χ)c₂(χ)` (c_i∈ℤ)、Δ real で
c_i(χ̄)=c_i(χ)、c_i(1)=0 → 本 `even_sum_of_involution` を conjPerm (χ↦χ̄, `IrreducibleCharacter.conjPerm`) に
適用。⚠ cross-Parseval + IsReal→c(χ̄)=c(χ) の materialize 要。その後 a=(∑ω_{r0}^σ,β) に適用 (β real=(11.8.3)、
∑ω_{r0}^σ real + ⊥1)。(11.8) closure は依然 doubly-gated (§9↔§10、§14)。

## 2026-07-02 cont.⁵⁴ (lane-a) — **cross-Parseval `mem_ZIrr_inner_eq_sum_over_irr` LANDED**
`mem_ZIrr_inner_eq_sum_over_irr` (S12, leaf green, sorry-free): `Δ∈ZIrr G` で
`⟨φ,Δ⟩ = ∑_{χ:Irr} ⟨φ,χ⟩·⟨Δ,χ⟩`。証明 = **Fourier 再構成** `sum_inner_irreducibleCharacter_smul`
(Δ=∑_χ⟨Δ,χ⟩•χ) + `inner_sum_right`/`inner_smul_right` (star は `mem_ZIrr_inner_int` (⟨Δ,χ⟩∈ℤ real) で
消滅) → `mul_comm`。**一発 green** (repr-support 経由より遥かに clean; ⚠ `irreducibleCharacters G` は Set
なので `∑ χ:IrreducibleCharacter G` subtype univ で和; `sum_inner_irreducibleCharacter_smul` は
CharacterCompleteness (ZIrrFourier 非 import) ゆえ S12 に置く)。

**次 = 一般 parity lemma `even_inner_of_isReal_orthogonal_one`**: cross-Parseval (本) + `even_sum_of_involution`
(cont.⁵³) を conjPerm (Irr∖{1}) に適用。要: (a) IsReal Δ → ⟨Δ,χ̄⟩=⟨Δ,χ⟩ (`conjPerm_apply_coe` + inner conj)、
(b) ⟨Δ,1⟩=0 で 1 項除外、(c) univ→univ\{1} で even_sum_of_involution。その後 a=(∑ω,β) application (β real 要)。
(11.8) closure は依然 doubly-gated (§9↔§10、§14)。

## 2026-07-02 cont.⁵⁵ (lane-a) — **一般 parity lemma `even_inner_of_conjPerm_symmetric` LANDED**
`even_inner_of_conjPerm_symmetric` (S12, leaf green, sorry-free): Δ₁,Δ₂∈ZIrr G (odd G)、conjPerm-symmetric
Fourier 係数 `⟨Δᵢ,χ̄⟩=⟨Δᵢ,χ⟩` (hsym、IsReal の帰結) + `⟨Δᵢ,1⟩=0` (htriv) ⟹ **`∃ z, ⟨Δ₁,Δ₂⟩=(z:ℂ) ∧ Even z`**。
証明: `choose c₁ c₂` (mem_ZIrr_inner_int で ⟨Δᵢ,χ⟩=(cᵢχ:ℂ)) → cross-Parseval (cont.⁵⁴) で ⟨Δ₁,Δ₂⟩=(∑cᵢ:ℂ) →
c₁(triv)=0 (htriv) で triv 項除外 (`Finset.add_sum_erase`) → `even_sum_of_involution` (cont.⁵³) を conjPerm に:
g_inv=`(conjPerm G).left_inv`、g_ne=`conjPerm_eq_self_iff`+`not_isReal_of_ne_trivial_of_odd_card'`、
g_mem=conjPerm injective+conjPerm triv=triv (`trivialClassFunction_isReal`)、hf=cᵢ symmetric (hsymc、hsym+cast)。
⚠ hsym (`⟨Δ,χ̄⟩=⟨Δ,χ⟩`) は hypothesis threaded (IsReal→係数対称の inner-conj identity 未整備ゆえ)。

**次 = (a) IsReal Δ → hsym (inner-conj identity `⟨Δ,χ̄⟩=conj⟨Δ,χ⟩` 整備); (b) a=(∑ω_{r0}^σ,β) application**:
β real=(11.8.3) + ∑ω real + 両者⊥1 で本 lemma 適用 → a even → (11.8.5) full a=0。⚠ (11.8.3) β real は
(4.8)/(4.10)/(5.9) の SHC port が要 (大)。(11.8) closure は依然 doubly-gated (§9↔§10、§14)。

## 2026-07-02 cont.⁵⁶ (lane-a) — **parity core 自己完結化 (IsReal 版) — inner-conj identity LANDED**
2 lemma landed + parity lemma refactor (S12, leaf green, all sorry-free):
1. **`inner_conj_conj`**: `⟨φ̄, ψ̄⟩ = star⟨φ,ψ⟩` (汎用)。証明 = innerSum pointwise (`conj_apply`+`star_mul`+`star_star`)
   → `card·inner` に乗じて `mul_left_cancel₀` (⅟card の star motive 問題を回避; `card_mul_inner`+`star_natCast`)。
2. **`inner_conjPerm_eq_of_isReal`**: real Δ∈ZIrr で `⟨Δ, conjPerm χ⟩ = ⟨Δ,χ⟩`。= `conjPerm_apply_coe`
   (χ̄=χ.conj) + Δ=Δ.conj (IsReal) + inner_conj_conj (star⟨Δ,χ⟩) + `mem_ZIrr_inner_int` (⟨Δ,χ⟩∈ℤ real で star 消滅)。
3. **`even_inner_of_conjPerm_symmetric` refactor**: hsym threaded → **`IsReal Δᵢ` を直接取る**自己完結版
   (内部で hsym を `inner_conjPerm_eq_of_isReal` で導出)。

**a-even parity core 完成** (`even_sum_of_involution`→cross-Parseval→inner_conj_conj→parity lemma、全て IsReal ベース、
threaded hyp 無)。**残 = a=(∑ω_{r0}^σ,β) application**: β real=(11.8.3, (4.8)/(4.10)/(5.9) SHC port、大) +
∑ω_{r0}^σ real + 両者⊥1_G。それで parity lemma 適用 → a even → (11.8.5) full a=0。⚠ β real は大 sub-chain。
(11.8) closure は依然 doubly-gated (§9↔§10、§14) — a-even 完成しても endpoint は §14 gate 残。

## 2026-07-02 cont.⁵⁷ (lane-a) — **parity lemma を「片側⊥1」に弱化 (application 適合)**
`even_inner_of_conjPerm_symmetric` の htriv を **片側 (`⟨Δ₂,1⟩=0`) のみ**に弱化 (leaf green, sorry-free):
χ=1 項 `c₁(1)·c₂(1)` は c₂(1)=0 だけで消える (mul_zero)。**理由**: application で Δ₁=∑ω_{r0}^σ は **⊥1 でない**
(⟨∑ω, ω_{00}^σ=trivial⟩=1、`alignedOmegaSigmaGrid_zero_zero`+`_inner`)、Δ₂=β のみ ⊥1。両者 real は必要
(係数対称)。より一般化した正しい版。

**a-even application の残ピース map (cont.⁵⁷ 調査)**:
- **∑ω_{r0}^σ real**: `exists_rowInv_alignedOmegaSigma_conj` (S12:5829、conj(ω_{i0})=ω_{i'0} 対合) + `.conj=mapRingEquiv conjAe`
  bridge (S12:4926) + reindex。`zeta_tau1_norm_ge_one` (5988) が pointwise で同 pairing 使用。~40 行 (choice+involutive+conj-sum+reindex)。
- **β real**: (11.8.3) = (4.8)/(4.10)/(5.9) の SHC port (大)。`tau_muGrid_column_diff` (4772, full-coh)=(4.8)。
- **β⊥1**: ⟨β,1⟩=⟨α^τ,1⟩−δ⟨ω^σ diff,1⟩+n⟨ζ^{τ₁},1⟩。
(11.8) closure は依然 doubly-gated (§9↔§10、§14)。

## 2026-07-02 cont.⁵⁸ (lane-a) — **∑ω_{r0}^σ real LANDED (a-even M-side reality)**
`Hypothesis.sum_alignedOmegaSigma_zeroColumn_isReal` (S12, leaf green, sorry-free): `IsReal (∑_r ω_{r0}^σ)`
(Pf (3.9)(a))。証明: `exists_rowInv_alignedOmegaSigma_conj` (5829) で choice → 行対合 σ (conj(ω_{r0})=ω_{σr,0})、
σ involutive (`hgridinj` = alignedOmegaSigmaGrid_inner の 1≠0、+ conj_conj) → bijective; conj-sum は Finset.induction
(`conj_add`/`conj_zero`)、`.conj=mapRingEquiv conjAe` bridge (4926) で各項 (hσ r).1、`Equiv.sum_comp` で reindex。
⚠ API ハマり: `map_sum` は mapRingEquiv (非 bundled coe) に非適用 → induction; sum_congr は g 明示 `show..from`;
挿入で charParam の `open scoped FiniteInduce in` が分離 → 再付与。

**a-even application 残 = β real (11.8.3, 大) + β⊥1**。∑ω real は landed、片側⊥1 (parity cont.⁵⁷) ゆえ
∑ω は⊥1 不要 (ω_{00}=1 成分持つが Δ₂=β のみ⊥1)。∑ω∈ZIrr も要 (ω^σ は ZIrr、要確認)。
(11.8) closure は依然 doubly-gated (§9↔§10、§14) — a-even 完成しても endpoint は §14 gate 残。

## 2026-07-02 cont.⁵⁹ (lane-a) — **a-even assembly `a_even_of_eq_inner_sumOmegaSigma` LANDED**
`Hypothesis.a_even_of_eq_inner_sumOmegaSigma` (S12, leaf green, sorry-free、**一発 green**): `a=⟨∑ω_{r0}^σ,β⟩`
+ β∈ZIrr + IsReal β + ⟨β,1⟩=0 ⟹ **`Even a`**。証明 = `∑ω∈ZIrr` (`alignedOmegaSigmaGrid_mem_ZIrr` 1717 +
`Submodule.sum_mem`、3 行) + `∑ω real` (cont.⁵⁸) + parity core (`even_inner_of_conjPerm_symmetric` cont.⁵⁷)
→ ⟨∑ω,β⟩=(z:ℂ)∧Even z、a=z (cast) → Even a。**a-even parity CHAIN 完成** (parity core→∑ω real→本 assembly)。

**残 = β-side (deferred, 本 lemma で hypothesis threaded)**: β def (=α^τ−δ(ω^σ diff)+nζ^{τ₁}) +
**a=⟨∑ω,β⟩ の 2-way calc** (general a、私の a∈{0,2} calc と別) + **β real=(11.8.3, 大)** + β⊥1。
これらが揃えば a even → a∈{0,2} → `charParam_a_eq_zero_of_residualEq` で a=0 (unconditional)。
(11.8) closure は依然 doubly-gated (§9↔§10、§14) — a-even 完成しても endpoint は §14 gate 残。

## 2026-07-02 cont.⁶⁰ (lane-a) — **β⊥1_G `beta_inner_trivial` LANDED**
`Hypothesis.beta_inner_trivial` (S12, leaf green, sorry-free、**一発 green**): i≠0 で
`⟨α^τ − δ(ω^σ diff) + nζ^{τ₁}, 1_G⟩ = 0`。証明: ⟨α^τ,1_G⟩=⟨α_{ij},1_M⟩ (`tau_inner_trivial` 5520 Dade 随伴、
α_{ij} A0-supp=`muGrid_alpha_support`) =0 (hα1M threaded); 1_G=ω_{00}^σ (`alignedOmegaSigmaGrid_zero_zero`) で
⟨ω^σ diff,1_G⟩=0 (`alignedOmegaSigmaGrid_inner`、i≠0 で両 [i=0]=false); ⟨ζ^{τ₁},1_G⟩=0 (5.3.b)。
`inner_add/sub/smul_left` で組んで ring。⚠ hα1M (⟨α_{ij},1_M⟩=0) は threaded (μ_{i0}≠1_M for i≠0 が要、非自明)。

**a-even application 入力状況**: ∑ω real ✓/∑ω∈ZIrr ✓/parity core ✓/assembly ✓/**β⊥1 ✓**。
**残 = β∈ZIrr + β real (11.8.3, 大) + a=⟨∑ω,β⟩ 2-way calc + hα1M (⟨α_{ij},1_M⟩=0)**。
(11.8) closure は依然 doubly-gated (§9↔§10、§14)。

## 2026-07-02 cont.⁶¹ (lane-a) — **β∈ZIrr + ⟨α_{ij},1_M⟩=0 LANDED (β⊥1 unconditional)**
2 lemma landed (両 clean, S12 sorry 4 不変):
- `Hypothesis.beta_mem_ZIrr` (be55188d): β = α^τ−δ(ω^σ diff)+nζ^{τ₁} ∈ ZIrr G。α^τ∈ZIrr
  (`muGridAlpha_tau_mem_ZIrr`)、ω^σ 各∈ZIrr (`alignedOmegaSigmaGrid_mem_ZIrr`)、ζ^{τ₁}∈ZIrr
  (`SHC_isCoherent.extension_mem_ZIrr`); `Submodule.add/sub_mem` + `Int.cast_smul_eq_zsmul`/zsmul_mem +
  `Nat.cast_smul_eq_nsmul`/nsmul_mem。→ assembly の `hβZ` 充足。
- `Hypothesis.muGridAlpha_inner_trivial_M` (05a23f31): i≠0 で ⟨α_{ij},1_M⟩=0。**cont.⁶⁰ で threaded した
  hα1M を実証明で discharge**。1_M=μ_{00} (`muGrid_zero_zero_eq_trivial`) ⇒ ⟨μ_{ij},1_M⟩=⟨μ_{ij},μ_{00}⟩=0
  (cross-column j≠0)、⟨μ_{i0},1_M⟩=⟨μ_{i0},μ_{00}⟩=0 (within-column i≠0)、⟨ζ,1_M⟩=0 (ζ irr deg w₁>1、
  `irr_cf_inner`+`if_neg`)。⚠ 発見: grid の 1_M は origin (0,0) に 1 個だけ (`muColumnZero_inner_trivial`=1 と整合);
  i≠0 だから全 constituents が principal を避ける。→ `beta_inner_trivial` の hα1M が grounded、β⊥1 が i≠0 で unconditional。

**a-even application 入力状況 (更新)**: ∑ω real ✓/∑ω∈ZIrr ✓/parity core ✓/assembly ✓/β⊥1 ✓ (now unconditional)/**β∈ZIrr ✓**/**hα1M ✓**。
**残 = β real (11.8.3, 大) + a=⟨∑_r ω_{r0}^σ,β⟩ 2-way calc** の 2 本のみ。両揃えば a-even capstone (Even a)
→ `charParam_a_eq_zero_of_residualEq` で a=0 (unconditional)。endpoint は依然 §14-gated。
- `ha` (a=⟨∑_r ω_{r0}^σ,β⟩): 展開すると ∑_r⟨ω_{r0}^σ,α^τ⟩ + δ (ω 自己直交 `alignedOmegaSigmaGrid_inner` で
  cross/within 項が畳まれ、5.3.b で ζ^{τ₁} 項消滅) → 残 = ∑_r⟨ω_{r0}^σ,α^τ⟩ が (11.8.4)-type residual に依存。moderate-big。
- `β real` (11.8.3): (4.8)/(4.10)/(5.9) SHC port。row-conj involution (`exists_rowInv_alignedOmegaSigma_conj`)
  + τ₁ conj 交換 + α reality。BIG (multi-iteration)。

## 2026-07-02 cont.⁶² (lane-a) — **ha 連結 + (11.8.5) capstone LANDED (a-even 全組立完了、残 β real のみ)**
まず**投資判断の検証** (重要): 私の β は係数 **δ** (α^τ−**δ**(ω diff)+nζ^{τ₁})、note 旧記述 (line 31/573) は係数 1。
`charParam` の `hαω`=⟨α^τ,∑ω⟩=−δ は a∈{0,2} 特殊値 (hYd 依存) で**無条件でない**。無条件展開すると
⟨α^τ,∑ω⟩=**a−δ** (`muGridAlpha_tau_inner_zeroColumnSum_sub_zeta`=n−δ + h114 + hinner(=a−n))。
⟹ ⟨β,∑ω⟩=(a−δ)−δ·(−1)+n·0=**a** (β の δ 係数が α^τ の δ を相殺) ⟹ **全 δ で成立** (δ=1 に限らない)。
∴ **係数 δ の私の β が正しい一般 (11.8.3) 残差** (note 旧係数 1 は δ=1 専用)。cont.⁶⁰⁻⁶¹ の β-pieces は正しい対象。

2 lemma + capstone landed (全 clean, S12 sorry 4 不変):
- `muGridAlpha_a_eq_inner_sumOmegaSigma_beta` (62230243): **ha 連結** (a:ℂ)=⟨∑_r ω_{r0}^σ,β⟩。
  ⟨α^τ,∑ω⟩=a−δ (`have hαω`、linear_combination) → ⟨β,∑ω⟩=a (`simp only [inner_add/sub/smul_left, hαω,
  alignedOmegaSigma_diff_inner_zeroColumnSum(=−1), SHC_extension_inner_zeroColumnOmegaSigma_sum(=0),
  star_int/natCast]; ring`) → `inner_conj_symm`+`star_intCast` で ⟨∑ω,β⟩=a。⚠ `[Invertible (card ↥M:ℂ)]`
  明示 binder は FiniteInduce scoped instance と非defeq衝突 → 除去 (charParam/beta_mem_ZIrr と同様 scope 供給)。
  ⚠ `rw [star_intCast]` は inner_smul_left の `starRingEnd ℂ` に非match → `simp only` で bridge。
- `residualCoeff_eq_zero` (c837cb6f、**capstone**): **無条件 a=0** = ⟨α^τ,ζ^{τ₁}⟩=−n、β real (hβr) threaded のみ。
  `charParam_a_eq_zero_of_residualEq` (a∈{0,1,2}+((Even a)→a=0)) + `beta_mem_ZIrr` + `beta_inner_trivial`
  (hα1M=`muGridAlpha_inner_trivial_M`) + `muGridAlpha_a_eq_inner_sumOmegaSigma_beta` (ha) +
  `a_even_of_eq_inner_sumOmegaSigma` (Even a) → a=0。trivial-char bridge (`trivialClassFunction G` vs
  `trivialIrreducibleCharacter G`) は defeq (`coe_trivialIrreducibleCharacter`=rfl) → exact 直結。

**a-even application = 完全組立済み。残る genuine prerequisite は β real (11.8.3) ただ 1 本**
((4.8)/(4.10)/(5.9) SHC port; row-conj involution `exists_rowInv_alignedOmegaSigma_conj` + τ₁ conj 交換 + α real)。
これが landed すれば `residualCoeff_eq_zero` の hβr が discharge され、(11.8.5) parity 側が完全 sorry-free。
(11.8) endpoint は依然 doubly-gated (§9↔§10 の |S₁|=n、§14 の S₂ coherence) — a=0 は (11.8.6) の
`μ_j^{τ₂}=∑ω_{ij}^σ` 矛盾の鍵入力だが endpoint closure は §14 gate 残。**次 = β real (11.8.3)**。

### β real (11.8.3) 実装計画 — Coq `PFsection11.v` 809-830 の構造 (cont.⁶³ 調査)
Coq `Rbeta: cfReal beta` の recipe (β = β_{0 j1}、row 0 に betaE で還元後):
```
have betaE i j: j != 0 -> beta_ i j = beta.   (* (11.8.3) 前半: i,j 独立 *)
  ... prDade_sub_TIirr / prDade_sub2_TIirr (= (4.8)/(4.10)) で β_{ij}=β_{i j1}=β_{0 j1} *)
have Rbeta: cfReal beta.                        (* (11.8.3) 後半: β̄=β *)
  rewrite rmorphD !rmorphB (conj を β の各項に分配)
  ... cfAut_cycTIiso (σ が conj と可換: conj(η_{0j})=η_{0,k}, k=aut_Iirr conjC j)
  ... Dade_aut (τ が conj と可換: conj(τ φ)=τ(conj φ))
  set k := aut_Iirr conjC j; rewrite -(betaE 0 k)  (* β_{0k}=β *)
  rewrite cfConjC_Dade_coherent coh_tau1 ?mFT_odd  (* τ₁ が conjC と可換 — 奇数位数必須 *)
  Dtau1 cfAut_seqInd (τ₁ on ζ̄)
```
**必要な 5 ピース (上流順)** — ⚠**重要発見 (cont.⁶³): piece 2,3 の Galois-equiv 中核は `S07_CoherenceGalois.lean`
に既存**。β real は「ゼロから構築」でなく「既存 comm lemma の wiring + assembly」→ 規模大幅縮小:
1. **σ Galois-equiv (一般 column, row 0)**: `conj(ω_{0j}^σ) = ω_{0,k}^σ`, k=w2 column-conjugate。
   既存 `exists_rowInv_alignedOmegaSigma_conj` は **column 0 の row-conjugation** (w1 側)。row-0 の
   **column-conjugation** (w2 側) が新規。machinery: `sigma_mapRingEquiv_comm`+`galoisMap_conj_omega`
   +`omegaProdChar_inv` は共通、w2CharEquiv の inversion が要 (w1CharEquiv_rowInv の w2 版)。**未実装**。
2. **τ Galois-equiv (`Dade_aut`)** ✅ **LANDED (cont.⁶³, `tau_mapRingEquiv_comm`)**: `hyp.tau(φ^{σc})=（hyp.tau φ)^{σc}`
   (A0-supp φ)。`hyp.tau`=`dadeIntegralCharacterMap ...` (def) ゆえ `S07.dadeIntegralCharacterMap_mapRingEquiv_comm`
   を直接 `exact` (一発 green)。σc=conjAe で reality。
3. **τ₁ (SHC extension) Galois-equiv (`cfConjC_Dade_coherent`)**: `SHC.ext(ζ^{σc})=(SHC.ext ζ)^{σc}`。
   ⚠ 中核は `S07.IsCoherent.extension_mapRingEquiv_comm` (Pf (5.9)(a)) に**既存** (general `hτ:IsCoherent`)。
   SHC への instantiate + 前提 (hSirr/hspan/hSu/hlat/h2) 供給が要 (wiring)。
   ✅ **LANDED (cont.⁶⁵, `SHC_extension_conj`)**: `(ζ^{τ₁})‾=(ζ‾)^{τ₁}`。全前提供給:
   hspan=`SHC_zSpan_vanish_support`; h2=共役対 {ζ,ζ̄} (`inducedFamily_hasNoRealCharacters`);
   hSu (conjAe)=`inducedFamily_closedUnderConjugate`+irr.conj+deg (`.conj=mapRingEquiv conjAe` bridge 経由);
   hlat=`extension_mem_ZIrr`; hSirr=`mem_irreducibleCharacters`; hA'=`subset_rfl`。
   ⚠ `.conj` 2 箇所は `simp only [hbridge]` で一括変換 (rw は inner χ.conj を先に食う)。⚠ `open scoped FiniteInduce in` 要。
4. **betaE (β independence)**: (4.8)/(4.10) SHC port。`tau_muGrid_column_diff` (4772) は full-coh `coh`
   依存 → SHC 版 extract 要 (Dade/σ isometry は coh 非依存ゆえ抽出可能なはず)。**未実装**。
5. **Rbeta assembly**: 1-4 を上記 recipe で組む。
**規模 (改訂)**: piece 2 ✅、piece 3 ✅ (cont.⁶⁵)。残 = 1 (σ column-conj at row 0)、4 (betaE)、5 (assembly)。上流順 1→4→5。
**次 = piece 1** (σ column-conjugation at row 0): `conj(ω_{0j}^σ) = ω_{0,k}^σ`, k=w2 column-conjugate。
既存 `exists_rowInv_alignedOmegaSigma_conj` (column 0 の row-conj、w1 側) の w2 版。machinery
(`sigma_mapRingEquiv_comm`/`galoisMap_conj_omega`/`omegaProdChar_inv`) 共通、w2CharEquiv inversion が新規。
**gate 確認**: §14 下流でなく (11.8.5) の genuine prerequisite (document-order 11.8.3<11.8.5、本来上流)。
SHC context で全て可能 (α^τ/ω^σ/ζ^{τ₁} は既に SHC で構築済み、conj 可換性を足すのみ)。

## 2026-07-02 cont.⁶⁶ (lane-a) — **β real 全 pieces LANDED、(11.8.5) hβr 実証明化。新上流 = issue 9004 (Hypothesis46 修正)**

**landed (leaf green ×3 commit)**:
- piece 1 `exists_colInv_alignedOmegaSigma_conj` (b6fe2cd5): ∃k, (k=0↔j=0) ∧ conj(ω_{0j}^σ)=ω_{0k}^σ
  ∧ conj(μ_{0j})=μ_{0k} ∧ δ_k=δ_j。σ/μ 両 grid 同一 k (column index 共有 `finCardEquivCharacterGroup`)。
  δ_k=δ_j は (4.9)(a) bridge+eq から w2-primality 不要で導出。⚠ ⁻¹-pattern の rw は letI/型表示差で
  不発 → congrArg+exact (defeq) 迂回; ite 条件は simp が True 化 → if_true (if_pos rfl 不可)。
- piece 4 `beta_row_eq` + `beta_column_eq_zeroRow` (180ec1eb): betaE 2 分解。row move は
  four-corner 差 (h410 thread = δ-scaled (4.10))、column move は μ_{0j}−μ_{0k} 差 (h48 thread =
  row-0 (4.8))。両方 harg (module) + map_add + thread + module の 4 行証明。
- piece 5 `beta_isReal` (同): Rbeta (Coq PFsection11.v 823-831 忠実)。row-0 還元 → conj 分配
  (pointwise ext、mapRingEquiv-atom 形) → piece 2/1/3 で各項 conj → coherence bridge
  `tau_zeta_sub_conj_eq_SHC_extension` で ζ̄→ζ → column move at k。
- **capstone 配線**: `residualCoeff_eq_zero` の hβr thread を beta_isReal の実証明で置換。
  残 thread = hdeg0 (row-0 degree、(10.3) で自明 discharge) + **h410/h48 のみ**。
- piece 2 の宣言名バグ修正: `Hypothesis.Hypothesis.tau_mapRingEquiv_comm` (namespace 内 prefix
  重複) → `Hypothesis.tau_mapRingEquiv_comm`。

**新発見 (issue 9004、shared-infra 設計逸脱)**: h48/h410 の discharge 先 = S06 の (4.8)
`certainType_diff_dade_eq`/(4.10) `fourCorner_dade_eq` (両方 landed 済・coherence-free) だが、
前提の `Hypothesis46` が**原文/Coq から逸脱** — `tic_V = W\W₂ (big V)` + dade0 on A∪V_big^L。
正 = small V (W−(W₁∪W₂)): 原文 (3.1)/(8.10)/**(8.15) (p.48 mmd MISSING → PDF 直読で回収**:
「(4.6) holds for L=M, K=M′, A=A(M), A₀=A₀(M), H=M_F or M_s」)/Coq `cyclicTIset`+
`prime_Dade_definition`。big V は W₁^# ⊆ V を強制し TI-in-G が C_G(x)⊆W (x∈W₁^#) を要求 →
§10 で供給不能 (位数論法で W₁^# は V_small^M にも A(M)=(M′)^# にも入らない)。
**Hypothesis46 は未インスタンス化** (全 repo でパラメータ出現のみ) ゆえ latent だった。
修正案+fallout map (S06 内 ~6 rw-site 単純化 + supp 補題 1 本強化 (W₁-vanishing で y=1 除外) +
S08 は型不変) は issue 9004。**lane a が claim** (hub 異議あれば差し戻し)。

**残作業 (上流順)**: ① issue 9004 の Hypothesis46 small-V 修正 (S06 refactor)、
② `Hypothesis.toHypothesis46` (§10 instantiation = (8.15) 形式化; tic は
`typePData_toTICyclicHypothesis` (already small-V)、A_covers は A(M)=(M′)^# で自明、
dade0 は typePA0 の conjClassSet (G-conj) vs V^M (M-conj) の照合が要調査)、
③ (4.8)/(4.10) → aligned grid の bridge lemma (ticVdiff h46 ≟ typePData tic の defeq 確認、
`certainTypeOmegaSigma` ↔ `alignedOmegaSigmaGrid`、`h46.tau.toDadeMap` ↔ `hyp.tau`)、
④ h48/h410 discharge。(11.8) endpoint は依然 doubly-gated (§9↔§10、§14) — h114 ((11.8.4)) の
discharge も③と同根の見込み。

## 2026-07-03 cont.⁶⁷ (lane-a) — **issue 9004 全完了: toHypothesis46 landed、h48/h410 discharge。(11.8.5) 残 thread = h114 のみ**

**landed (4 commits, 全 full-build green + AxiomsCheck OK)**:
- ①' typePA0 M-共役化 (4623902b): 前提衛生の追加発見 2 (G-共役は subset_L×単純性で充足不能) を修正。
  `conjClassSetIn H T` (Coq `class_support`) を GroupTheory/ConjClassSet に新設。
  `normalizer_typePA_eq` は A(M)=(M')# → N_G(M')=M (極大+単純、hG param 追加) で再証明;
  consumer (toHypothesis71 系) は easy 方向のみ → `le_normalizer_typePA` 抽出で無傷。
- ①'' (4.6.d) dade0 台集合も conjClassSetIn に統一 (da38b5f7) — §10 照合を definitional 化する布石。
- ② `Hypothesis.toHypothesis46` (52150245): (8.15)/(10.1) 形式化。**dade0/tau は definitionally
  `hyp.dadeData.dade`/`fullDadeIsometryData hyp.hconj`** (conjClassSetIn 統一の payoff)、tic_V=rfl、
  H:=K=M' ((10.1) H=M_s)、A_covers 自明 (A(M)=(M')#)。Hypothesis46 初インスタンス化。
- ③+④ (f5dd2373): `tau_muGrid_zeroRow_diff` ((4.8) row-0) + `tau_muGrid_fourCorner` ((4.10)
  δ-scaled) — §6 の `certainType_diff_dade_eq`/`fourCorner_dade_eq` を toHypothesis46 経由で
  aligned grid に cite。**(11.8.5) capstone `residualCoeff_eq_zero` の hdeg0/h410/h48 thread 除去**
  (+hw2 : w2.Prime param、CharacterParameters.w2_prime が供給)。

**③ bridge の実装知見 (再利用可)**:
- defeq が全部通る: `ticVdiff h46 = typePData_toTICyclicHypothesis … := rfl`、
  `ticVdiffFullDadeApplication h46 = canonicalFullDadeApp … := rfl` (Prop fields は proof-irrel)、
  `hyp.tau = dadeIntegralCharacterMap h46.dade0 h46.tau := rfl`。
- σ-bridge `certainTypeOmegaSigma h46 χ₂ⱼ i' = alignedOmegaSigmaGrid i j`: ω-引数の pointwise 一致
  (`ticWEquivSdiffW h46 g = e g`、二重 Subtype.ext + `coe_ticWEquivSdiffW`/`subgroupCongr_apply`)
  → `show (ticVdiff h46).sigma …; rw [harg]; unfold alignedOmegaSigmaGrid; rfl`。
- ⚠ rw の invisible mismatch 2 種: (a) `set`-fvar (χ₂/i0) vs 展開形 → bridge を「χc = 展開形 →
  ic = 展開形 → 結論」の等式パラメータ形にして rfl-subst; (b) OfNat/instance 差 (h-based vs
  h46-based の `0 : Fin (Nat.card _.W1)`) → 結論 shape ごとに `have hbN : … := hbridge …`
  (exact は defeq 許容) してから rw [hbN]。sign 合わせも congrArg+esign.symm (exact ベース)。
- hXeq ((4.10) の δ-rescale) は h-based atom に揃えて `simp only [difference, classFunction]` 後
  δ = ±1 で rcases → push_cast → module。

**現状 (11.8.5)**: `residualCoeff_eq_zero` の前提は全て genuine §10 data + **h114 ((11.8.4)
`(μ₀−ζ)^τ = ∑ω^σ_{r0} − ζ^{τ₁}`) のみ**が residual thread。h114 は ζ^{τ₁} (SHC coherent
extension) が絡み (4.8)/(4.10) と異質 (coherence-dependent) — Pf 原文 (11.8.4) は「(11.8.1) と
τ の linearity」による由; 次 frontier はこれの実証明化 (SHC_tau_muGridAlpha_eq 系の在庫確認から)。
(11.8) endpoint 自体は依然 doubly-gated (§9↔§10 の |S₁|=n、§14 の S₂ coherence)。

## 2026-07-03 cont.⁶⁸ (lane-a) — **(11.8.4) 完全実証明化: dichotomy + branch-2 swap + h114 producer LANDED**

h114 ((11.8.4) 正規化形) を **原文 p.66 に忠実な dichotomy として実証明** (S12, 全 axiom-clean、
S12 sorry 4 不変)。「h114 は残 residual thread」という cont.⁶⁷ の評価を解消 — h114 は今や
`∃ ν coherent extension, h114-for-ν` として無条件に供給可能:

- **`tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal`** (dichotomy): 直交仮定下、
  `(μ₀−ζ)^τ` は `∑ω_{r0}^σ` と **単一 signed coherent extension** だけずれる:
  branch 1 = `= ∑ω − ζ^{τ₁}` (= h114、正規形)、または branch 2 = `S(HC)={ζ,ζ̄}` かつ
  `= ∑ω + ζ̄^{τ₁}`。証明 = `‖χ‖²=1` (Dade 等長 + 直交 pin `⟨ψ,ω_{r0}⟩=1`) → 整数内積
  `⟨χ,ζ^{τ₁}⟩,⟨χ,ζ̄^{τ₁}⟩` (ZIrr pairing, Cauchy–Schwarz ≤1, 差 −1) → `χ=ζ^{τ₁}` or `χ=−ζ̄^{τ₁}`。
  汎用 unit-norm 整格子 toolkit (`m²≤1`、`⟨A,θ⟩=±1→A=±θ`) を inline 証明。
- **`SHC_swap`** (branch-2 「we may assume」の core math): `S(HC)={ζ,ζ̄}` のとき
  `φ ↦ −SHC.ext(φ̄)` が **再び τ の coherent extension** (原文の ζ^{τ₁},ζ̄^{τ₁} → −ζ̄^{τ₁},−ζ^{τ₁}
  置換)。4 field 全証明: 等長 = `inner_conj_conj` + ZIrr-pairing 実性、`extends_on_supported` =
  `S(HC)={ζ,ζ̄}` ゆえ A₀-supported span 元は `a(ζ−ζ̄)` (値 at 1 = `(a+b)w₁=0`)、ZIrr codomain +
  nonzero witness `ζ−ζ̄` は SHC 継承。**実装知見**: (i) conj の ℤ-linearity は
  `conj = mapRingEquiv conjAe` bridge + `mapRingEquiv_zsmul` で inline `hconj_zsmul`; (ii) zsmul
  値抽出は `← Int.cast_smul_eq_zsmul ℂ` + `smul_apply`; (iii) `1∉A₀` は
  `supportInSubgroup` defeq + `dade.ne_one`; (iv) span-pair 係数 → `a+b=0` は φ(1)=0 経由。
- **`SHC_swap_h114`**: branch 2 で swap が h114 を満たす (`SHC_swap.ext ζ = −ζ̄^{τ₁}` ゆえ
  `∑ω − SHC_swap.ext ζ = ∑ω + ζ̄^{τ₁} = (μ₀−ζ)^τ`)。
- **`exists_coherent_extension_h114_of_orthogonal`** (統合 producer): 直交仮定 →
  `∃ ν : IsCoherent τ S(HC) A₀, (μ₀−ζ)^τ = ∑ω − ν.ext ζ`。branch 1 = SHC、branch 2 = swap。
  **(11.8.4) は sorry-free に完全形式化** (residual thread 解消)。

**残 = (11.8.5) machinery の extension-一般化 refactor** (次 frontier): `residualCoeff_eq_zero` と
その依存 (~20 本: `charParam_a_eq_zero_of_residualEq`/`beta_isReal`/`muGridAlpha_a_eq_inner_sumOmegaSigma_beta`/
`SHC_residual_eq_omegaSigma_diff`/`SHC_extension_inner_self`/`_of_ne`/`tau_zeta_sub_conj_eq_SHC_extension`/
`SHC_extension_inner_zeroColumnOmegaSigma_sum` 等) は現状 `hyp.SHC_isCoherent hG` を hardcode。
これらを **「conj と可換な任意 coherent extension ν」でパラメタ化**すれば (SHC/swap 両方が instance)、
`exists_coherent_extension_h114_of_orthogonal` の ν を渡して **無条件 (11.8.5) a=0** が出る。
refactor は各補題に `(ν : IsCoherent …)` + conj-commute 前提を足し SHC 版を薄い specialization に
する機械的作業 (build-green 保ちつつ 1 本ずつ)。**swap が conj-commute を満たすことは確認済**
(`SHC_extension_conj` が negation+swap で保存: `(−ext(φ̄)).conj = −(ext(φ̄)).conj = −ext(φ) = swap(φ̄)`)。

**endpoint (`exists_zeta_residual_not_orthogonal`) は依然 §14-gated** (S₂=S(C)−S(HC) coherence、
lane-b/c の 9.11 sibleyTarget)。(11.8.5) 無条件化は §14 gate の手前まで spine を honest に前進させる
(deferred-payoff だが genuine、CLAUDE.md「報酬後払いを deprioritize しない」)。

**spine 接続の code-level 確認 (2026-07-03)**: `card_kappaHall_lt_of_isTypeIIIorIV` (spine 唯一の
bare sorry の consumer) → `w2_lt_w1_of_hypothesis` (11.9.b) → `exists_zeta_residual_not_orthogonal`
(11.8)。§9 counts の残 (`caseA_character_counts`/`caseB_character_counts` conjunct 4 = (9.8.d)/(9.9.c)、
`exceptional_case_frobenius_realization` = (9.10)) は **consumer ゼロ** (grep 確認) = 現状 off この
spine (type-III 判定 (11.9.c) 向け、endpoint は degree facts (9.8.b/9.9.b = 既 proven) のみ要)。
10.7/10.8/10.10 は on-spine (`no_typeV_maximal`←FeitThompson) だが (7.8.b は S09 で sorry-free 済) +
type-II 構造 (10.7 carrier scaffold) + §14 に coupled-gated。⟹ 現 lane-a の on-spine ungated frontier
= **(11.8.5) extension-一般化 refactor** (上記) が最有力。

## 2026-07-03 cont.⁶⁹ (lane-a) — **(11.8.2)–(11.8.5) machinery を任意 coherent extension `coh` に一般化完了 + producer↔capstone wiring 完結**

cont.⁶⁸ が指した「(11.8.5) machinery の extension-一般化 refactor」を**完遂** (2 commits, 全 full-build
green + AxiomsCheck OK, S12 sorry 4 不変)。

**① 全 subtree を `coh` でパラメタ化** (commit `5a67ee61`): `residualCoeff_eq_zero` 以下の (11.8.2)–
(11.8.5) 補題群 (~27 本) が固定 `SHC_isCoherent hG` でなく任意 `(coh : IsCoherent hyp.tau hyp.SHCSet hyp.A0)`
を取る。`coh` が要る性質は全て **generic** (直交正規性 `IsCoherent.inner_extension_*`、ZIrr 所属
`extension_mem_ZIrr`、`τ(ζ−η)=coh ζ−coh η` = `extends_on_supported`) — 例外は **conj-commute のみ**
(`beta_isReal`/`residualCoeff_eq_zero` に `hconj : ∀ χ deg-w₁ irr, (coh χ)‾ = coh χ‾` を追加、P4)。
- 新 `abbrev Hypothesis.SHCSet` (degree-w₁ irr subfamily の略記)。
- `SHC_extension_inner_self`/`_of_ne` は generic への SHCSet-adapter に。
- **SHC producers** (`tau_muColumnZero_sub_zeta_dichotomy_of_orthogonal`/`SHC_swap`) は SHC-specific
  のまま、一般化 leaf へ `hyp.SHC_isCoherent hG` を渡す (9 call sites)。
- 数学的健全性を**両 branch で検証済**: branch 1 (coh=SHC, a=0, `⟨α^τ,coh ζ⟩=a−n=−n`)、branch 2
  (coh=swap, two-way computation が SHC-basis 係数 `a=n` を出し `⟨α^τ,swap ζ⟩=−⟨α^τ,SHC ζ̄⟩=−a=−n`) —
  同一の abstract 論証が両方を被覆。

**② `SHC_swap_conj` + producer 強化** (commit `da165ea8`): (11.8.4) dichotomy producer が capstone の
消費インターフェースを丁度供給するよう wiring 完結。
- `SHC_swap_conj`: swap の P4 conj-commute (両辺 `=−SHC(χ‾‾)`)。
- `exists_coherent_extension_h114_of_orthogonal` を強化し `∃ ν, hconj(ν) ∧ h114(ν)` を返す
  (branch 1=`SHC_extension_conj`、branch 2=`SHC_swap_conj`)。**h114 は自由仮定でなく orthogonality
  仮定から producer が生成** (+ ν の conj-commute も) → (11.8.5) `a=0` は h114 スレッド解消済。

**現状 (11.8.5) = 無条件化の interface 完成**。`residualCoeff_eq_zero` は `coh`+`hconj`+`h114` を取り、
これらは全て producer (h114) か `SHC_extension_conj`/`SHC_swap_conj` (hconj) が供給。**残る endpoint
`exists_zeta_residual_not_orthogonal` の gate は genuine downstream のみ**:
- **(11.8.1) count `|S(HC)| = n`** = §9↔§10 carrier bridge (`hRn : R.card = n` の gated 入力)。
- **(11.8.6) `S(C)`-coherence contradiction** = §14 (S₂=S(C)−S(HC) coherence、lane-b/c の 9.11 sibleyTarget)。

**次 frontier 候補** (上流優先+文書順): endpoint の (11.8.6) assembly は §14-gated ゆえ、lane-a の on-spine
ungated 上流は §9 count carrier (`card_G0_lower_bound` 7.10 = issue 0044、on-path 確定) か §10-13 structural。
(11.8) machinery 側は interface 完成につき、これ以上の ungated 前進は endpoint assembly (gated) 待ち。
