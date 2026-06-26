---
id: 2025
slug: mf-hall-centralizer-control-cor153
title: "Cor 15.3 mf_hall_centralizer_control = 次の FT-path W1 target [deep, 3 inputs]"
created: 2026-06-26
---

# Cor 15.3 `mf_hall_centralizer_control` = 次の FT-path W1 target [deep, 3 inputs]

## 背景 (2026-06-26 lane-c scoping)

lane-c は W1 寄与で (12.9) Hall complement (issue 2016) を着地後、**次の非衝突 FT-path W1 target**
を精査。orphaned な §14/§15 sorry (`sigmaLength_one_frobenius_type`/`exists_sigmaDecomposition_length_le_two`/
`typeP1_conjugate_and_typeP_twoClasses`/`centralizer_escape_final_local` = 全 0 consumer、off-path)
を除外し、**唯一の FT-path 接続を持つ §14/§15 sorry = `mf_hall_centralizer_control`** (Cor 15.3,
`S15_MF.lean:2483`) を同定。

### FT-path 接続 (重要)
```
mf_hall_centralizer_control (Cor 15.3)
  → theoremI_nilpotentHall_conjugacy_and_type_dichotomy (BG Thm I, S16:2852,
     "the BG output consumed by Peterfalvi (8.8)") [first assertion = fusion control; consumes hfusion @S16:2890]
  → Peterfalvi (8.8) dichotomy (Thm I second assertion = all-type-I ∨ case-(b))
  → theorem88_caseB_holds (Pf S14_MaximalI:1396, FT endpoint, FeitThompson:361)
```
⟹ lane-c の (12.7) `typeI_frobenius` work と**同じ endpoint に収束**。`ha` (part a 分解) も
`sylow_le_Msigma_of_le_centralizer_sylow` (S15:2756) → Cor 15.4 (`nilpotent_hall_embeds_in_msigma`)
→ Thm I 経由で FT-path。非衝突: `S15_MF.lean` は lane-f の hot file (S16_MainResults/NonExistenceG) と別。

## 構造 (tractability)

`mf_hall_centralizer_control_of_inputs` (S15:2424) は **sorry-free gated-endpoint skeleton**。
wrapper `mf_hall_centralizer_control` (S15:2483, sorry) は 3 input を discharge して skeleton 適用:

| input | 内容 | provenance (docstring L2411-2419) | 状態 |
|---|---|---|---|
| `ha` | `C_M(H) = (C_M(H)⊓M_σ) ⊔ X`, X cyclic τ₂ | Prop 14.2(b1)(e) + Lemma 15.1(c) | **deep** — H=M_σ 版 (`mf_centralizer_msigma_decomp`, sorry-free) は template だが、一般 Hall H 版は **`C_M(H)` が κ'-群** を要し M_σ 版 (`centralizer_msigma_isPiSubgroup_kappa_compl`) は一般化不可 (x が H を中心化しても M_σ を中心化しない) ⟹ 新 math |
| `hconj` | G-共役 H-元は M 内で共役 (∃ m∈M) | Theorem 14.4 + `normalizer_eq_self_of_mem_maximalSubgroups` (S15:2635, proven) | **deep** — Theorem 14.4 (∃ c∈C_G(x), M^{gc}=M) が citeable lemma として **未発見** |
| `hfratt` | H⋬M で Frattini factorization M=N_M(H)·Q | Theorem 15.2 の normal Q=O_q(M) + Frattini | **deep** — Theorem 15.2 O_q 要確認 |

## やること

- [x] **`ha` 完了 (2026-06-26, κ'-fact 実証明)**: `mf_centralizer_hall_decomp_of_kappaCompl`
      (S15_MF, sorry-free + axiom-clean) = H=M_σ template `mf_centralizer_msigma_decomp` を一般 Hall H に
      一般化。κ'-性は **hypothesis `hkappa : IsPiSubgroup (kappa M)ᶜ (C_G(H)⊓M)` として取る** (=「C_M(H) κ'」)、
      `C_{M_σ}(X)≠1` は `H ≤ M_σ⊓C_G(X)` (X≤C_G(H)) + `H≠⊥` で導出。⟹ **ha の残 gate = 単一事実
      「C_M(H) が κ'-群」(一般 Hall H、BG Prop 14.2(b1)(e)、subtle prime-set 論法、新 math)**。
      M_σ 版 `centralizer_msigma_isPiSubgroup_kappa_compl` は H=M_σ 専用で一般化不可。
      **「C_M(H) κ'」の証明路 (2026-06-26 原文精読で確定、BG Cor 15.3 proof + Prop 14.2)**:
      背理。p∈κ∩π(C_M(H)) と仮定、x'∈C_M(H) order p、X'=⟨x'⟩∈E¹(K) (K=κ-Hall)。
      (1) **Prop 14.2(b1)**: N_M(X')=K×K* (K*=C_{M_σ}(K))。
      (2) H ≤ C_M(x') ≤ C_M(X') ≤ N_M(X')=K×K*。H は σ-群 ⟹ H ≤ (K×K* の σ-部)=K* (K は σ')。
      (3) H は M_σ の Hall ⟹ q∈piSet(H) で H ⊇ (M_σ の Sylow q)。H≤K* ⟹ Sylow q ⊆ K*。
      (4) q∈piSet(H)⊆π(K*) (H≤K*, H≠1)。**Prop 14.2(e)**: p∈π(K*) なら M_σ の Sylow ⊄ K* ⟹ 矛盾。
      ⟹ 要 repo: Prop 14.2(b1) `N_M(X)=K×K*` + (e) `Sylow_p(M_σ)⊄K*` + Hall⊇Sylow。
      **可用性 (2026-06-26 確認)**: (b1) は `typeP_structure` (S14:1808) の conjunct 3 (`hb1`) で**可用**。
      **✅✅ ha 完了 (2026-06-26, commits `37a15204` + `d742451a`)**: (e) を含む 4 lemma を実証明
      (全 sorry-free + axiom-clean、AxiomsCheck 登録)。
      - `typeP_sylow_not_le_kstar` (S14, Prop 14.2(e) 第2節 `S⊄K*`): Part A (ℳ(K*)≠{M}, Lemma 13.13)
        + Part B (S≤K* なら Lemma 13.6 `ℳ(S)={M}` と矛盾)。`kstar_ne_msigma_aux` を corollary 化。
      - `exists_typePESetup_kappaHall` (S14): Hall κ K → E-setup (E₁≤K≤E) (Prop 14.2 preamble)。
      - `typeP_sylow_not_le_kstar_of_isHall` (S14): (e) を typeP-packaged 形に。
      - `centralizer_hall_isPiSubgroup_kappa_compl` (S14): **κ'-fact** (H≤K* via b1+Dedekind →
        Sylow_q(M_σ)≤H≤K* が (e) に矛盾)。
      - `mf_centralizer_hall_decomp` (S15): general `ha` を **unconditional 化**
        (`mf_centralizer_hall_decomp_of_kappaCompl` の κ' 仮説を κ'-fact で discharge)。
      ⟹ **ha gate 閉鎖**。残 = hfratt + wrapper signature gap (下記)。
- [x] **`hconj`: 完了 (2026-06-26)** — `mf_hall_conj_realized_in_M` (S14_TypePCounting, sorry-free + axiom-clean)。
      Theorem 14.4 = `sigmaLength_one_centralizer_structure` (proven) は sharp transitivity を持つが
      conjugator の C_G(x) 所属を捨てていた → 新 helper `exists_conj_centralizer_of_mem_maximalSigma`
      で C_G(x)-witness を保持 → `normalizer_eq_self_of_mem_maximalSubgroups` で `cg⁻¹∈M` を導出。
      D は param 化 (caller が `dummySigmaDecomposition G` 等を供給)。
- [ ] `hfratt` = **次の W1 大型ユニット (workable-hard, gated でない)**。Theorem 15.2 (c)/(d) の Q=O_q(M)
      組み立て + Frattini。**精査 (2026-06-26, mmd L4180-4213)**: 全インフラ sorry-free で在庫:
      - `frattini_factorization` (S15:2316): `∀m∈M,∃n a,…` 結論を供給 (要 hQHnorm + hcop)。
      - `msigma_quotient_isNilpotent_of_inputs` (S15:4627, **sorry-free skeleton**): Q (hQMσ/hMnormQ/
        hKstarQ/hQneMσ/Normal) が揃えば M_σ/Q nilpotent を FPF (prime action) から証明。
      - `kstar_le_fittingInAmbient_of_inputs` (S15:1893) + `kstar_le_opiCore_of_le_fittingInAmbient`
        (S15:1930): K*⊆F(M_σ)⊆O_q(M)=Q を of_inputs で供給 (Theorem 3.8 `S03h_Thm38` + Lemma 6.3a
        `S06_Additional` 既存)。
      残 = **assembly** (deep gate でなく多段組み立て、~1 session):
      - **✅ step 1 完了 (2026-06-26, commit `7c199a70`)**: `hall_subgroupOf_normal_of_msigma_nilpotent`
        (S15_MF, sorry-free + axiom-clean) = M_σ 冪零で H Hall なら H=O_{π(H)}(M_σ) char ⟹ H⊴M。
        対偶で `H⋬M ⟹ M_σ 非冪零 ⟹ M_F≠M_σ` (`isTypeP1_of_mf_ne_msigma` S15:2098 sorry-free が型-P₁ を供給)。
      - **step 2 (Q 構成) = 既存で済む**: `mf_ne_msigma_typeP1_structure` (S15:6595, sorry-free) が M_F≠M_σ +
        Hall κ K から Q=O_q(M) を全 property (Q≤M_σ, M≤N(Q), K*≤Q, D nilpotent complement of Q in M_σ)
        付きで供給。⟹ M_σ/Q nilpotent は D-complement (M_σ/Q≅D) または `msigma_quotient_isNilpotent_of_inputs`。
        K (Hall κ) は `exists_isHallSubgroup_kappa_ge` 等で取得。
      - **step 3 (QH⊴M) = 残る核 (~50-70 行, novel)**。**鍵の発見 (2026-06-26)**: **Q = M_σ の normal
        Sylow_q ⟹ Q char in M_σ** (Thm 15.2(c): Q=normal Sylow_q(M), q∈σ ⟹ |Q|=q-part of |M_σ| ⟹
        Q=Sylow_q(M_σ); `Sylow.characteristic_of_normal`)。⟹ QH⊴M の 2 経路:
        (A) **推奨経路 (全 lemma 確定済)**: Q char in M_σ = `Q=O_q(M_σ)=opiCoreInG{q}M_σ` ゆえ
            `oPiCore.characteristic` (Q⊴M_σ q-群⊆O_q(M_σ); O_q(M_σ) char⊴M⊆O_q(M)=Q で Q=O_q(M_σ))。
            QH.subgroupOf M_σ = `(oPiCore π̄ (M_σ/Q)).comap(mk')` (image=O_π を card 論法、π=π(H));
            `oPiCore.characteristic` + `Subgroup.Characteristic.comap_quotient_mk` (mathlib QuotientGroup/
            Basic:395、kernel char + K char ⟹ comap char) ⟹ QH.subgroupOf M_σ char in M_σ;
            `normal_of_characteristic_subgroupOf` (S04d:116) + M_σ⊴M ⟹ QH⊴M。残 card 論法 = image=O_π のみ;
        (B) `normal_sup_sylow_of_quotient_nilpotent` (S10_BetaRadical:458, Sylow 版 template) を Hall 化
            (証明同型、Sylow→Hall=O_π) → QH⊴M_σ → Q char で ⊴M lift。
      - **step 4**: q∉π(H) (q∈π(H) なら Q≤Syl_q(M_σ)≤H, QH=H⊴M で H⋬M に矛盾) ⟹ Q∩H=1 + coprime。
      - **step 5**: `frattini_factorization` で M=N_M(H)Q。
- [ ] 3 input を `mf_hall_centralizer_control_of_inputs` に wire → wrapper sorry-free 化。
- [ ] ⚠ **wrapper signature gap**: `mf_hall_centralizer_control` (S15:2483) は `H ≤ M_σ` を欠く
      (`hH : IsHallSubgroup (piSet H) (H.subgroupOf M_σ)` からは導出不可)。hconj/ha は `H ≤ M_σ` 要 →
      wrapper に `hHMσ : H ≤ Msigma M` を追加要 (consumer S16:2890 [lane-f hot] + S15:2795 [lane-c] の
      call site に 1 引数追加; S16 編集 = lane-f 調整要)。

## 完了条件

`mf_hall_centralizer_control` が sorry-free ⟹ BG Theorem I (first assertion) の fusion gate 解消
→ Pf (8.8) dichotomy → `theorem88_caseB_holds` (FT endpoint) の (8.8) 入力に前進。

## 参照

- 主所有: `OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF.lean` (`mf_hall_centralizer_control` 2483 /
  `_of_inputs` 2424 / `mf_centralizer_msigma_decomp` 2509 template)。
- 消費: `S16_MainResults.lean:2890` (Thm I)。FT endpoint = `S14_MaximalI.lean:1396`。
- 関連: issue 0080 (W1 Prop 16.1 bridges, lane-f)、2016 (CLOSED, (12.9) Hall compl)、0081 (W2 §12)。
- ⚠ multi-session deep。lane-f の S16 hot file と非衝突 (別 file S15_MF)。
