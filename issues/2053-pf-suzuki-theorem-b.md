---
id: 2053
slug: pf-suzuki-theorem-b
title: "Peterfalvi II Ch.II The First Case: Theorem B campaign"
created: 2026-07-21
---

# Peterfalvi II Ch.II The First Case: Theorem B campaign

## 背景

Part II Ch.I (§1–§3, pp. 97–107) は **sorry 0 で完全** (Lemma 5 =
issue 2048 で完結)。文書順の次 = **Ch.II The First Case (pp. 108–114)**、
完全未着手。主定理 **Theorem B**: (B1) (V が素数位数 p の P を含み
C_G(P) の 2-rank が 1) の下で Theorem A の結論が成り立つ。

構造 (2026-07-21 に pp. 108–114 全読で確定):
(B2) 「G に指数 p の正規部分群なし」を仮定 (否定側は Ch.I §3 Prop 2 =
InductionNonSimple で済) して番号付き steps (1)–(17):

- (1) `V = W ⋊ P`, `|Q₀| = 2^p`, `N_G(P) = C_G(P)`,
  `C_D(P) = C_W(P) × P` — Ch.I §2 Prop 3 + §3 Prop 1(b) 部品
- (2)(a) `C_G(P)` は Ω_P 上で (A1) を満たす; kernel N。
  (b) near-field F で `C_G(P)/N = (F ⋊ C_Q(P)) ⋊ Σ` —
  Ch.I §1 Prop 4(c) + **Appendix II Prop 1 (NearFields.lean 実装済)**
- (3) `|Q₁|` の素因数 r ≡ 2^i (mod 2^p−1) — [Is] Thm 15.16
  (coprime 次元 dim M = p·dim C_M(P)) + Clifford ([Is] 6.5) +
  **Appendix I Prop 2 (SemilinearField.lean 実装済)** の field 構造
- (4) `|Q| = |C_Q(P)|^p` — **Wielandt fixed point thm ([HB] XI 12.4)**、
  Z[KP] の Frobenius identity 経由 (repo 被覆要確認:
  GroupTheory/WielandtPerFactorDischarge / CoprimeFixedPoints)
- (5) F 非可換 → F ≅ F_{9,2} ∧ Q₁ = 1 — Ch.I §2 Cor to Prop 2
  (SylowTwo) + [H] III 8.2 (2-rank 1 quaternion) +
  Appendix II Prop 2 (F_{r²,2} 分類)
- (6) Q₁ = 1 → |Σ| ∈ {1,3} or (|F| = f or 9 ∧ Σ = 1) —
  [HB] IX 2.7 型算術 (f^a = 2^b + 1)
- (7) N = P ∧ Σ ≅ C_W(P) — §3 Prop 1(c) の |R| 三分岐で場合消去
- (8) Q₁ ≠ 1 → ℓ = |Σ| prime、|F| = 3^ℓ/5^ℓ/9^ℓ
- (9) p = f — transfer T : G → H/(QKW) の直接計算 (coset reps = §1
  Prop 4(a))、p ∣ |Q|+1
- (10) |F| = p^m の二分岐 (10.1) p ∤ |Σ| ∧ |G|_p = p^{m+2} /
  (10.2) p = |Σ| = 3, F ≅ F_{9,2}, W cyclic of 3 or 9 —
  **Ch.I §3 Lemma 5 を使用 (完成済!)** + (3)(4)(6)(8) の算術
- (11) R = T × P、C_Q(P) が A − {P} に正則作用
- (12) case (10.2) が成立 — (10.1) を否定。R₁ = Sylow p (order p³,
  class 2 < p) に **Hall-Wielandt**: `G/O^p(G) = N_G(R₁)/O^p(N_G(R₁))`。
  ⚠ ここは A = Sylow 自身なので **weakly closed 自明 + class < p =
  Isaacs Cor 10.2 (transfer_range_eq_of_nilpotencyClass_lt, 実装済)** で
  賄える見込み — 必要なのは「transfer range equality →
  G/O^p ≅ N/O^p 同型」への bridge (focal subgroup 系)
- (13) C_G(Z₁) は 3-group (Z₁ = ⟨st⟩) — PSL(2,8) 構造 (§3 Lemma 4)
- (14) Z(RΣ) = Z₁P、N_G(RΣ)/RΣ ≅ S₃、R₂ = C_G(Z₁)
- (15) L cyclic of 9 (PSL(2,8) 内)、Ω₁(LV) = Z₁ΣP
- (16) Z₁PΣ ⊆ Z₂(R₁)、N_G(Z₁PΣ) = R₂⟨s⟩
- (17) 結論 — Z₁PΣ abelian weakly closed in R₂、
  **Hall-Wielandt (p = 3 > 2, A abelian 版)**: `G/O³(G) ≅
  R₂⟨s⟩/O³(R₂⟨s⟩)` → (B2) と矛盾 2 連で Theorem B 完結

## Hall-Wielandt の所在 (2026-07-21 調査)

- statement は Peterfalvi p. 108 に明記: P Sylow p、A weakly closed in
  P rel G、`A ⊆ Z_{p−1}(P)` or `p > 2 ∧ A abelian` ⟹
  `G/O^p(G) ≅ N_G(A)/O^p(N_G(A))` ([Ha] Thm 14.4.2)
- Gorenstein は §7.6 で「M. Hall [1] pp. 206–212 参照、本書では証明せず」
  — **references/ に M. Hall・Huppert とも無し**。Coq odd-order にも無し。
  Isaacs FGT は weakly closed を演習 5C.6 のみ (Grün 周辺 p.163)。
- (12) 用は上記のとおり Cor 10.2 で回避可能。**(17) 用の
  「p > 2 ∧ A abelian weakly closed」版が真の新規 infra** (shared:
  Isaacs/Ch10 delta → 9300 claim を検討)。証明再構成は transfer/fusion
  標準論法 + 必要なら ChatGPT 相談・ユーザーへ Hall 原文追加依頼を報告。

## やること (文書順 + 上流優先)

- [x] Ch.II hypothesis carrier — `FirstCaseHypothesis` (FirstCase/Basic.lean,
      `4a2fede50`): (B1) は「C_G(P) 内 EA-2 部分群 ≤ 2」形。
      p_odd / P ∩ W = ⊥ / C_{Q₀}(P) ≤ 2 も同 leaf
- [x] (1) **完了 (2026-07-21)** — 全 5 主張 sorry 0・axiom-clean・
      AxiomsCheck 6 本登録
  - [x] |Q₀| = 2^p (FirstCase/FieldAction.lean `card_Q0_eq_two_pow`,
        `a39140c69`): P ↪ V̄ (toVbar) → semilinear model 消費 →
        固定体 = F₂ (B1) → Artin で [F : F₂] = p
  - [x] C_K(P) = 1 (StepOne `K_inf_centralizer_eq_bot`, `42ed5777d`);
        |C_{Q₀}(P)| = 2 (StepOne `card_Q0_inf_centralizer_eq_two`,
        軌道計数+Fermat, `c89a19234`); FieldAction は
        `exists_adapted_field_model` bundle (eQ/μ/σhom + 固定元 0∨1) に
        リファクタ済
  - [x] V = W ⋊ P (`W_join_P_eq_V` + `exists_decomp_of_mem_V`;
        |V̄| ∣ |Aut F| = p は natCard_ringAut_eq_finrank + char-2 同定)
  - [x] N_G(P) = C_G(P) (`normalizer_P_eq_centralizer`; Prop 1(b) +
        W∩N(P) ≤ C(P) の commutator トリック) と
        C_D(P) = C_W(P) × P (`D_inf_centralizer_eq_W_inf_centralizer_join_P`;
        D̄ = fitting ⋊ V̄ の成分分離 + `fitting_eq_one_of_conjAction_fixed`)
- [x] (2) C_G(P) の near-field 構造 — StepTwo.lean (`c022a3d01` +
      `e4e7eb646`): `exists_four_subgroup_of_quotient` (奇数 kernel の
      EA-4 lift)、`rankOneQuotient` (RankOneHypothesis、sorry 0)、
      `exists_affineNearFieldModel` (App C Prop 1 sorried-cite — 9318 待ち)。
      ⚠ NearFields → Suzuki hub の import のため StepTwo は root/AxiomsCheck
      直接配線 (hub 経由は cycle)
  - **設計 (2026-07-21 調査)**: (2)(a) は §3 Prop 1(a) 部品
    (`centralizerHypothesisA1 (X := P)` : HypothesisA1 C_G(P) Ω_P、
    CentralizerInduction.lean:246) + kernel N = C_D(C_Q(P)) ∩ C_G(P) の同定。
    (2)(b) は faithful 商 C_G(P)/N に `RankOneHypothesis` (NearFields.lean:652;
    (A1)+(A2)+2-rank-1、2-rank-1 は (B1) から) を構成し
    **`rankOne_affine_nearField` (App C Prop 1) を sorried-cite** して
    `AffineNearFieldModel` を得る。
  - ⚠ `rankOne_affine_nearField` は honestly-stated **sorry** (NearFields:741)。
    未形式化前提 = (i) Huppert III 8.2 (2-rank 1 → Sylow-2 cyclic/quaternion)、
    (ii) **Brauer–Suzuki** (G = O_{2'}(G)·C_G(u))、(iii) Huppert II 3.2
    (normal complement)。方針 = sorried-cite で Theorem B の下流を実証明しつつ、
    Brauer–Suzuki 形式化を独立 campaign として起票 (shared infra、9300 claim)
    - **📌 2026-07-22 hub 裁定更新**: (i)(iii) は c が完了済 (9404 closed)、
      (ii) = **issue 9318 は b → c に移管** (ユーザー裁可、issues/9318 冒頭
      HUB RULING)。b は本 campaign で `rankOne_affine_nearField` を
      sorried-cite し続けるだけでよい (producer = c、b 側の追加作業なし)
- [ ] (3) 素因数の合同条件
  - **被覆調査 (2026-07-21)**: (i) Q₁ = `hyp.Q1` (SylowDecomposition.lean:89、
    Q1Subgroup + sylowTwoProdQ1MulEquiv で S × Q₁ 分解済) ✓。
    (ii) [Is] 15.16 (dim M = |P|·dim C_M(P)) 相当 =
    `finrank_eq_card_mul_finrank_invariants_kernelFPF` (WielandtKernelFPF:303)
    ほか free/freeBlock 3 変種 — 適合形の確認要 ✓ 有望。
    (iii) [H] V 8.15 (Frobenius complement の pq-部分群 cyclic →
    dim C_M(P) = 1 で使用) — **無ヒット、ギャップ**。ただし使用点は
    「C_M(P) の 1 次元性」1 箇所で、KP ≤ 近傍の cyclic 性など別供給も
    検討余地あり。
    (iv) App I Prop 2 = SemilinearField.lean「Proposition 2(a)」✓。
    次: (ii) の正確な適合確認 → M (極小 EA r-部分群) の存在と KP-正規化の
    構成 → (iii) ギャップの扱い決定
  - **適合確認済 (2026-07-21)**: kernelFPF 変種が完全適合 — L := KP、
    U := K (normal)、E := P、k := ZMod r、W := M (additive)。
    invariants(ρ|K) = ⊥ は conjQByK_fixed_eq_one (K fpf on Q)。
    結論 dim M = p·dim C_M(P) で **C_M(P) ≠ 0 も dim 等式から従う**
    (原文の Frobenius 論法不要)。dim C_M(P) = 1 は原文どおり (2)(b) の
    near-field 構造経由 = sorried 継承側。M 存在 =
    MinimalInvariantNormal (exists_aInvariant_normal_isElementaryAbelian 系)。
    実装プラン: StepThree.lean で (a) M 存在、(b) dim 等式 (sorry-free 側)、
    (c) Clifford 二分岐 + App I Prop 2 + (2)(b) 消費 (sorried 継承側) の順
  - **進捗 (2026-07-22, commit 760be19d9)**: (b) dim 等式 =
    `card_eq_card_inf_centralizer_pow` (f8954166a)、`|C_M(P)| = r` =
    `card_inf_centralizer_eq_prime` (9318 継承)。(c) Clifford 二分岐 =
    `exists_prime_order_invariant_or_irreducible` (9318 継承)、**第一分岐
    r ≡ 1 = `card_K_dvd_sub_one_of_prime_order_invariant` sorry-free 完了**
    (AxiomsCheck 登録)。残 = **第二分岐 (M が K-既約) → r ≡ 2^i**。
  - **第二分岐プラン (2026-07-22 精読 p.109 + infra 全確認、上流 gap 無し)**:
    3 部品に分解 (すべて既存 infra の assembly):
    - **Half A (Q₀ 側, M 非依存)**: `∃ i ≤ p-1, ∀ k∈K, a·k·a⁻¹ = k^(2^i)`
      (a = P の生成元)。供給 = `FieldAction.exists_adapted_field_model`
      (σhom : P →* RingAut F, F = 𝔽_{2^p}; μ : fitting(D̄) ≃* Fˣ; 共役律
      `μ(fittingConjAction (toVbar g) t) = fieldRingAutOnUnits F (σhom g) (μ t)`)
      + RingAut(𝔽_{2^p}) = ⟨Frobenius x↦x²⟩ 位数 p ⟹ σhom(a) = Frob^i
      + K ≅ K̄ = fitting(D̄) (`SemilinearIdentification.Kbar_eq_fitting`)。
      ⚠ fittingConjAction ↔ 実 K 上共役、K→fitting の橋が要工作。
      - **A1 (RingAut 𝔽_{2^p} = power-2, mathlib path 確定 2026-07-22)**:
        `frobeniusAlgEquivOfAlgebraic (ZMod 2) F : F ≃ₐ[ZMod 2] F`
        (Mathlib/FieldTheory/Finite/Basic.lean:367)、`orderOf = finrank = p`
        (`orderOf_frobeniusAlgEquivOfAlgebraic`) ⟹ Gal 生成、σ = Frob^i、
        `coe_frobeniusAlgEquivOfAlgebraic_iterate` で σ(x) = x^(2^i)。
        friction 4 点: (1) CharP F 2 を Nat.card F = 2^p から (2 prime)、
        (2) Algebra (ZMod 2) F instance (CharP 経由; `ZMod.algebra`?)、
        (3) RingAut F → (F ≃ₐ[ZMod 2] F) 橋 (prime field 固定ゆえ自動、
        `AlgEquiv.ofRingEquiv` + commutes)、(4) orderOf = card ⟹ 全元が冪
        (`mem_powers`/`zpowers_eq_top`)。汎用ゆえ将来 leaf 化候補だが当面
        StepThree.lean 内 section。
    - **Half B (M 側)**: `∀ k∈K, a·k·a⁻¹ = k^r`。供給 =
      `SemilinearField.exists_field_semilinear` (F' = 𝔽_{r^p} on M,
      K ↪ F'ˣ (M 1-dim over F', K が F'-linear), a は σ-semilinear で
      σ = Gal 生成元 = Frobenius x↦x^r; 共役 k ↦ σ(k) = k^r)。⚠ 最重量。
    - **Combine**: k^(2^i) = k^r ∀k∈K cyclic 位数 2^p−1 ⟹ r ≡ 2^i (mod 2^p−1)。
    - **package (3)**: |Q₁| の素因数 r ⟹ ∃i, r≡2^i (第一分岐 i=0 + 第二分岐)。
    (iii) の [H] V 8.15 ギャップは「dim C_M(P)=1」= 2(b) near-field 経由で
    9318 継承、独立ギャップではない。
  - **進捗 (2026-07-22): 第二分岐 4/5 完了 (StepThree.lean, hB パラメータ化で sorry-free)**:
    A1 `ringAut_card_two_pow_eq_pow` (f444719e0)、Half A
    `exists_pow_two_fittingConjAction` (ec7f1be5c)、A2
    `fittingConjAction_pow_of_K_conj` (9407e5de2)、combine
    `exists_pow_two_modEq_of_K_conj` (131319f5b: hB → ∃i r≡2^i)。
  - **Half B 完了 (2026-07-22)**: `exists_K_conj_pow_of_irreducible`
    (StepThree.lean 末尾) — M K-既約 ⟹ ∃ a∈P, ∀k∈K a·k·a⁻¹=k^r。
    実装 = `exists_field_semilinear_with_scalar` (App I Prop 2(a)+(b) の
    μ : K→*F'ˣ 保持版; E:=↥M, T:=↥K, ψ:=正規化共役) で F'=𝔽_{r^p} を取得、
    μ 単射 (fpf `conjQByK_fixed_eq_one`)、生成元 a₀ の共役が σ-semilinear、
    σ=x↦x^{r^j} (`ringAut_card_prime_pow_eq_pow` q:=r)。p∣j なら σ が Fˣ 固定
    → a₀ が K 中心化 → `K_inf_centralizer_eq_bot`+|K|=2^p−1>1 で矛盾;
    さもなくば m=j⁻¹ (mod p) で a:=a₀^m が Frobenius = x↦x^r → μ 単射で
    K に転送。9318 継承 (`card_inf_centralizer_eq_prime` 経由) ゆえ
    AxiomsCheck 非登録。
  - **package (3) 完了 (2026-07-22) → step (3) 完結**:
    `exists_pow_two_modEq_of_prime_dvd_card_Q1` (StepThree.lean 末尾) —
    r ∣ |Q₁| prime ⟹ ∃i, r ≡ 2^i [MOD 2^p−1]。M の存在+極小性 =
    `exists_minimal_invariant_elab` (Q1MinimalInvariant, X := K⊔P ≤ H) が
    丸ごと供給、dichotomy 消費、第一分岐 = `card_K_dvd_sub_one...` の
    (2^p−1) ∣ (r−1) を Nat.modEq_iff_dvd' で r ≡ 2^0 化、第二分岐 =
    Half B → combine。9318 継承 (AxiomsCheck 非登録)。
- [x] (4) **完了 (2026-07-22)** — `card_Q_eq_card_inf_centralizer_pow`
      (FirstCase/StepFour.lean 新設、root 配線済): |Q| = |C_Q(P)|^p。
      Wielandt = **Pf (9.1) 実装済** (`wielandt_fixedPoint_trivial_U_fixed`,
      sorry-free) を消費 — port 不要だった。carrier `CoprimeFrobeniusAction`
      (L = K⊔P, U = K, E = P) を組立: Frobenius 構造 =
      `isFrobeniusGroup_of_prime_complement_fixedFree` (C_K(P)=1)、
      C_Q(K)=1 = fpf、coprime = `coprime_card_Q_K` + **p ∤ |Q|**
      (`not_p_dvd_card_Q1`/`not_p_dvd_card_Q`: step (3) の合同 r≡2^i と
      p odd の矛盾 — 書籍の「r ≠ p は (3) の帰結」を形式化)。9318 継承。
- [x] (5) **完了 (2026-07-22)** — `card_nearField_eq_nine_and_Q1_eq_bot`
      (StepFive.lean, FirstCaseHypothesis): `(∀ x y : F, comm) ∨ (|F| = 9 ∧
      |C_Q(P)| = 8 ∧ Q₁ = ⊥)`。本体 sorry-free (Higman `pow_four` + 9318 model
      継承のみ)。詳細は末尾「step (5) 完了記録」。
- [ ] (6)–(9) — **(6)(7)(8) 完了, 残 = (9) `p = f`**
  - **(6) 体の場合 完了 (2026-07-22)** — `card_field_eq_and_D_eq_one_of_comm`
    (axiom-clean ∀-model): Q₁=1, F 可換 ⟹ (|F|=char ∨ |F|=9) ∧ |D|=1。
    部品完備: arithmetic + ringAut_sq + fieldOfComm + 抽象核 + `dAutHom`
    (dAut→RingAut 群 hom, crux) + `card_Q_eq_two_pow_of_Q1_eq_bot`。全 StepSix.lean。
  - **(6) 全体形 landing (2026-07-22)** — `card_field_and_D_of_Q1_eq_bot`:
    Q₁=1 ⟹ (可換 → (|F|=char∨9)∧|D|=1) ∧ (非可換 → |D|∈{1,3})。field case は
    実証明、`card_D_le_three_of_noncomm` (非可換=F_{9,2}) は **gated sorry**
    (Aut(F_{9,2}) 奇部分=3、F*=Q₈ ゆえ; near-field Aut infra 無し、D_odd は在り
    |D|∣3 だけ欠く; shared 9300 候補)。StepSix の唯一の sorry。
  - **(7) 完了 (2026-07-22, FirstCase/StepSeven.lean 新設・root+AxiomsCheck 配線)** —
    `N = P ∧ Σ ≅ C_W(P)` (p. 110)。3 commit:
    - **decomposition (axiom-clean)**: `kernelN` (= book の N = `(H.subgroupOf L).normalCore`
      を L↪G で map)、`P_le_kernelN` (P ⊆ C_{D_L}(Q_L)=N)、`kernelN_le_V`
      (N ≤ C_D(P)=C_W(P)·P ≤ V)、`kernelN_eq_kernelInf_W_join_P` (`N=(N∩W)⊔P`、
      n∈N⊆V を exists_decomp で g·w 分解、g∈P⊆N ⟹ w=g⁻¹n∈N∩W)、
      `kernelN_eq_P_of_kernelInf_W_eq_bot` (N∩W=1 ⟹ N=P)。
    - **f = char (axiom-clean ∀-model)**: `orderOf_st_eq_char` — s̄,t̄ (π(s),π(t) in L/N)
      が distinct involution (s∈Q∖D / t∉H⊇D / st⁻¹∉H) ⟹ char=|s̄t̄|
      (`model.orderOf_mul_of_involutions`) ⟹ (st)^char∈N ⟹ odd-kernel bridge
      `orderOf_mul_eq_prime_of_pow_mem_odd_kernel` で |st|=char。書籍の "(2), §1 Prop 4(c)
      + App II Prop 1"。 ⚠ 当初懸念した「quotient 用 hA3 が (B1) で偽」問題は core bridge
      が qhyp 不要ゆえ回避 (X=P で直接適用可)。
    - **|C_Q(X)| readoff (axiom-clean)**: `Hypothesis.cQ_card_and_pGroup_of_trichotomy` —
      `centralizer_trichotomy_of_induction` を branch cases 展開、
      `|C_Q(X)|=|C_{Q₀}(X)|^k` (k=1,2,3) を `distinguishedProduct_order`(f=3/5/3) と対で返す。
    - **contradiction (sorryAx: 9318+Higman)**: `kernelN_inf_W_eq_bot` — X=N∩W≠1 仮定、
      X≤W が Q₀ 中心化 ⟹ C_G(X) に four-subgroup ⟹ trichotomy。R=C_Q(X) 2群 +
      C_Q(P)⊆R ⟹ C_Q(P) 2群 ⟹ (step4) Q 2群 ⟹ Q₁=1 (**Q₁=1 は仮定でなく導出**、
      当初の解釈修正)。step(5)/(6) で `|C_Q(P)|∈{2,8,4}` + `cQ_card_cases_of_Q1_eq_bot`
      (`c=char-1 ∨ (c=8∧char=3)`、|F|=9⟹char=3 は addOrderOf で導出)。faithful
      (`centralizer_Q_inf_D_eq_bot`) ⟹ R⊊Q; Q₀⊆R strict when c>2 (|C_{Q₀}(P)|=2)。
      5 consistent (k,m) 組を `step_seven_numeric` (2冪 exponent 比較) で全消去。
    - **Σ ≅ C_W(P) (sorryAx: kernelN_inf_W_eq_bot 経由)**: `sigma_mulEquiv_centralizer_W` —
      `rankOneQuotient.D = (D_L).map(mk' N)` (rfl!)、`w↦[w]` が iso (inj = C_W(P)∩N⊆W∩N=1、
      surj = C_D(P)=C_W(P)·P + P⊆N)。assembly = `N_eq_P_and_sigma_mulEquiv_centralizer_W`。
    - 数学的には step (7) 完結。sorryAx は 9318 (model) + Higman (step5 F_{9,2} 枝、lane a)
      の legitimate 上流 sorried-cite のみ。
  - **(8) 完了 (2026-07-22, FirstCase/StepEight.lean, root+AxiomsCheck 配線)** —
    `Q₁≠1 ∧ ℓ=|Σ|≠1 ⟹ ℓ prime ∧ |F|∈{3^ℓ,5^ℓ,9^ℓ}` (p. 110)。endpoint =
    `card_prime_and_card_field_of_Q1_ne_bot` (sorryAx=9318+Higman)。以下 sub-lemma 群:
    - `comm_of_Q1_ne_bot` (∀-model, sorryAx=9318+Higman): 「By (5), F is a field」—
      step5 の dichotomy (comm ∨ F_{9,2}∧Q₁=1) から Q₁≠1 ⟹ comm。
    - `st_mem_and_cQ_isPGroup_of_mem_centralizer_W` (**axiom-clean**): w∈C_W(P)#
      で trichotomy を X=⟨w⟩ に適用 ⟹ f=|st|∈{3,5} ∧ C_Q(w) 2群。readoff の直接消費。
    - **fixed-field arithmetic heart 完了 (2026-07-22, axiom-clean, model-free)**:
      `exists_card_fixedSet_eq_char_pow` (σ:F≃+*F 固定集合を AddSubgroup で構成 →
      additive Lagrange で |{x:σx=x}|=f^a) + `card_fixedSet_mem_of_units_two_pow`
      (固定単位 2^b群 ⟹ f^a=2^b+1 ⟹ |固定体|∈{f,9}、step6 算術補題)。書籍の
      「|C_F(w)|=f^a=2^b+1 ⟹ ∈{f,9}」を model 非依存に切り出し済。
    - **equivariance linchpin 完了 (2026-07-22, axiom-clean, model-general)**:
      `model_dAut_one`/`model_dAut_hom`/`model_dAut_inv_cancel` (dAut は D→Aut(F) 群 hom) +
      **`model_qEquiv_conj`** (crux: g∈D,q∈Q で `qEquiv(g q g⁻¹) = dAut g (qEquiv q)`、
      emb(1) を g q g⁻¹ 共役して dAut_conj/qEquiv_conj で unwinding、emb/ofAdd 単射)。
      consumables: `ringEquivOfAddEquivMul` (dAut g を RingEquiv 化) +
      `card_fixedSet_eq_card_fixedUnits_add_one` (|{x:σx=x}|=|fixed units|+1) +
      heart 2 本。**crux 全部 done — 残りは mechanical assembly**。
    - **(B) 完了 (2026-07-22)**: `card_fixedUnits_eq_card_fixedConj` (axiom-clean,
      model-general) — qEquiv + model_qEquiv_conj で `{u:Fˣ//dAut g ↑u=↑u}` ≅
      `{q:↥Q//[g]q[g]⁻¹=q}`、card 一致。equivariance の直接 payoff。
    - **(C) 完了 (2026-07-22)**: per-`w` fixed-field order。3 宣言 (StepEight.lean 末尾):
      - `sigmaElt` (axiom-clean, def): w∈C_W(P) → [w]∈rankOneQuotient.D (=mk'N⟨w,hwP⟩、
        membership = mem_map_of_mem∘mem_subgroupOf∘V_le_D∘W_le_V)。σ_w は本体で
        `dAutHom hcomm model [w]` (step6 の D→*RingAut 橋を再利用、`ringEquivOfAddEquivMul`
        直書きより堅牢)。
      - `exists_card_fixedM0_eq_two_pow` (**axiom-clean**, AxiomsCheck 登録): w-fixed part of
        M₀=C_Q(P) は C_Q(w) 2群に属す ⟹ card = 2^b。実装 = fixed⟺centralizes⟨w⟩ (`hfix_iff`)、
        `{m:↥M₀//w-fixed} ≃ ↥(M₀.subgroupOf K)` (K=centralizer(zpowers w))、
        `M₀.subgroupOf K ≤ Q.subgroupOf K` (comap_mono) + st_mem の IsPGroup 2 で `to_le` +
        `exists_card_eq`。
      - `cardFixedField_char_or_nine` (**sorryAx=9318+Higman**): Q₁≠1 ⟹ 各 nonid w∈C_W(P) で
        `|{x:F//dAut[w]x=x}| ∈ {char, 9}`。chain = card_fixedUnits_eq_card_fixedConj ∘
        cardFixedConj_eq_cardFixedM0 ∘ exists_card_fixedM0_eq_two_pow で |C_{F*}(w)|=2^b、
        card_fixedSet_eq_card_fixedUnits_add_one で |C_F(w)|=2^b+1、b≥1 は char∈{3,5} odd から
        (fixedSet=char^a odd ⟹ 2^b+1 odd ⟹ b≥1)、heart `card_fixedSet_mem_of_units_two_pow`。
        Field 化 = `fieldOfComm hcomm` (hcomm=comm_of_Q1_ne_bot)、CharP F char は step6 導出流用。
    - **(D) 完了 (2026-07-22) → step (8) 完結**: `card_prime_and_card_field_of_Q1_ne_bot`
      (**sorryAx=9318+Higman**、∀-model): `Q₁≠1 ∧ ℓ=|Σ|=|C_W(P)|≠1 ⟹ ℓ prime ∧
      |F|∈{3^ℓ,5^ℓ,9^ℓ}`。汎用 axiom-clean 3 補題 (StepEight top、AxiomsCheck 登録):
      - `card_eq_card_fixedPoints_pow_orderOf` (Artin): σ:RingAut(有限体) で
        `|F|=|{x:σx=x}|^{orderOf σ}`。zpowers σ の MulSemiringAction + `FixedPoints.finrank_eq_card`。
      - `isCyclic_ringAut_of_charP`: 有限体の `RingAut F` cyclic。RingAut F ↪ Gal(F/𝔽_q)
        (`AlgEquiv.ofRingEquiv`, prime field 固定) + Gal cyclic instance + `isCyclic_of_injective`。
      - `card_prime_of_isCyclic_forall_ne_one_orderOf`: cyclic 群で全 nonid 同位数 ⟹ card prime
        (`IsCyclic.card_orderOf_eq_totient` + `Nat.totient_eq_iff_prime`)。
      assembly: ψ=(dAutHom hcomm model).comp f (f:C_W(P)→*Σ、sigma_mulEquiv の f と同構成)、
      単射 (f 単射=kernelN∩W=⊥ + dAut_injective)。IsCyclic(RingAut F)⟹IsCyclic C_W(P)。
      constancy = 各 nonid w で |F|=char^{a_w·orderOf σ_w} (a_w∈{1,2}=step C+char_pow、
      orderOf σ_w odd=D_odd)、N=a_w·orderOf の parity が a_w 一意決定 ⟹ |C_F(w)| 一定。
      ⟹ orderOf σ_w 一定 ⟹ generator で ℓ prime + |F|=|C_F(g)|^ℓ、|C_F(g)|∈{3,5,9}。
  - **(6) 算術補題 完了 (2026-07-22, StepSix.lean 新設)**:
    `eq_one_or_pow_eq_nine_of_pow_eq_two_pow_add_one` (axiom-clean, AxiomsCheck
    登録) — [HB] IX 2.7: `f 奇 ∧ f^a = 2^b+1 (b≥1) ⟹ a=1 ∨ f^a=9`。純 ℕ 算術
    (幾何和の偶奇で a 偶 → (f^c-1)(f^c+1)=2^b で 2 冪 → f^c=3)。steps (6)/(8) が消費。
  - **(6) 体の場合 crux 完了 (2026-07-22)**: `ringAut_sq_eq_one_of_card_prime_or_prime_sq`
    (StepSix.lean, axiom-clean, AxiomsCheck 登録) — 有限体 F (位数 q or q²) の
    RingAut は exponent ≤ 2 (∀σ, σ²=1)。`ringAut_card_prime_pow_eq_pow` (σx=x^{q^i})
    + `FiniteField.pow_card_pow` (x^{|F|^i}=x)。⟹ Σ 奇位数 ↪ exponent-2 群 → Σ=1。
  - **(6) 本体 assembly プラン (2026-07-22 精査済)**: model 上で 2 分岐 (letI-prefix,
    step 5 と同型)。**核心の ungated/gated 判定完了**:
    - **体の場合 (F 可換) = ungated だが plumbing 多層**:
      (i) NearField 可換 → Field インスタンス橋 = **未整備** (`nearField_field_structure_of_index_two`
      は別型 K を返すのみ; `NearField.mul_add_of_mul_comm` で distributivity はある →
      Field 構造を F 上に直接構成する def が要る)。
      (ii) dAut g (F≃+F 乗法的) → RingAut F (体なら ring equiv)、D →* RingAut F 単射。
      (iii) |F*| = |C_Q(P)| が 2 冪 (Q₁=1 ⟹ Q=Sylow-2 2群) → |F|=|F*|+1=2^b+1 →
      **arithmetic lemma** で |F|∈{f,9} → **ringAut_sq_eq_one** → Σ 奇 → Σ=1。
    - **F_{9,2} の場合 = gated (深い near-field Aut)**: `Twisted`/`TwistData` に
      automorphism infra 無し。「Aut(F_{9,2}) 奇部分 = 3 (F*=Q₈ ゆえ)」は sorried-cite
      (shared 9300 claim 候補) or 独立 campaign。arithmetic lemma・ringAut_sq は供給済。
    - 供給済 upstream: arithmetic lemma, ringAut_sq_eq_one。残 = (i) Field 橋 +
      (ii) dAut→RingAut + (iii) |F*|=2冪 plumbing + F_{9,2} sorried-cite。
  - **(5) 被覆調査 (2026-07-22): 3 部品すべて実装済、assembly のみ**:
    (i) Ch.I §2 Cor = `sylowTwo_isMulCommutative_or_isSuzuki2Group`
    (Suzuki/SylowTwo.lean:60、S 可換 or Suzuki 2-group)。
    (ii) App II Prop 2 = `cyclic_index_two_nearField_classification`
    (NearFields.lean:958、**proved axiom-clean 2026-07-21**: F*が指数2巡回
    部分群 → F field ∨ F≅F_{r²,2} ∧ |Z(F*)|=r−1)。
    (iii) [H] III 8.2 = `RankOneHypothesis.sylow_two_isCyclic_or_quaternion`
    (NearFields.lean:691、2-rank 1 → cyclic ∨ quaternion)。
    Suzuki 2-group 指数 4 = `higman_classification`
    (Appendices/Suzuki2Groups.lean:76)。
    証明筋 (p. 109–110): C_Q(P) 非可換 → C_S(P) 非可換 → S Suzuki 2-group
    (可換なら C_S(P) 可換) → exp 4 + 2-rank 1 → C_S(P) quaternion order 8
    → F* ≅ C_Q(P) が指数 2 巡回部分群を持つ → (ii) で F≅F_{r²,2},
    |Z(F*)|=r−1 → |F*/Z(F*)|=4 (quaternion 構造) = r+1 → r=3, |C_Q(P)|=8
    → (4) より |Q|=8^p=|F*|^p... Q₁=1 は |Q|=2^{3p} 2-群化から。
    F の supply = StepTwo `exists_affineNearFieldModel` (9318 sorried-cite)
    経由 — (5) も 9318 継承。statement 形 = AffineNearFieldModel を ∀-model
    パラメータで消費 (letI-prefix statement)。
  - **(5) 部品 2 点完了 (2026-07-22, FirstCase/StepFive.lean 新設・root 配線)**:
    (i) `centralizer_inf_mulEquiv_units` — **C_Q(P) ≅ F*** (書籍の standing
    identification)。qEquiv ∘ (mk' N の Q⊓C_G(P) への制限)。単射 = N ≤ D_L
    + Q⊓D=1 (StepThree の ι イディオム)、全射 = Q̄ := map の定義から。
    (ii) `Q1_eq_bot_of_card_two_pow` — |Q| = 2^n → Q₁ = ⊥。
  - **(5) 抽象核 完了 (2026-07-22, 5641a66bf)**:
    `nearField_card_eq_nine_of_nilpotent_units` (StepFive.lean, 本体
    sorry-free) — F near-field + Fˣ nilpotent + 2-rank 1 + 2-元指数 4 +
    非可換 → |F| = 9 ∧ |F*| = 8。helper 3 点 (c4e069e7b):
    `pow_four_eq_one_of_isSuzuki2Group` (**Higman sorried-cite**、lane a
    campaign 待ち)、`card_center_eq_two_of_card_eq_eight`、
    `isCyclic_odd_pSubgroup_of_nearField_units`。
    残 = **fc-level assembly**: ⚠ hexp4 の供給は S Suzuki 経由なので
    F-可換で場合分けしてから: F 非可換 → **抽出補題** (要実装:
    `exists_noncommuting_two_elements_of_nearField_units` — abstract 証明の
    prefix (O/T 分解 + hTnc) を再利用して Fˣ の非可換 2-元 pair を返す)
    → e.symm で Q の非可換 2-元 → S 非可換 →
    `sylowTwo_isMulCommutative_or_isSuzuki2Group` で S Suzuki → 全 Q の
    2-元が指数 4 (2-元 ∈ S) → hexp4 供給 → 抽象核 → |C_Q(P)| = 8
    (`centralizer_inf_mulEquiv_units` で転送) → step (4) で |Q| = 8^p =
    2^{3p} → `Q1_eq_bot_of_card_two_pow` → Q₁ = ⊥。
    最終形: `(∀ x y : F, comm) ∨ (card F = 9 ∧ card C_Q(P) = 8 ∧ Q₁ = ⊥)`。
  - **step (5) 完了記録 (2026-07-22)**:
    - 抽象核の O/T 分解 prefix を共有補題 **`exists_nilpotent_units_sylowTwo_decomp`**
      (axiom-clean) に括り出し、抽象核と抽出補題が共に消費 (二重化回避、
      抽象核は signature 不変で内部だけ差し替え・regression 無)。
    - **`exists_noncommuting_two_elements_of_nearField_units`** (axiom-clean):
      nilpotent 非可換 near-field の Fˣ から非可換 2-元 pair (共に 2-元)。
    - **`card_nearField_eq_nine_and_Q1_eq_bot`** (∀-model, letI-prefix):
      hnc で場合分け → 非可換なら抽出補題 → `toQ = incl∘e.symm` で C_Q(P)≤Q へ
      転送 → `mem_sylowTwo_of_orderOf_two_pow` で S 到達 → S 非可換 →
      `sylowTwo_isMulCommutative_or_isSuzuki2Group` で S Suzuki →
      `pow_four_eq_one_of_isSuzuki2Group` で hexp4 供給 → 抽象核 → |F|=9,|Fˣ|=8
      → `centralizer_inf_mulEquiv_units` で |C_Q(P)|=8 → step(4) で |Q|=8^p=2^{3p}
      → `Q1_eq_bot_of_card_two_pow`。hnil = Q nilpotent の subgroup を e で転送、
      h2rank = (B1) を e.symm で転送。
    - #print axioms 実測: 抽象核・bundle・extraction = clean (hexp4 は仮説ゆえ
      Higman 非依存)、conclusion のみ sorryAx (pow_four 経由)。
    - AxiomsCheck: StepFive を import 追加、clean 3 本を登録 (conclusion は
      Higman+9318 継承ゆえ意図的に非登録、注記済)。
- [x] (9) `p = f` — **transfer 半分 + endgame 完了 (2026-07-22)、残 = 構造ゲート 1 本**:
  - **算術半分** (既済): `char_eq_p_of_p_dvd_card_Q_add_one` (sorryAx=9318 through model):
    `p∣|Q|+1 ⟹ char=p`。|Q|=|C_Q(P)|^p (step4) + |C_Q(P)|=|F|−1 (units) ⟹ Fermat ⟹ p∣|F|
    ⟹ additive Cauchy + char_spec ⟹ p=char。near-field F でも成立 (additive 経路)。
  - **transfer 半分 完了 (axiom-clean)**: 予想と違い `transfer_eq_pow` の key 条件 (universal
    weakly-closed) は不要だった。真の機構 = **transversal `R = {1}∪{ty}` が x∈P 共役で不変**
    (`x∈V=C_D(t)` が t 中心化 + Q normal ⟹ `x⁻¹(ty)x=t(x⁻¹yx)`)。→ 汎用補題
    **`OddOrder.GroupTheory.transfer_eq_pow_of_conj_invariant_transversal`**
    (`GroupTheory/TransferInvariantTransversal.lean` 新設・root 配線): 左 transversal が x 共役
    不変なら `transfer ϕ x = ϕ(x)^[G:H]` (mathlib 左 transversal で `x•S=S·x` を示す、
    axiom-clean・reusable)。右版 corollary + `isComplement_inv_of_isComplement` も。
    - `CanonicalForm.lean`: `rightTransversalTQ`={1}∪{ty} + `isComplement_H_rightTransversalTQ`
      (Prop 4(a) を IsComplement 化、`exists_canonicalForm`+`canonicalForm_unique` から)。
    - `StepNine.lean`: `rightTransversalTQ_conj_invariant` (R が x∈P 共役不変) +
      **`transfer_eq_pow_card_Q_add_one`** (`transfer ϕ x = ϕ(x)^{|Q|+1}`、[G:H]=|Ω|=|Q|+1)。
  - **endgame 完了 (axiom-clean)**: **`p_dvd_card_Q_add_one`** — ϕ=Abelianization.of:H→H^ab。
    `T=transfer ϕ` は可換群への hom ゆえ `⁅G,G⁆≤ker T`；(B2)=`p∤|G^ab|` で p-元 x∈⁅G,G⁆ ⟹
    `T(x)=1`；`T(x)=ϕ(x)^{|Q|+1}` かつ `P∩⁅H,H⁆=1` で `ord ϕ(x)=p` ⟹ `p∣|Q|+1`。
    **`char_eq_p`** = p_dvd + 算術半分の連結 (= step (9) `p=f`、model sorry 継承)。
  - **構造ゲート `P∩⁅H,H⁆=⊥` 完了 (2026-07-22、axiom-clean)** = 書籍の `P∩QKW=1` (∵ `⁅H,H⁆≤QKW`):
    `P_inf_commutator_H_eq_bot` (StepNine.lean)。機構 = 保持 hom `hToAbDbar : ↥H→*Abelianization Dbar`
    (`Abelianization.of ∘ mk'_W ∘ hToD`) が `⁅H,H⁆` を殺すが `P^#` 上非自明。部品:
    - `QD_isComplement_in_H` (H=Q⋊D、`isComplement'_subgroupOf_of_disjoint_mul_eq_univ`) +
      **`hToD:↥H→*↥D`** (Q-kill 保持、`dToV` clone) + `QsubgroupOfH_normal` instance。
    - 非自明性 `hToAbDbar_ne_one_of_mem_P`: x∈P# の Dbar 像は Vbar (既存 `toVbar`) ∈、≠1
      (`P∩W=⊥`)、∉ Kbar=fitting Dbar⊇commutator Dbar (`Kbar⊓Vbar=⊥`、`fitting_Dbar_cyclic_fpf_abelian.2.2`)。
    - **`p_dvd_card_Q_add_one`/`char_eq_p` は hPinj 仮説を撤去** → char_eq_p は **hB2 + model のみ**。
  - **残 = hB2 (B2 standing 仮説) の carrier 化のみ** (ゲートでない): `p∤|G^ab|` = 「index-p 正規
    部分群なし」。Theorem B が全体で仮定するので step (17) 組立時に carrier/statement で threading。
    (否定側は Ch.I §3 Prop 2 = InductionNonSimple で処理済。) model sorry は 9318 継承。
- [x] (10) 二分岐 — **完了 (2026-07-23、FirstCase/StepTen.lean・StepFive.lean)**。
      endpoint = `step_ten_dichotomy` (`|F|=p^m` の下で (10.1) `¬p∣|Σ| ∧ |G|_p=p^{m+2}` ∨
      (10.2) `p∣|Σ| ∧ p=3 ∧ |F|=9 ∧ IsCyclic W ∧ |W|∈{3,9} ∧ 3^|G|_3=3^4·|W|`)。
      sorryAx=9318+Higman through model (AxiomsCheck 非登録)。
  - **arithmetic core (axiom-clean)**: `padicValNat_pow_sub_one_add_one` (LTE
    `v_p((N-1)^p+1)=v_p(N)+1`)、`card_field_eq_prime_pow` (|F|=p^m, m≥1、additive
    p-group)、`padicValNat_card_Q_add_one` (opening `(|Q|+1)_p = p^{m+1}`)。
  - **structural |G|_p (axiom-clean 群論部)**: `card_D_eq_card_Dbar_mul_card_W`
    (|D|=|D̄||W|)、`card_Kbar_mul_card_Vbar` (|D̄|=|K̄||V̄|)、`card_Kbar_eq_two_pow_sub_one`
    (|K̄|=2^p−1=|K|、Prop 2 経由)、`not_p_dvd_card_Kbar` (Fermat)、`card_Vbar_eq_p`
    (|V̄|=p、V=W⋊P の image)、`factorization_card_Dbar_eq_one`/`factorization_card_D_eq`
    → `factorization_card_G_eq` (model): **|G|_p = p^{m+2}·|W|_p**。
  - **(10.1) 完了 (model)**: `P_le_normalizer_W` + `not_p_dvd_card_W_of_not_p_dvd_card_centralizer_W`
    (P p群が W に共役作用、mod-p 固定点合同 `|W|≡|C_W(P)|`、fixedPoints≃W⊓C_G(P)、
    両 axiom-clean) → `factorization_card_G_eq_of_not_p_dvd_card_centralizer_W`:
    **p∤|Σ| ⟹ |G|_p = p^{m+2}**。
  - **(10) Q₁=1 (model)**: `Q1_eq_bot_of_p_dvd_card_centralizer_W` — p∣|Σ|∧Q₁≠1 で
    step8 の |F|∈{3^ℓ,5^ℓ,9^ℓ} → p∈{3,5}, |C_Q(P)|∈{26,3124,728} の奇素因数
    r∈{13,11,13} が step3 の r≡2^i mod(2^p−1) と矛盾 (`pow_two_mod_seven`/`pow_two_mod_31`
    + `dvd_card_Q1_of_odd_prime_dvd_card_Q` 全 axiom-clean helper)。
  - **(10.2) numeric core 完了 (model)**: `card_field_eq_nine_of_p_dvd_card_centralizer_W`
    — p∣|Σ| ⟹ **p=3 ∧ |F|=9 ∧ |C_Q(P)|=8 ∧ |Σ|=3** (step6 で可換 F は |Σ|=1 ⟹ 矛盾 →
    非可換 → step5 で |F|=9; step7 Σ≅C_W(P) で |Σ| 変換)。
  - **(10.2) 完了 (2026-07-23)**: `w_cyclic_of_p_dvd_card_centralizer_W` — p∣|Σ| ⟹
    p=3 ∧ |F|=9 ∧ IsCyclic W ∧ |W|∈{3,9} ∧ 3^|G|_3=3^4·|W|。3 部品:
    - **`isSuzuki2Group_Q_of_noncomm` (StepFive 新規、model-carrying)**: F 非可換 ⟹
      IsSuzuki2Group Q。|C_Q(P)|=8 (`card_nearField_eq_nine_and_Q1_eq_bot`) で |Q|=8^p=2^{3p}
      は 2-群 ⟹ 任意 Sylow-2 S=⊤ (`Sylow.card_eq_multiplicity`+`eq_top_of_card_eq`)、
      `↥S≅↥Q` (`subgroupCongr`+`topEquiv`)。非可換 units 2 個 (`exists_noncommuting_two_elements`)
      を Q へ転送 ⟹ Q 非可換 ⟹ `sylowTwo_isMulCommutative_or_isSuzuki2Group` で S Suzuki ⟹
      `IsSuzuki2Group.of_equiv eS` で Q Suzuki。⚠ `of_equiv` は full name
      `...SpecificGroups.Suzuki.IsSuzuki2Group.of_equiv` (dot notation は Suzuki2Group
      namespace を見るので不可)。
    - **`orderOf(st)=3`**: `orderOf_st_eq_char model` (step7) + char=3 (|F|=9 の additive
      order 論法、StepSeven パターン流用)。
    - **Lemma 5 消費**: m:=p, `card_Q0_eq_two_pow` (|Q₀|=2^p), |Q|=|Q₀|^3 (step4+p=3)。
      `lemmaFive_of_orderThree` ⟹ IsCyclic W ∧ |W|∣2^p+1=9。|Σ|=3∣|W| (`card_dvd_of_le`)
      で |W|≠1 ⟹ |W|∈{3,9} (`dvd_prime_pow`)。|G|_3 = `factorization_card_G_eq` (m=2) +
      |W|=3^k で 3^4·|W|。
- [x] (11)–(12) — **完了 (2026-07-25)**。(11) = StepTwelve.lean 前半 (R = T×P、
      𝒜 正則作用、index 定理は一般 m)。(12) = δ1–δ4 + ε1–ε3 (StepTwelve{,Endgame,
      Conclusion,Transfer}.lean) → **`step_twelve` (StepTwelveTransfer.lean,
      `e9256e1dc`): "Case (10.2) holds"** — (10.1) 下で m = 1 を index 定理
      (p^{2m+1} ∣ |G| → 2m+1 ≤ m+2) で導出し `factorization_ne_three` で排除。
      結論 = p=3 ∧ |F|=9 ∧ W cyclic ∧ |W|∈{3,9} ∧ |G|_3 = 3^4·|W|。
      ⚠ 書籍 (12) 中の Hall-Wielandt 言及は Cor 10.2 range-equality 直用で回避済
      ((17) 用 abelian 版とは別)。
- [x] **(13) — 完了 (2026-07-25)**: `exists_card_centralizer_st_eq_three_pow` /
      `isPGroup_three_centralizer_Z₁` (`54b472b8b`, 新 leaf
      `FirstCase/StepThirteen.lean`)。C_G(Z₁) は 3-群 (Z₁ = ⟨st⟩)。
      chain = (13-i) centralizer 恒等式 (`059f53f03`) → (13-ii)
      |C_G(st)| = |V|·|J| (`bd5484c64`) → (13a) Cauchy-in-J
      (`8330e0c13`, InvertedProduct.lean) + (13-iii-a/b) |J| の素因数は
      u·t の位数で |L| = |Q₀||K|(|Q₀|+1) を割る (`7b71b1839`/`77f4521f7`;
      |L| は `card_orderThreeGeneratedSubgroup` `d65f71609`) → (13-iv)
      r = |K| (=7) の排除 (`7c366997d` D = K ⋊ V / `393268394` 奇位数 →
      D / `06c49e107` 中核 / `49b196568` Sylow 輸送 / `216bb3f75` 本体) →
      (13-v) |J| = 3^n (`815653e8a`) + |V| = |P||W| (`ff2a73e33`) → assembly。
- [ ] (14)–(16)
- [ ] Hall-Wielandt abelian 版 (shared infra、claim してから)
- [ ] (17) 結論 → Theorem B assembly

## 完了条件

- Theorem B (`(B1) → Theorem A conclusion for G`) が sorry-free で
  landing、AxiomsCheck 登録

## 参照

- references/peterfalvi/pdf/05.4_pp_108_114_The_First_Case.pdf (全 7 頁)
- issues/closed/2048-pf-suzuki-lemma5.md (Ch.I 部品への pointer)
- OddOrder/Peterfalvi/Appendices/NearFields.lean (App II)
- OddOrder/Peterfalvi/Appendices/SemilinearField.lean (App I)
- OddOrder/Isaacs/Ch10_MoreTransfer/Yoshida.lean:509 (Cor 10.2)
- OddOrder/GroupTheory/WielandtPerFactorDischarge.lean (要調査)

---

## 📝 2026-07-24 hub 監査メモ (checklist が実装に遅行)

実測: `FirstCase/` に **StepNine.lean / StepTen.lean が既に存在**し、`OddOrder/Peterfalvi/
Appendices/Suzuki/FirstCase/**` は実 sorry 0。本文 checklist の「残 = (9) p = f」は遅行記述。
owner (lane b) が次回 sync 時に checklist を実状態へ更新し、Theorem B 最終 assembly の
有無 (`theoremB` 相当の endpoint 宣言) を明記すること。

---

## ❄ 2026-07-24 FROZEN (ユーザー裁定) — pending へ

Pf II Ch.II Theorem B campaign (lane b の現 frontier) はユーザー裁定で凍結。
凍結時点の実状態 = StepOne〜StepTen まで leaf 存在・`FirstCase/**` 実 sorry 0
(checklist は「残 (9) p=f」表記のまま遅行 — 解凍時に実測で再同期すること)。
Theorem B 最終 assembly の有無も解凍時に確認。lane b の次 frontier は hub 裁定で再割当。

---

## 🔓 2026-07-25 再活性化 (ユーザー指示)

ユーザーが本 issue を含む pending 4 件 (0106/0131/2053/8005) の再着手を指示。
pending の凍結/トリガー待ち/ユーザー判断待ちはいずれも解除 — main セッションが引き取る
(3 レーンとも 2026-07-23 から停止中・未マージ 0 を確認済、territory 衝突なし)。

## 📝 2026-07-25 解凍・実測再同期 (再活性化指示による)

- **FirstCase/** 全 12 file (Basic/FieldAction/StepOne〜StepTen) = 実 sorry 0** (comment-strip
  census で確認)。checklist の「残 = (9) p = f」は遅行 — **(1)〜(10) は全て完結済み**。
  StepSix の gated sorry (`card_D_le_three_of_noncomm`) も解消済み。
- **Higman Thm 1(a) landing 済** (lane b 最終 commit `bcf5dbfa2`):
  `pow_four_eq_one_of_isSuzuki2Group` (Higman/Suzuki2Groups/ExponentFour.lean) は sorry 0。
  StepFive の sorried-cite は実証明化された。
- **NearFields.lean = 実 sorry 0** — `rankOne_affine_nearField` 本体は証明済み。残る sorryAx
  経路は上流 **BS Q₈ (|S|=8)** のみ (= issue 0147、Navarro PDF 購入待ち)。Theorem B の
  axiom 状態はこれを継承する (sorried-cite 方針どおり、campaign は block されない)。
- **Theorem B 最終 assembly (`theoremB` 相当 endpoint) は未作成** (grep 0 件)。
- ⟹ **真の残作業 = steps (11)〜(17) + Hall-Wielandt abelian 版 (9500 claim 要) + assembly**。
  次の一手 = (11) R = T × P、C_Q(P) の A − {P} 正則作用 (p. 111)。

## 📖 2026-07-25 step (11)(12) 精読ノート (PDF pp. 111-112 直読、実装用)

**(11) statement**: R := F の G 内逆像 (= mk' P : C_G(P) → C_G(P)/P の下で F-並進部分群の
preimage、step (7) の N = P 使用)。主張:
(i) **R = T × P** — T は C_Q(P)·C_W(P) に正規化される部分群、**T ⋊ C_Q(P) ≅ F ⋊ F***。
(ii) **C_Q(P) は 𝒜 − {P} に正則作用** — 𝒜 := 「R の位数 p 部分群で T に含まれないもの」。

**(11) 証明**:
1. R abelian: 非可換なら [R,R]=Z(R)=P (C_Q(P) が F* に推移的)、N_G(R) ⊆ N_G(P)。
   - case (10.1): R が N_G(P) の (よって G の) Sylow-p、|R|=p^{m+1} が |G|_p=p^{m+2} と矛盾。
   - case (10.2): RC_W(P) が N_G(P) の Sylow-3; Σ が R/P≅F に非自明作用 ⟹
     Z(RC_W(P))=Z(R)=P ⟹ RC_W(P) が G の Sylow-3、|RC_W(P)|=3^4 が |G|_3=3^4|W|≥3^5 と矛盾。
2. T := [R, s] (s = involution)。R abelian ⟹ R = T × C_R(s) = T × P。
3. |𝒜| = (p^{m+1}−p^m)/(p−1) = p^m = |F|。正則性: a ∈ C_Q(P)^# が P₁ ∈ 𝒜 を正規化 ⟹
   a は T を正規化し R/T ≅ P を中心化 ⟹ [a,P₁] ⊆ P₁∩T = 1 ⟹ a が P₁ 中心化。
   a は R/P に fpf ⟹ C_R(a) = P ⟹ P₁ = P。

**(12) Case (10.2) holds** (= (10.1) を否定):
1. (10.1) 下で R は N_G(R) の Sylow-p でない ⟹ N_G(P) ⊊ N_G(R)。
2. 𝒜' := N_G(R) 下の P の軌道。P₁ ∈ 𝒜' ⟹ P₁^# は strongly real でない (Ch.I §3 Lemma 3、
   P と共役ゆえ)。T の元は s に反転される ⟹ P₁ ∩ T = 1 ⟹ {P} ⊊ 𝒜' ⊆ 𝒜。
   C_Q(P) の 𝒜−{P} 正則性 ⟹ 𝒜' = 𝒜。[N_G(R):N_G(P)] = |𝒜| = p^m ⟹ (10) より **m = 1、
   |G|_p = p³**。
3. N_G(R)/R 内: C_G(P)‾ = C_Q(P)‾ ⋊ C_W(P)‾、C_Q(P)‾ が 𝒜−{P} 正則、C_W(P)‾ が
   C_Q(P)‾ に忠実。**App II Prop 1 を N_G(R)/R ↷ 𝒜 に適用** ⟹
   N_G(R)/R = (R₁/R) ⋊ C_Q(P)C_W(P)、R₁ = G の Sylow-p、C_Q(P) が (R₁/R)^# に正則。
4. R₁ 非可換位数 p³ ⟹ class 2 < p ⟹ **Hall-Wielandt (= Isaacs Cor 10.2 で賄う予定、
   issue 本文の (12) 注記どおり)**: G/O^p(G) = N_G(R₁)/O^p(N_G(R₁))。
5. T ⊴ R₁ (N_G(R) が 𝒜 に推移的)。R₁/T = (R/T) × (T₁/T)、T₁ = [R₁/T, s]。
   𝒜₁ := R₁/T の位数 p 部分群で T₁/T と異なるもの。(11) と同様に C_Q(P) が
   𝒜₁ − {R/T} に正則 ⟹ N_G(R) ⊊ N_G(R₁) なら [N_G(R₁):N_G(R)] = |𝒜₁| = p が (10) と矛盾
   ⟹ **N_G(R₁) = N_G(R)**。T₁C_Q(P)C_W(P) が N_G(R₁) 内 index p 正規 ⟹ 4 と合わせ
   G に index p 正規部分群 ⟹ **(B2) 偽** ⟹ (10.1) 不成立。□

**実装設計メモ**:
- R の構成 = `(mk' P) ⁻¹' (F-並進部分群の像)` — StepTwo の `exists_affineNearFieldModel`
  bundle と step (7) `N_eq_P_...` の合流点。model の F-部分群を G に引き戻す comap 構成。
- (11) は FirstCase/StepEleven.lean 新設 (leaf 配線 = OddOrder.lean 追記を忘れない)。
- 使用部品: C_Q(P) の F* 推移性 (model qEquiv 経由)、s の反転作用 (Q₀ 系 =
  `model.orderOf_mul_of_involutions` 周辺)、fpf (`conjQByK_fixed_eq_one` 型)、
  (10) = `step_ten_dichotomy`。
- (12) の App II Prop 1 = NearFields.lean `rankOne_affine_nearField` (実 sorry 0、BS Q₈ 継承)
  を N_G(R)/R に再適用する形 — RankOneHypothesis の新しい実例化が要る。
- Ch.I §3 Lemma 3 (strongly real) の被覆確認が (12) 着手時の最初の grep 項目。

## 🚧 2026-07-25 step (11) 進捗 (FirstCase/StepEleven.lean、全 push 済)

**landing 済 (全て leaf+root green・警告ゼロ、∀-model 形で leaf 自体は axiom-clean)**:
- `invImageF` (R = emb(F) の mk' preimage の G 押し出し) + le_centralizer / P_le / mem_iff
- `conj_mem_invImageF` (R ⊴ C_G(P)、range_normal の comap)
- `addSubgroup_eq_bot_or_top_of_mul_units_mem` (near-field F*-右乗不変 → ⊥∨⊤)
- `conjInvariant_eq_bot_or_range_emb` (model-level、qEquiv_conj 消費; generic 形)
- `eq_P_or_eq_invImageF_of_conj_invariant` (G-level 二択、ind 消費で kernelN=P)
- `P_le_center_invImageF` / `commutator_invImageF_le_P` (⁅R,R⁆ ≤ N=P)
- `center_eq_P_of_not_isMulCommutative` (Z(R) = P、非可換時)
- `card_invImageF` (|R| = |F|·|P|、Lagrange×2 + index_comap)
- `normalizer_invImageF_le_normalizer_P` (N_G(R) ≤ N_G(P)、Z(R)=P の特性性)

**次 = R abelian の完成 (p. 111 証明 1 の残り = 位数矛盾)**。ポイント:
- **step (1) の `normalizer_P_eq_centralizer` (N_G(P) = C_G(P)) が使える** ⟹ 書籍の
  「R Sylow in N_G(P)」は C_G(P) の p-part 勘定に還元 (Aut(P) 埋め込み不要)。
- |C_G(P)| = |N'|·|F|·|Q̄|·|D̄| (Lagrange + model.isComplement.card_mul + Q_mul_D_eq_H)、
  p-part = p^{m+1} (p∤(p^m−1) + case (10.1) の p∤|Σ|)。
- (10.1): R < P₁ (Sylow_p G, p^{m+2}) → p-群の normalizer 成長 (mathlib 名要確認:
  IsPGroup 系 lt_normalizer) → N_{P₁}(R) ≤ N_G(R) ≤ C_G(P) が p-part 超過で矛盾。
- (10.2): RC_W(P) を 3-Sylow として同型の論法 (|RC_W(P)|=3^4 vs |G|_3=3^4|W|≥3^5)。
- その後: T := [R,s] 分解 (R abelian + s 反転) → |𝒜| = p^m → 正則性 (a fpf on R/P)。
- **(10.1) 側 R abelian 完了** (`a1b9159c3`): `invImageF_mul_comm_of_not_dvd_card_D`。
  次 = (10.2) 側 arm (p=3, RC_W(P) が N_G(P) の 3-Sylow、|RC_W(P)|=3^4 vs |G|_3=3^4|W|≥3^5)。
  部品はほぼ同型: card 勘定 (|R·C_W(P)| = |R|·|Σ|/...) + Σ の R/P への非自明作用で
  Z(RC_W(P)) = Z(R) = P。その後 step_ten_dichotomy を消費して無条件 R abelian。
- **R abelian 両 arm 完成** (`4cff5efb8`〜`8ca894010`): 共有 Sylow engine
  (`false_of_ppart_subgroup_center_P`) + (10.1) arm + (10.2) arm
  (Z(R·C_W(P)) = P は faithfulness core `eq_one_of_dAut_sigmaElt_eq_id` 経由)。
  次 = step_ten_dichotomy を消費する無条件 `invImageF_isMulCommutative`
  (|F| = p^m の供給 = card_field_eq_prime_pow + char_eq_p の hB2 threading に注意) →
  T := [R,s] 分解 → |𝒜| = p^m → C_Q(P) 正則性 → step (11) statement 完成。
- **step (11) 第一主張 (R abelian) 完成** (`71e1d3b12`): `invImageF_mul_comm` が
  step_ten_dichotomy 消費で両 arm を接続 (無条件、hB2 + |F|=p^m を threading)。
  p. 111-112 の (11) 証明 ¶1 が完全形式化。
  次 = **T := [R,s] 分解**: s = Q₀ 側の distinguished involution (StepSeven の s/t 系を確認)、
  R abelian + s が R を正規化 → T = {r·(s r s⁻¹)⁻¹ | r ∈ R}-型の構成 or [R,s] 部分群 +
  R = T × C_R(s) = T × P (C_R(s) = P は s-fixed part)。その後 𝒜 の定義と正則性。
- **R = T × P 分解完成** (`55906c7ee`): `exists_sInverted_complement` — T = s-反転部分群、
  T⊔P=R / T⊓P=⊥ / s-inverted。並進側の ψ(x)=x·u−x 単射→全射が核。
  残 (11): (i) T の C_Q(P)C_W(P)-正規化句 — c が s と可換なら即時; s の Q₀-中心性
  or unique_involution_in_H 経由で c s c⁻¹ = s を先に確立するのが筋。
  (ii) 𝒜 := {位数 p の R-部分群で T ⊄} の |𝒜| = p^m と C_Q(P) 正則性
  (a ∈ C_Q(P)# が P₁ ∈ 𝒜 を正規化 → [a,P₁] ⊆ P₁∩T = 1 → a が P₁ 中心化 →
  a fpf on R/P (u-乗の固定点なし) → P₁ = P)。
- **step (11) 全主張完成** (`a68f08548`〜、StepElevenComplement.lean):
  sInvertedT def 化 / spec (R = T×P) / C_Q(P)-正規化 (s ∈ Q0 中心性) /
  C_W(P)-正規化 (H̄ unique involution + N=P 補正) / freeness
  (`eq_P_of_prime_order_conj_invariant`)。regular の数え上げ形
  (|𝒜−{P}| = |C_Q(P)| = p^m−1) は (12) が要求する形で assembly 予定。
  **次 = step (12)**: (10.1) 仮定下で N_G(P) ⊊ N_G(R)、𝒜' = 𝒜 (strongly-real 排除 =
  Ch.I §3 Lemma 3 の被覆確認から)、[N_G(R):N_G(P)] = p^m → m=1 → App II Prop 1 再適用 →
  Isaacs Cor 10.2 → (B2) 矛盾。
- **step (12) 進捗**: strongly-real 3 補題 (`7f8e5063a`) + ↑R=↑T·↑P public 化 +
  R exponent p (`dae631f5a`)。
  **|𝒜| = p^m の設計 (一般 subgroup 計数を回避)**: 𝒜 ≃ T の complement bijection —
  t ↦ ⟨x₀·t⟩ (x₀ = P の生成元)。単射 = (x₀t)^k = x₀t' ⟹ x₀^{k−1} ∈ P∩T = ⊥;
  全射 = P₁ ∈ 𝒜 は P₁∩T = ⊥ (素数位数) で R/T ≅ P に同型に乗る ⟹ ξ = x₀·t ∈ P₁。
  orbit 論法は |𝒜−{P}| = p^m−1 = |C_Q(P)| + freeness で単一自由軌道 → 𝒜' = 𝒜。
  残り部品: N_G(P) ⊊ N_G(R) (Sylow 成長、engine の部品再利用) / orbit-stabilizer /
  m = 1 / N_G(R)/R への App II Prop 1 再実例化 / Isaacs Cor 10.2 bridge
  (transfer range → G/O^p 同型、issue 本文 (12) 注記) / (B2) 矛盾で (10.1) 否定。
- step (12) 続き (`52bce6ebc`/`8c1cba24f`): 𝒜 上界 (⟨x₀·t⟩ 生成) + N_G(P) ⊊ N_G(R)
  (case 10.1) + p∤|Q̄| helper。**次 = orbit-stabilizer**: N_G(R)-共役軌道 orbit(P) の
  |orbit| = [N_G(R) : N_G(P)] (stab = N_G(P): N_G(P) ≤ N_G(R) は landing 済の hle 部分) と、
  |orbit| = p^m の挟み撃ち (上界 = 𝒜↪T 全射性; 下界 = C_Q(P)-自由軌道
  eq_P_of_prime_order_conj_invariant + |C_Q(P)| = p^m−1)。mathlib の
  MulAction.orbitEquivQuotientStabilizer を Subgroup-conj 作用
  (MulAut.conj • : G ↷ Subgroup G の restriction) で使う。その後 m = 1 →
  |G|_p = p³ → App II Prop 1 再実例化 (N_G(R)/R) → Cor 10.2 bridge → (B2) 矛盾。
- **|𝒜| = p^m 完成** (`ncard_prime_order_not_le_sInvertedT` + card_sInvertedT/
  not_p_dvd_card_rankOneQ helpers)。step (12) 残 = orbit-stabilizer
  (N_G(R)-軌道 = 𝒜 の挟み撃ち: 上界 |𝒜| = p^m + 下界 C_Q(P) 自由軌道) →
  [N_G(R):N_G(P)] = p^m → m = 1 → App II Prop 1 (N_G(R)/R) → Cor 10.2 bridge → (B2)。
- **[N_G(R):N_G(P)] = p^m 完成** (`e1a47f1ea`): orbit-stabilizer 挟み撃ち monolith。
  数え上げ phase 完結。次 = 新 leaf StepTwelve.lean で m = 1 (index·|N_G(P)| の p-part
  = p^{2m+1} ∣ |G|_p = p^{m+2} → m ≤ 1; m ≥ 1 は F nontrivial) → |G|_p = p³ →
  App II Prop 1 の N_G(R)/R 再実例化 (RankOneHypothesis 構築が本体) →
  Isaacs Cor 10.2 (transfer_range_eq_of_nilpotencyClass_lt) bridge → (B2) 矛盾 →
  step_twelve endpoint「case (10.2) holds」。
- **m = 1 完成** (`a4b4ffdf7`、StepTwelve.lean 新設): case (10.1) 下で |F| = p、|G|_p = p³。
  **残 (12) 終盤 (次の設計課題)**: 書籍は N_G(R)/R の 𝒜 への作用に App II Prop 1
  (rankOne_affine_nearField) を適用 — RankOneHypothesis の新実例化が必要:
  (i) 𝒜 への N_G(R)/R-作用の 2-推移性 (書籍: C_G(P)‾ = C_Q(P)⋊C_W(P)、C_Q(P) が
  𝒜−{P} に正則 = 完成済の材料から)、(ii) 忠実性、(iii) 2-rank 1 の継承。
  結論 N_G(R)/R = (R₁/R) ⋊ C_Q(P)C_W(P)、R₁ = Sylow_p(G) 非可換 p³ class 2 < p →
  Isaacs Cor 10.2 (transfer_range_eq_of_nilpotencyClass_lt) + focal bridge →
  T₁C_Q(P)C_W(P) が N_G(R₁) 内 index p 正規 → (B2) 偽。
  RankOneHypothesis 実例化は StepTwo の rankOneQuotient 構築 (HypothesisA1 経由) と
  同型のパターンだが、A1 でなく直接 RankOneHypothesis を組む必要がある — フィールド
  (basept/doubly_transitive/faithful/H/Q/D/t/...) を 𝒜-作用で埋める設計から。

### (12) 終盤: RankOneHypothesis (N_G(R)/R ↷ 𝒜) の field 別設計 (2026-07-25 具体化)

m = 1 後は |𝒜| = p、R = T×P は rank-2 elementary abelian (|R| = p²)。
carrier: quotient Q̂ := ↥NR ⧸ (R.subgroupOf NR) (R ⊴ NR は normalizer の定義)、
Ω̂ := ↥(orbit) or subtype of 𝒜 (**先に orbit = 𝒜 を Set.eq_of_subset_of_ncard_le で確定**:
subset = monolith 内 hsub を public 化、ncard = index 定理 + ncard_A)。
- basept := ⟨P, ...⟩
- doubly_transitive: 推移性 (orbit=𝒜) + stabilizer 内 C_Q(P) の 𝒜−{P} 正則性
  (mathlib の 2-pretransitive 判定: isMultiplyPretransitive_of_...one-point-stab 推移;
  `MulAction.is_two_pretransitive_iff`-系を要調査)
- faithful: kernel = R — ⊇ は R abelian (conj 自明)、⊆ は「全 P₁ ∈ 𝒜 + T? を固定する
  元は R の全 order-p 部分群 (p+1 本) を正規化」→ R 上の作用が各巡回部分群を保つ →
  scalar-型 → C_G(R) ∩ NR ∩ ... = R·C-系の同定が必要 (要: C_G(R) ⊓ NR の分析;
  Z(R)=R (abelian) なので C_G(R) ⊇ R; C_G(R) ∩ NR / R が全 P₁ 固定と交わる部分)。
  ⚠ ここが (12) 終盤の主要な非自明部分 — 書籍は暗黙 (「Proposition 1 ... can then be
  applied」)。faithful 化は kernel で割る手 (StepTwo と同じ normalCore quotient) が安全:
  Q̂ := NR ⧸ (kernel of NR ↷ 𝒜) とし、kernel = R を別 lemma にする (kernel ⊆ N_G(P₁)∀ →
  kernel ⊆ N_G(P) = C_G(P) → kernel の元は R-decomposition r·w... C_G(P)-元で全 P₁ 固定 →
  freeness から C_Q(P)-成分 = 1 → D̄-成分も W-型 normalization で制約 → ∈ R)。
- t: 位数 2 で P を動かす元の存在 — C_Q(P) ∋ s は P を固定するので不可。書籍の構造
  N_G(R)/R = (R₁/R) ⋊ C_Q(P)C_W(P) の R₁/R 側からではなく、2-推移性から:
  P ↔ P₁ を swap する g の 2-part (odd-order 部分を冪で消す; |swap-元| の 2-part が
  依然 swap する) — `exists_involution_conj_of_odd_orderOf` (Suzuki/Basic:54) 型の補題流用。
- H/Q/D: H = stabilizer(P)-image、Q := C_Q(P)-image、D := H ⊓ H^t (D_def 通り定義)。
  Q_normal/Q_mul_D/Q_even/D_odd/2-rank: C_G(P) = P·(F⋊F*⋊Σ)-構造からの読み出し +
  2-rank-1 は G の (B1) から部分群継承。
- 適用後: model' で N_G(R)/R = F'⋊(F'*⋊Σ') 形 → R₁ := 逆像 (Sylow_p(G)、|R₁| = p³) →
  T₁ := [R₁/T, s]-系 → N_G(R₁) = N_G(R) (11)-型正則性論法の再利用 → T₁C_Q(P)C_W(P)
  index p 正規 → Isaacs Cor 10.2 + focal bridge → (B2) 偽。
- orbit = 𝒜 landing (`6c5201918`/`a3ccd51bd`)。2-推移性の mathlib 入口確定:
  `MulAction.is_two_pretransitive_iff` (pair-moving 判定) — 推移性 (orbit=𝒜) +
  stabilizer(P) 内 C_Q(P) の 𝒜−{P} 正則性から標準組み立て (a≠b, c≠d:
  transitivity で a→c、stabilizer(c)-側の正則性で残り 1 点合わせ)。
  ⟹ (12) 終盤の実装順: (a) faithful kernel = R の同定 (設計書の主要非自明点) →
  (b) Q̂ := NR⧸kernel + Ω̂ = ↥𝒜 の RankOneHypothesis 全 field →
  (c) rankOne_affine_nearField 適用 → (d) R₁/T₁/Cor 10.2 bridge → step_twelve endpoint。
- **(12) 終盤の generic 側完成** (9502 closed): `rankOneHypothesisOfCardEqMulPred`
  (RankOneFromPrimeDegree.lean) が |G|=p(p−1)・degree p・faithful・transitive から
  RankOneHypothesis を全 field 構成。StepTwelve 側の供給物も完備:
  kernel = R iff (`mem_invImageF_iff_forall_conj_smul_eq`)、orbit = 𝒜、
  |D̄|=1 (`sigmaComponent_eq_one_of_card_F_eq_p`)、|Q̄|=|F|−1、
  [NR:R] = p^m·|Q̄|·|D̄| (`index_invImageF_subgroupOf_normalizer`)。
  **残る fc-specific plumbing**: (α) Ω₂ := ↥(orbit NR P) carrier +
  MulAction (↥NR ⧸ R.subgroupOf NR) Ω₂ の構成 (toPermHom → QuotientGroup.lift →
  compHom) + Finite/Faithful/IsPretransitive instance + card Ω₂ = p +
  card 商 = p(p−1) → constructor 適用 → (β) rankOne_affine_nearField 適用
  (hbs = BS Q₈ sorried-cite 経由, 0147 posture) → F₂ near-field |F₂| = p →
  (γ) R₁ = 正規正則部分群の preimage, |R₁| = p³ Sylow → (δ) N_G(R₁) = N_G(R)
  ((11) 型 regularity) → (ε) Isaacs Cor 10.2 transfer → index-p normal →
  ¬(B2) 矛盾 → step_twelve endpoint「(10.2) が成立」。

### (12) tail の PDF 確定読解 (p. 112、2026-07-25 Read で確認)

書籍原文の連鎖 (「As R₁ is non-abelian of order p³...」以降):
1. **R₁ 非可換**: 可換なら R₁ ≤ C_G(R) = R (centralizer_invImageF_eq!) と
   |R₁| = p³ > p² が矛盾 — 無料。class 2 < p (p ≥ 3)。
2. **Hall–Wielandt (class < p 版)**: G/O^p(G) = N_G(R₁)/O^p(N_G(R₁))。
   repo 資産 = transfer_range_eq_of_nilpotencyClass_lt (Isaacs Cor 10.2) を確認。
3. **T ⊴ R₁** (δ1): n ∈ R₁ ≤ N_G(R) の n•T は R 内位数 p、n•T ∈ 𝒜 なら
   orbit 不変性で T ∈ 𝒜 (偽: T ≤ T)、ゆえ ¬(¬ n•T ≤ T) → n•T = T。easy。
4. **R₁/T 可換** (位数 p² — 自明)。**C_{R₁/R}(s) = 1** = [s] が R₁/R を反転
   (δ2): ±1 論法の hinv を public 化 — 任意の対合 u ∈ NR/R は σ を反転
   (k ≡ 1 側は mem_zpowers_of_centralizes → 奇数位数の対合で消滅)。
   [s] は対合 (s ∉ R、s² = 1)。
5. **R₁/T = (R/T) × (T₁/T)**, T₁ = [R₁/T, s] 逆像 (δ3): R/T ≅ P は s 中心化、
   T₁/T は s 反転 — sInvertedT パターンの 1 段上再演。
6. **N_G(R₁) = N_G(R)** (δ4): 𝒜₁ := R₁/T の位数 p 部分群 ∖ {T₁/T}。
   C_Q(P) が 𝒜₁ − {R/T} に正則 ((11) 同様) → N_G(R) ⊊ N_G(R₁) なら
   [N_G(R₁):N_G(R)] = |𝒜₁| = p が (10) に矛盾。
7. **(ε)**: T₁ は C_Q(P)C_W(P) と P に正規化される → T₁C_Q(P)C_W(P) が
   N_G(R₁) 内 index p 正規 → 2 と合わせ G に index p 正規部分群 → (B2) 偽 □
※ (13)–(17) (pp. 113–114 Read 済) は (10.2) 側 endgame (p=3, Z₁=⟨st⟩,
  PSL(2,8), 弱閉 Z₁PΣ の Hall–Wielandt 可換版, R₂⟨s⟩) — (12) とは独立の次章。
  (14) は本 campaign の kernel-同定機構 (N_G(RΣ) ↷ 𝒜₂, kernel = RΣ) を再利用可。
- δ2 (`conj_eq_inv_of_sq_eq_one`, 9f614e728): 対合は正規 ⟨σ⟩ を反転 — public 化済。
  ⚠ **適用には Q̂₂ := NR⧸R' の faithful degree-p 作用 instance が必要** (抽象群だけ
  では偽: C_p × C_{p−1} 反例)。⟹ (α) plumbing を δ2' として 1 定理に集約実装する:
  **`conj_mk_distinguishedInvolution_zpowers_inv`** (次 iteration):
  Ω₂ := ↥{X | 𝒜-predicate}; letI MulAction ↥NR Ω₂ (invariance = orbit_eq);
  φ = toPermHom、hker : R' ≤ φ.ker (kernel iff →)、ψ = QuotientGroup.lift、
  letI = compHom ψ; Faithful (kernel iff ←)・IsPretransitive (orbit=𝒜)・
  card Ω₂ = p (ncard_A m=1)・card Q̂₂ = p(p−1) (済) → conj_eq_inv 適用、
  u := mk ⟨s, s∈NR⟩ (s∈NR: s は T を反転+P 中心化 → R=T·P 正規化;
  u ≠ 1: s∉R は位数 2 vs |R| = p² 奇数)。
  結論 = [s] が Q̂₂ の唯一 Sylow-p 生成元を反転 = C_{R₁/R}(s) = 1 (書籍 p.112)。
  この instance pack は (14) ((10.2) 側 N_G(RΣ) ↷ 𝒜₂) でも再利用できる。
- δ2' 完了 (`3bcf40314`): `quotient_conj_eq_inv_of_sq_eq_one` — N/R ↷ 𝒜 の
  instance pack (subtype MulAction + lift 降下 + Faithful/Pretransitive/card) を
  1 定理に集約し ±1 補題適用。任意の対合が R₁/R を反転。
- **δ3 への key 観察: T = [R₁,R₁]** (T は R₁ の特性的部分群):
  [R₁,R₁] ≤ T は |R₁/T| = p² (可換) から自明; [R₁,R₁] ≠ 1 は R₁ 非可換
  (R₁ 可換 → R₁ ≤ C_G(R) = R が card 矛盾); |T| = p 素数で等号。
  ⟹ N_G(R₁) は T を正規化 (δ1 の NR 版より強く、char で自動) —
  δ4 の「N_G(R₁) が R₁/T の line たちに作用」の基盤。
- 次 iteration: (i) R₁ 非可換 + T = [R₁,R₁] を landing → (ii) δ4 =
  𝒜₁-line 論法 (C_Q(P) が 𝒜₁∖{R/T} に正則、(11) の
  invImageF_mul_comm_of_not_dvd_card_D 系のパターンを R₁/T level で再演) →
  (iii) ε = Cor 10.2 (transfer_range_eq_of_nilpotencyClass_lt、Yoshida.lean) +
  T₁C_Q(P)C_W(P) index-p 正規 → ¬(B2)。

### δ4 (N_G(R₁) = N_G(R)) の完全分解 (2026-07-25 導出済・matrix-free)

書籍の「As in (11)」の行間を埋める再構成。V := R₁/T (位数 p² 可換、
⁅R₁,R₁⁆ = T ゆえ R₁-共役は V に自明作用)。「line」= T を含む R₁ の極大部分群
(= V の位数 p 部分群、全 p+1 本、各 ⊴ R₁)。

- **δ4-i** C_{R₁}(s) = P: C∩R = P (R = T×P、T は s-反転で奇数位数)。
  R₁∖R の固定元 x は [x] ∈ C_{R₁/R}([s]) = 1 (δ2' の反転) → 矛盾。
- **δ4-ii** T₁ := {x ∈ R₁ | sxs⁻¹ = x⁻¹}:
  (a) 部分群: x,y 反転 → ⁅x,y⁆ ∈ T は s-固定 (class-2: ⁅x⁻¹,y⁻¹⁆ = ⁅x,y⁆)
      かつ s-反転 (∈T) → ⁅x,y⁆² = 1 → 奇数位数で = 1 → 可換 → 積も反転。
  (b) |T₁| = p²: ψ(g) := g⁻¹·(sgs⁻¹) の像 ⊆ T₁、fiber = C_{R₁}(s)-coset
      → |image| = p³/p = p²; T₁ ∩ P = 1 で ≤ p²。T ≤ T₁。
  (c) T₁ の元は strongly real: x = s·(sx)、(sx)² = (sxs⁻¹)x = x⁻¹x = 1。
  (d) T₁ は line (image in V = 位数 p、pullback 全体)。
- **δ4-iii** C_{NR}(V) = R₁ かつ C_N(V) = R₁ (N := N_G(R₁)):
  V に自明 → 全 line 固定 → R を正規化 → ∈ NR; [k] が σ̂ と可換 →
  [k] ∈ ⟨σ̂⟩ (**要 public 化: PrimeDegreeTwoTransitive の private
  mem_zpowers_of_centralizes**) → [k] ∈ ⟨σ̂⟩ ∩ (P の stabilizer 像) = 1
  (freeness) → k ∈ R₁。
- **δ4-iv** 「第 3 line を固定する k ∈ NR は R₁」: k は R-line (k∈NR) と
  T₁-line (下記) を常に固定; X ∉ {R-line, T₁-line} も固定なら V 上 3 本の
  固定 line → scalar → R/T 上自明で λ=1 → V に自明 → δ4-iii で k ∈ R₁。
  (2 次元の「3 固定直線 → scalar」を V の部分群計算で: x = a·b 分解
  (a ∈ R/T-方向, b ∈ T₁/T-方向), kxk⁻¹ ∈ xT-line 条件から u = 1。)
  **T₁-line の NR-不変性**: ksk⁻¹ = s·r₁ (r₁ ∈ R₁; NR/R₁ ≅ C_{p−1} の
  唯一対合)、r₁ は V に自明作用 → s と ksk⁻¹ の V-作用同一 → 反転 line 同一
  → k•(T₁-line) = T₁-line。
- **δ4-v** N-orbit(R-line) ∌ T₁-line: n•R = T₁ なら n•P# ⊆ T₁ が
  strongly real (δ4-ii-c) だが P-共役は not strongly real
  (not_isStronglyReal_of_mem_P + 共役不変性) → 矛盾。
- **δ4-vi** 数え上げ: stab_N(R-line) = N ∩ N_G(R) = NR → |orbit| = [N:NR] =: s'。
  p ∤ s' (|N|_p = p³)。s' > 1 なら L ∈ orbit ∖ {R-line} (≠ T₁-line, δ4-v);
  stab_NR(L) = R₁ (δ4-iv) → NR-suborbit サイズ p−1 → s' ≥ p → p∤s' で
  s' = p+1 → orbit = 全 line ∋ T₁-line ✗。ゆえ s' = 1、**N_G(R₁) = N_G(R)** □
- ε 資材: この時点で NR = N(R₁)、R₁ = Sylow_p(G) (p³ = |G|_p)、class 2 < p
  → transfer_range_eq_of_nilpotencyClass_lt (Isaacs Cor 10.2)。index-p 正規:
  M := T₁·(C_G(P)∩NR)-系 = pullback of (T₁-line 方向 ⋊ 全 K̄) — kernel of
  NR → NR/R₁-mod... 実装時は hom NR → C_p を V の R/T-成分で構成
  (K̄ は R/T に自明作用 = C_G(P)、[R₁] → R/T-projection; well-defined-性は
  ⁅NR,R₁⁆-計算) — 詳細は着手時に再設計。
- δ4 進捗 (2026-07-25 続き、全 push 済): δ4-i (`280e3b5e0`) / δ4a (`d97d53e10`) /
  δ4-ii-a (`4e078c8ff`) / δ4-ii-b,c (T₁+card, `80f540c37`, 新 leaf
  **StepTwelveEndgame.lean**) / δ4-ii-d+v (strongly real + g•R ≠ T₁,
  `ebe78e35d`) / δ4-iii core+consumer (`807e41451`, `021d8b171`)。
  generic 側: zpowers_normal_of_orderOf_eq 抽出 + surjective_zpow_smul /
  mem_zpowers_of_centralizes public 化。
  **残り**: δ4-iv (第 3 line 固定 k ∈ NR は R₁ — 座標系は R₁ = R·T₁,
  R ⊓ T₁ = T (card: p²·p²/p = p³); X-line の生成元 x = a·b (a ∈ R, b ∈ T₁)
  分解で k-共役の T-剰余成分比較 → u = 1 → δ4-iii へ) → δ4-vi (assembly:
  stab_N(R-line) = NR、orbit ∌ T₁-line (δ4-v)、非 {R,T₁}-line の NR-orbit
  = p−1 → [N:NR] ∈ {1} → N_G(R₁) = N_G(R)) → ε (Cor 10.2 transfer +
  T₁C_Q(P)C_W(P) index-p 正規 → ¬(B2))。

### δ4-iv/vi の精密化 (2026-07-25 再導出 — cyclicity 不要版)

- **(A) 分解 block**: R ⊓ T₁ = T (x = ty ∈ R∩T₁: s-反転と R-可換性で y² = 1)。
  **NR = R₁·C_G(P)**: R₁ ∩ C_G(P) = R ([x]-order p vs C_G(P)-像の位数 p−1、
  card 計算は mk'∘subtype の quotientKerEquivRange で |像| = |C|/|C∩R'| = p−1)
  → card 積で全体。⟹ 任意の k ∈ NR は k = r₁·c (r₁ ∈ R₁, c ∈ C_G(P))。
- **(B) 全 k ∈ NR は T₁-line を固定**: r₁ は V-自明。c 側: s' := c s c⁻¹ は
  T を elementwise 反転 (T ⊴ NR) かつ s' ∈ C_G(P) (c ∈ C_G(P))。
  **w := s'·s は P と T を両方 centralize → w ∈ C_G(R) = R** (L1 再利用!)
  → s' = w·s、w は V-自明 → s' と s の V-作用一致 → 反転 line 同一
  → c•(T₁-line) = T₁-line。cyclicity/唯一対合論法は不要。
- **(C) δ4-iv 本体**: u₁(k) ≡ 1 ∀ k ∈ NR (r₁ V-自明 + c は R/T ≅ P-classes に
  自明 — c ∈ C_G(P) で T-part しか動かさない)。k が X-line (∉{R,T₁}) も固定
  すると (R/T ⊕ X/T)-座標で diag(1, u₂); T₁-line は第 3 の固定 line で
  mixed → u₂ = 1 → V-自明 → δ4-iii で k ∈ R₁。
- **(D) δ4-vi assembly**: N := N_G(R₁) ⊇ NR (R₁ ⊴ NR)。stab_N(R-line) =
  N ∩ N_G(R) = NR (T = ⁅R₁,R₁⁆ で N は T 固定 → line-pullback = R 正規化)。
  orbit of R-line: ∌ T₁-line (δ4-v)。s' := [N:NR] = |orbit|; s' > 1 なら
  L ∈ orbit∖{R-line}, L ≠ T₁-line → Stab_NR(L) = R₁ ((C)) → NR-suborbit
  サイズ [NR:R₁] = p−1 → s' ≥ p; p ∤ s' (|N|_p = p³) → s' = p+1 → 全 line
  ∋ T₁-line ✗。∴ **N_G(R₁) = N_G(R)** □
- δ4 続き (全 push 済): [NR,NR] ≤ R₁ (`f6e0db94f`, exists_quotient_generator
  private 抽出 + action-free 交換子補題 `b438fcf71`) / R₁ ⊓ C_G(P) = R
  (`078f74aa1`, C/R 商位数 p−1 vs [x]-order p) / **NR = R₁·C_G(P)**
  (`7e0d0f44a`, 埋め込み card 下界 + coe 積分解) / R ⊓ T₁ = T (`68960e933`)。
  **残り 4 部品**: (B-final) conj k • T₁ = T₁ — X₁ := {x ∈ R₁ | sxs⁻¹x ∈ T}
  を S₁-式 inline 部分群化 (mul: ⁅x⁻¹,y⁻¹⁆ ∈ T = δ3 + T 中心 δ4a)、
  X₁ ⊓ R = T (x=ty → y² ∈ T∩P = 1)、X₁ ≠ R₁ → card 挟み撃ちで X₁ = T₁;
  kT₁k⁻¹ ⊆ X₁ は s' = ⁅k,s⁆·s (⁅k,s⁆ ∈ R₁) で mod-T 反転が保たれることから。
  → (C) k が X-line (∉{R,T₁}) 固定 → k = r·c 分解で R/T-方向自明 (c ∈ C_G(P)
  は R/T ≅ P-classes に自明) + T₁-line 固定 → V-自明 → δ4-iii で k ∈ R₁。
  → (D) assembly: stab_N(R-line) = NR、orbit ∌ T₁-line、suborbit p−1 →
  N_G(R₁) = N_G(R)。→ (ε) R₁ Sylow + class 2 < p → Cor 10.2
  (transfer_range_eq_of_nilpotencyClass_lt) + T₁C_Q(P)C_W(P) index-p 正規
  (M := 逆像 of hom NR → R/T-方向) → p ∣ |Ab(G)| → ¬(B2) → step_twelve 完結。
- **δ4 完結** (2026-07-25, `56f588501`): N_G(R₁) = N_G(R) が landed。全 chain =
  C1 (`a2be30c94`) / C2 (`9c5ae1a2c`) / D1+D2 (`75a4dcca2`) / D3 counting
  (`872b33f59`) / D-assembly (`56f588501`)、第 3 leaf StepTwelveConclusion。
  **残るは ε のみ**: (ε1) R₁ は G の Sylow-p (card p³ = p-part hfact +
  Sylow.ofCard); R₁ 非可換 (commutator ≠ ⊥) → class 2 < p →
  transfer_range_eq_of_nilpotencyClass_lt (Isaacs Cor 10.2, Yoshida.lean) で
  G/O^p(G) ≅ N_G(R₁)/O^p(N_G(R₁))-型の結論を取得 (正確な statement 形は
  Yoshida.lean を読んで適合) → (ε2) NR = N_G(R₁) に index-p 正規部分群:
  M := T₁ ⊔ (C-part)… 実装候補: hom NR → ↥R₁⧸(T₁-sub) ≅ C_p を
  [NR,NR] ≤ R₁ + T₁ ⊴ NR + R₁/T₁ ≅ C_p (card p³/p²) で構成 —
  NR/T₁-商で R₁/T₁ が中心的位数 p、NR/(T₁·[C-part])… 具体形:
  NR ⧸ T₁-normal (T₁ ⊴ NR ✓ conj_sInvertedOvergroup_eq!) の中で
  R₁/T₁ (位数 p) と (C_G(P)-像) の積; [NR,NR] ≤ R₁ → NR/R₁ 可換 →
  合成 NR → NR/T₁ → (NR/T₁)/((C-像)·付随) の設計は着手時に確定 →
  (ε3) p ∣ |Ab(G)| → ¬hB2 で False → **step_twelve 主定理**
  (case (10.1) → False) を assemble。
- ε1 完了 (`ff3def388`): [N_G(R), R₁] ≤ T₁。**残る ε2/ε3 (transfer bridge)**:
  資産確認済 — `transfer_range_eq_of_nilpotencyClass_lt` (Yoshida.lean:518,
  v(G).range = w(N).range 形、N = normalizer-of-Sylow)、`focalSubgroupTheorem`
  (Ch05_Transfer/Basic.lean:1158: commutator G ⊓ P = P.focalSubgroup 等 3 conj)。
  実装計画: (ε2) G-focal ≤ T₁: focalSubgroup の生成元 x⁻¹·(gxg⁻¹) (G-共役対
  in R₁) — Cor 10.2 の range-equality から fusion 制御を経由するのが本筋だが、
  直接 route も検討価値: focal = commutator G ⊓ R₁ (focalSubgroupTheorem.1) を
  使い、p³ ∤ |commutator G| を示す方が軽い可能性 — R₁ ≤ commutator G と仮定
  すると focal = R₁ で、Cor 10.2 равен-transfer から N-側 transfer が
  G-transfer と一致 → N-focal ⊇-関係… ここは transferRes/Abelianization の
  API 精読が必要 (TransferIndexPrime.lean Lemma 10.6/10.7/10.9/10.11 一式あり)。
  (ε3) p ∣ |Ab(G)|: p³ ∤ |commutator G| (Sylow-共役で R₁ ≤ commutator を排除)
  → v_p(|Ab G|) = 3 − v_p(|comm|) ≥ 1 → ¬hB2 → **False = step_twelve 完結**。
  R₁ の class < p: R₁ 非可換 p³ → class = 2 (⁅R₁,R₁⁆ = T ≤ Z(R₁) via δ4a)
  < 3 ≤ p (p 奇素数)。nilpotencyClass-API との橋 (Group.nilpotencyClass ↥R₁ = 2)
  は mathlib の nilpotencyClass-le-iff-…-central-series で組む。
- **ε2/ε3 完結 = step (12) 完結** (`cf9996d97`, 2026-07-25): 新 leaf
  **StepTwelveTransfer.lean** — `factorization_ne_three` (case (10.1) の閉鎖):
  hfact (v_p(|G|) = 3) を仮定して False。route は focal 計算を経ず range 消滅で直行:
  (i) `nilpotencyClass_overgroup_le_two` (δ4a の T-中心性 + `⁅R₁,R₁⁆ = T` +
  mathlib `Subgroup.map_subtype_commutator` / `lowerCentralSeries_eq_bot_iff…`);
  (ii) R₁ = `Sylow.ofCard` (hfact で card p³ = full p-part) → **Isaacs Cor 10.2**
  (`transfer_range_eq_of_nilpotencyClass_lt`, class 2 < p) で G/N-transfer range
  一致; (iii) generic `transfer_abelianization_range_eq_bot` (hB2 → G-transfer
  range = ⊥、|range| が |G^ab| と p-冪の公約数); (iv) generic
  `transfer_eq_pow_of_map_conj_eq` (x の全共役 ∈ H + ϕ-値共役不変 →
  transfer = ϕ(x)^index; 正規部分群では既存の transversal-不変版が使えないための
  変種) を ψ = mk'(T̄₁) ∘ transferRes に適用 — ϕ-不変性は **ε1**
  (`commutator_mem_sInvertedOvergroup`: ⁅s⁻¹,x⁻¹⁆ ∈ T₁) から。
  π(of x)^[N:R₁] = π(w x) = 1、p ∤ [N:R₁]
  (`not_p_dvd_index_subgroupOf_normalizer_overgroup`) + 商が p-群 → of x ∈ T̄₁ →
  ker of = commutator → x ∈ T·T₁ = T₁ → R₁ ≤ T₁ → p³ ≤ p² 矛盾 □
  **⟹ (12) は全部品 sorry-free で完結。次 frontier = 文書順で (13)–(17)
  ((10.2) 側 endgame: p = 3, Z₁ = ⟨st⟩, PSL(2,8), Hall–Wielandt 可換版, R₂⟨s⟩;
  pp. 113–114 Read 済、(14) は kernel-同定機構を δ2'/δ4 から再利用)。**

### (13) C_G(Z₁) は 3-群 — 実装計画 (2026-07-25 精読・部品確定済)

原文 p. 113 (PDF page 6 直読済)。Z₁ = ⟨st⟩、orderOf(st) = 3 ((10.2) の
`orderOf_st_eq_char` + char = 3)。証明 = |C_G(Z₁)| = |C∩C_G(s)|·|J| 分解
(J = s-反転元集合) → 両因子が 3-冪。**部品は全て実在確認済**:

- **Odd |C_G(st)|**: `centralizer_natCard_odd_of_stronglyReal` (StronglyReal.lean:469)
  に x := st (st = s·t は def どおり strongly real、(st)² ≠ 1 は位数 3)。
- **§1 Lemma (a)**: `card_eq_card_centralizer_mul_ncard_invertedBy`
  (InvertedProduct.lean:244; X := C_G(st)、t := s、hodd ↑、hnorm = s は st を反転
  → C_G(st) を正規化)。
- **C ⊓ C_G(s) = V = WP**: C_G(st)∩C_G(s) = C_G(s)∩C_G(t) (可換性の同値変形)
  = V (Ch.I の V-特徴付け; 所在は実装時に grep) — |V| = |W|·|P| は 3-冪
  ((10.2): |W| ∈ {3,9}, |P| = 3)。
- **(13a) 新 generic 補題 (唯一の新規 infra)**: 「r prime ∣ |invertedBy X t| →
  ∃ x ∈ invertedBy X t, orderOf x = r」(Cauchy-in-J)。証明 (自己完結 ~100 行,
  重 machinery 不要): X⟨t⟩ 内で R ∈ Syl_r(X) に Frattini → coset X·t 内の
  2-元 trick で対合 u ∈ N(R) ∩ X·t → **既存 `exists_mem_normalizer_conj_of_odd_orderOf`**
  (StronglyReal.lean:40, 対合対の奇積 dihedral 共役が normalizer 保存) で
  u = t^c (c ∈ X) → R^{c⁻¹} は t-不変 Sylow → Lemma (a) を R^{c⁻¹} に適用、
  r-進付値の積乗法性 (|X| = |Y|·|J|) で C_R(t) < R → 非自明 s-反転 r-冪元 →
  冪で位数 r (invertedBy は冪閉)。置き場 = StronglyReal.lean generic 節
  (dihedral 補題と同居) or InvertedProduct.lean (import 向き確認)。
- **r ∈ {3,7}**: x ∈ J 位数 r、strongly real (x = t·(tx)、(tx)² = 1) →
  normal form `exists_isConj_mul_t_of_stronglyReal` (x ~ u·t, u ∈ Q₀#) →
  u·t ∈ ⟨Q₀,K,t⟩ =: L ≅ PSL(2,8) (**Lemma 4** =
  `exists_orderThreeGeneratedSubgroup_mulEquiv_psl2`, hst = orderOf(st) = 3,
  q = |Q₀| = 2³) → r ∣ |PSL(2,F₈)| = 504 = 2³·3²·7、r 奇 (J ⊆ C 奇) → r ∈ {3,7}。
  ⚠ |PSL(2,F₈)| = 504 の card 計算が repo に要るか確認
  (Matrix.ProjectiveSpecialLinearGroup card — mathlib/repo grep)。
- **r = 7 の排除**: 7-Sylow(L) = K-共役 (|K| = 2^p−1 = 7)、x ~ k ∈ K^# →
  C_G(x) ≅ C_G(k)、Ch.I §2 Prop 1(a) (K^# は固定点 2 個) → C_G(k) = C_D(K) = KW。
  st ∈ C_G(x) の像 = KW 内 strongly real 位数 3 元 — KW の位数 3 元は W 側、
  W^# は strongly real でない (Ch.I 系; 所在実装時 grep — FirstCase の
  `not_isStronglyReal_of_mem_P` 同型パターン) → 矛盾。
- **assembly**: |C| = |V|·|J|、|V| = 3-冪、|J| の素因数は 3 のみ → C は 3-群
  (`IsPGroup.of_card`-style: card = 3^k 形へ)。

実装順: (13a) generic → (13) 本体 (新 leaf `FirstCase/StepThirteen.lean`)。

**(13a) 完了 (`8330e0c13`)**: `exists_orderOf_eq_prime_of_dvd_ncard_invertedBy`
(InvertedProduct.lean 末尾、conjInvolution MulAut + Sylow 数奇 + 2-群固定点合同で
t-不変 Sylow → 付値比較)。下流 4556 jobs green。

**(13) 本体の追加 scoping (2026-07-25 実測)**:
- `V := D ⊓ centralizer {t}` (Basic.lean:189)、**Prop 5 =
  `V_eq_centralizer_distinguishedInvolution` : V = D ⊓ centralizer {s}**
  (CentralizerStructure.lean:143)。
- **C_G(t) ⊓ C_G(s) = V の G-level 版は未形式化** — route: 対合の固定点一意性
  (x ∈ C_G(t)∩C_G(s) は s/t 各々の唯一固定点を固定 → 2 点固定 → x ∈ D、
  `exists_fixedPoint_of_involution` + 一意性 lemma を grep)。
  C_G(st)∩C_G(s) = C_G(t)∩C_G(s) は elementary (s と st に可換 ⟺ s と t に可換)。
- **§2 Prop 1(a) は action form** (`ActualKActor.lean:56`)。C_G(k) = KW (k ∈ K^#)
  の subgroup-level 版は組み立てが要る (r = 7 排除 branch の主部品)。
- |PSL(2,F₈)| = 504 / |L| card: repo に orderThreeBruhatSet の card lemma 無し、
  mathlib の PSL card は要調査 (`Matrix.card_special_linear_group...` 系)。
  代替 = Bruhat 分解の直接 counting (|L| = |Q₀K|(1+|Q₀|))。
- ⟹ (13) は複数 iteration 規模。順: (13-i) centralizer 恒等式 2 本 →
  (13-ii) |C| = |V|·|J| 分解 + |V| 3-冪 → (13-iii) r ∈ {3,7} (PSL card) →
  (13-iv) r = 7 排除 (C_G(K) = KW) → assembly。

**(13-i)〜(13-iii-b) 完了 (2026-07-25)**:
- (13-i) `centralizer_mul_t_inf_eq_centralizer_t_inf` /
  `centralizer_t_inf_centralizer_eq_V` / `centralizer_mul_t_inf_centralizer_eq_V`
  (`059f53f03`)。V の G-level 特徴付けは Q の Ω−{basept} 正則性
  (`qRegularEquiv` 単射) で basept 固定を出す route。
- (13-ii) `card_centralizer_mul_t_eq` : |C_G(st)| = |V|·|J| (`bd5484c64`)。
- (13-iii-a) `exists_mem_Q0_orderOf_mul_t_eq_of_dvd_ncard_invertedBy` (`7b71b1839`)。
- **|L| = |Q₀|·|K|·(|Q₀|+1)** = `card_orderThreeGeneratedSubgroup`
  (OrderThreePSLInduction.lean, `d65f71609`)。⚠ **mathlib に PSL の位数は無い**
  (`ProjectiveSpecialLinearGroup.lean` は 39 行の定義のみ; `card_GL_field` から
  |SL₂| を出す route は数百行)。**Lemma 4 の PSL 同型を経由せず、L 自身が満たす
  Hypothesis (Q := Q₀, D := K) に Prop 1(c) の順序公式 `card_G_eq` を適用**して
  |L| を得る — 帰納法仮説も V ≠ ⊥ も不要 (hst のみ)、29 行。
- (13-iii-b) `dvd_card_orderThree_of_dvd_ncard_invertedBy` (`77f4521f7`)。

### (13-iv) r = 7 排除の完全論法 (2026-07-25 導出、部品実在確認済)

書籍の「C_G(K) = C_D(K) = KW ⟹ x は strongly real な位数 3 元を中心化できない」
の行間を埋めた版。**新規 infra 不要 — 全部品が repo に実在**:

1. **x ~ K の生成元**: r = 7 のとき (13-iii-a) の u·t ∈ L は位数 7、
   |L| = 8·7·9 ゆえ ⟨u·t⟩ は L の Sylow-7、K ≤ L も位数 7 = Sylow-7
   ⟹ L 内共役 (`IsPGroup.exists_le_sylow`/`Sylow.conj` 系)。
2. **y := (st) の共役 ∈ C_G(k)**: x ∈ J ⊆ C_G(st) ⟹ st ∈ C_G(x) = C_G(k)^g。
   y は strongly real (st の共役) で位数 3。
3. **y ∈ D**: y は k を中心化 ⟹ Fix(⟨k⟩) を保つ。Prop 1(a)
   (`fixedPoints_zpowers_eq_pair_of_mem_KSet`) で Fix(⟨k⟩) = {basept, t•basept}
   の 2 点。y は奇位数ゆえ 2 点集合上の誘導置換は自明 ⟹ 両点固定 ⟹
   `D_eq_stabilizer_inf` で y ∈ D。
4. **y ∈ V**: **D = K ⋊ V** — `coe_K` (K = KSet = invertedBy D t)、
   `K_normal` ((K.subgroupOf D).Normal, KCyclic.lean:799)、
   |D| = |V|·|KSet.ncard| (§1 Lemma (a); `V_eq_centralizer_distinguishedInvolution`
   の証明中に既出)、K ⊓ V = 1 (t に反転かつ中心化 ⟹ x² = 1 ⟹ D 奇位数で 1)。
   K は巡回 (`K_isCyclic`, KCyclic.lean:813) ゆえ **C_D(k) = K × C_V(k)**
   (v ∈ C_V(k) は K = ⟨k⟩ 全体を中心化するので直積)。y の位数 3 は |K| = 7 と互いに素
   ⟹ K-成分は 1 ⟹ y ∈ C_V(k) ≤ V = C_D(t)。
5. **矛盾**: y ∈ V ⟹ t ∈ C_G(y)、t は対合 ⟹ |C_G(y)| 偶。一方 y は
   strongly real かつ y² ≠ 1 ⟹ |C_G(y)| 奇 (Lemma 3 centralizer clause,
   `centralizer_natCard_odd_of_stronglyReal`)。∴ r ≠ 7 □

⟹ **(13-v) assembly**: (10.2) で |Q₀| = 2^p = 8・|K| = 2^p−1 = 7 を入れると
r ∣ 504 ∧ r 奇 ⟹ r ∈ {3,7}、(13-iv) で 7 を排除 ⟹ |J| は 3-冪。
|V| = |W|·|P| (step (1) の V = W ⋊ P) は (10.2) で 3-冪 ⟹ |C_G(Z₁)| = |V|·|J|
は 3-冪 = **(13) 完了**。C_G(⟨st⟩) = C_G(st) の橋 (zpowers の centralizer) も要。

## 📐 step (14) 進捗と残り (2026-07-25、main session)

新 leaf **`FirstCase/StepFourteen.lean`** (OddOrder.lean 配線済)。

### landed
- **前提「Z₁ ⊂ T」** (書籍 p.113 の括弧書き; 形式化では非自明):
  `AffineNearFieldModel` に **`mul_involutions_mem_range`** を追加 (`174146bb1`)
  — 相異なる 2 対合の積は移動群 `range emb` に入る。この事実は
  `RankOneHypothesis.model_involution_data` の証明内に `huvF : u*v ∈ Fsub` として
  既にあったので、結論を強化して露出させただけ (新規数学なし)。
  → `mk_distinguishedInvolution_mul_t_mem_range_emb` (StepSeven) →
  `distinguishedInvolution_mul_t_mem_invImageF` (StepEleven, st ∈ R) →
  `distinguishedInvolution_mul_t_mem_sInvertedT` /
  `zpowers_..._le_sInvertedT` (StepElevenComplement, Z₁ ≤ T) — `72f802781`。
- **(14)(i) `Z(RΣ) = Z₁P`** = `inf_centralizer_sup_eq_zpowers_sup_P` (`a76bfc612`)。
  中心は G 内で `RΣ ⊓ C_G(RΣ)` と表現 (subtype の center より下流が楽)。
  汎用 3 補題 (`dabd49d97`): `card_sup_eq_mul_of_commute` /
  `center_eq_inf_centralizer_subgroupOf` /
  `inf_centralizer_eq_of_index_sq_of_not_comm`。
- **`⁅RΣ,RΣ⁆ = Z₁`** = `commutator_sup_eq_zpowers` (`4c02c2b96`)。
  ⚠ 書籍の "Since Z₁ = [RΣ,RΣ]" は Σ の T 上の作用 (F₉ の transvection) 解析に
  見えるが、**Z₁P と T がともに指数 p² の正規部分群 ⟹ 交換子群は両方に含まれ、
  Z₁P ⊓ T = Z₁ (Dedekind)** で回避できる。汎用
  `commutator_le_of_card_eq_prime_sq_mul` を追加。
- **N_G(RΣ) は Z₁ / Z₁P を保つ** (`446e42486`)。⚠ `Subgroup.pointwise_smul_def` は
  `MulDistribMulAction.toMonoidEnd` 形で `MulEquiv.toMonoidHom` と噛み合わないので
  共役像の等式は normalizer の elementwise 版から ext で作る。

### 残り (次セッションの実装順)
1. **|𝒜₂| = 3** — generic 部品は **完了** (`b1ebb0711` / `082977ee7` / `aa82a0300`):
   `finset_card_prime_subgroups_le` (≤ p+1) /
   `mem_of_card_eq_of_prime_subgroups` (p+1 個挙げれば完全) /
   **`card_eq_of_forall_zpowers_mem` (= p+1; 生成元の像で Finset を作る版)**。
   残り = FirstCase 側で 𝒮 := `Finset.image (zpowers ·) ((Z₁P : Set G).toFinset \ {1})`
   を `haveI := Fintype.ofFinite G; classical` の下で組み、hmem/hall を与えて
   |𝒮| = 4 → 𝒜₂ := 𝒮.erase Z₁ で card 3。⚠ Z₁P の非単位元が全て位数 3
   (Z₁·P 可換で両者指数 3) を先に出すこと。
   ⚠ `primeLines` を top-level def にすると `Fintype ↑↑E` が立たない
   (Finite → Fintype は proof 内 haveI が要る) ので Finset は呼び出し側で作る。
2. **作用と kernel**: N_G(RΣ) ↷ 𝒜₂ (1 の不変性から)。kernel の元は特に
   P ∈ 𝒜₂ を固定 ⟹ kernel ≤ N_G(P) = R·C_Q(P)·Σ、C_Q(P)^# は 𝒜−{P} に
   自由 ((11) の `invImageF_mul_comm_of_not_dvd_card_D` 系) ⟹ kernel = RΣ。
3. **S₃ の実現**: ⟨s⟩ が 𝒜₂ ∖ {P} (2 元) を交換 ((11) の正則性) + RΣ が
   Sylow-3 でない ((10.2) の |G|_3 = 3^4|W| ≥ 3^5 > 81 = |RΣ|) ゆえ
   N_G(RΣ) ⊄ N_G(P) ⟹ 推移的 ⟹ 全 S₃。
4. **R₁**: S₃ の A₃ の逆像 (|R₁| = 3·81 = 3^5)。以降 (14) の後半
   (|R₂:R₁| ∈ {1,3}, Z(R₁) = Z(R₂) = Z₁, R₂ = C_G(Z₁) — 最後は (13) を使う)。

## ✅ step (14) 完了 (2026-07-25 夜、main session)

`R₂ = C_G(Z₁)` の逆包含 (= (13) 依存) を除き、書籍 (14) の全主張が landed。
新 leaf 2 本 (`OddOrder.lean` 配線済):

**`FirstCase/StepFourteenAction.lean` (812 行)** — `N_G(RΣ)` の `𝒜₂` 上の作用
- generic: `smul_eq_map_conj` / `mem_conj_smul_iff` / `conj_mem_of_conj_smul_eq` /
  `conj_smul_eq_of_forall_comm` / **`commute_of_odd_orderOf_of_conj_mem_zpowers`**
  (位数 3 の部分群を正規化する奇位数元はそれを中心化する)
- `normalizerRSigma` = `N_G(RΣ)`、`lineSetTwoPermHom : N_G(RΣ) →* Sym(𝒜₂)`
  (mathlib の `MulAut G ↷ Subgroup G` pointwise 作用 + `Equiv.Perm.subtypePerm`)
- **`centralizer_P_inf_centralizer_mul_t_eq_sup`** : `C_G(Z₁P) = C_G(P) ⊓ C_G(st) = RΣ`
  — 書籍 (15) が引用する事実。`|C_G(P)| = 3⁴·8` (`card_centralizer_P_eq`) と
  「`st` は strongly real ⟹ `|C_G(st)|` 奇」で、奇約数は `3⁴` を割る
- **`mem_ker_lineSetTwoPermHom_iff`** : kernel = `RΣ`。書籍の
  `N_G(P) = R·C_Q(P)·Σ` 構造分解は使わず、`P ∈ 𝒜₂` 固定 ⟹ `N_G(P) = C_G(P)`、
  `⟨(st)y⟩` も固定 ⟹ `Z₁ × P` 分解の一意性で `k ≡ 1 (mod 3)` ⟹ `st` も中心化
- **`lineSetTwoPermHom_surjective`** : 像 = `Sym(𝒜₂)` 全体。書籍の「⟨s⟩ 正則 +
  推移的」を「像の位数が 2 でも 3 でも割れる ⟹ 6 ∣ |image| ∣ 3! = 6」に整理
  (`s ∈ N_G(RΣ)`、`RΣ` は Sylow-3 でない ⟹ normalizer 増大で 3-元)
- `card_normalizerRSigma` : `|N_G(RΣ)| = 2·3⁵`

**`FirstCase/StepFourteenSylow.lean` (~560 行)** — `R₁` と `R₂`
- **`sylowThreeNormalizerRSigma`** (= `R₁`) : `N_G(RΣ)` の 3-元が生成する部分群
  として **choice-free に定義**。書籍「S₃ の構造から R₁ が存在」は
  「Sylow-3 は指数 2 ⟹ 正規 ⟹ 一意 ⟹ 全 3-元を含む」と読み替え
- `card_sylowThreeNormalizerRSigma` : `|R₁| = 3⁵` / `sup_le_...` : `RΣ ≤ R₁` /
  `conj_mem_...` : `R₁ ⊴ N_G(RΣ)` (3-元集合の共役不変性から直接)
- `sylowThree_sup_zpowers_distinguishedInvolution` : **`N_G(RΣ) = R₁ ⋊ ⟨s⟩`**
- `inf_centralizer_P_eq_of_isPGroup` : `RΣ` を含む任意の 3-部分群 `K` で `C_K(P) = RΣ`
- **`inf_centralizer_sylowThree_eq_zpowers`** : `Z(R₁) = Z₁`
  (推移性の代わりに `C_G(Z₁P) = RΣ` + 位数比較)
- `card_sylow_eq` : `|R₂| ∈ {3⁵, 3⁶}` (= 書籍の `|R₂:R₁| ∈ {1,3}`)
- **`inf_centralizer_sylow_eq_zpowers`** : `Z(R₂) = Z₁`
- `sylow_le_centralizer_zpowers` : `R₂ ≤ C_G(Z₁)`

⟹ **残る (14) の主張は `C_G(Z₁) ≤ R₂` のみ**で、これは (13)
(`C_G(Z₁)` は 3-群) が閉じれば `R₂` が Sylow-3 であることから即従う。

### ⚠ 上記「次の一手 = (13-iv)」は stale だった (2026-07-25 実測で訂正)

**step (13) は既に完結済み** — `54b472b8b` "step (13) 完結 — C_G(Z₁) は 3-群"。
r = 7 排除は `not_card_K_dvd_ncard_invertedBy` (StepThirteen.lean:455) として
landed 済で、最終形は `isPGroup_three_centralizer_Z₁` (同 :752)。
FirstCase 配下に実 sorry は 0 (コメント除去して計測)。

⟹ これを使って **`sylow_eq_centralizer_zpowers` : `R₂ = C_G(Z₁)` を追加**し、
**step (14) は全主張 landed で完了**。

### 次の一手 = step (15)

書籍 p.113-114:
> **(15)** There is a subgroup `L` of `R₁` which is cyclic of order 9, inverted by
> `s`, normalized by `V` and centralized by `W` but not by `P`. It is also the case
> that `|R₂ : LV| = 3`, `Z(LV) = Z₁Σ` and `Ω₁(LV) = Z₁ΣP`.

`L := C_G(st) ⊓ ⟨Q₀,K,t⟩`。書籍は `⟨Q₀,K,t⟩ ≅ PSL(2,8)` から
「`L` は位数 9 の巡回群でその元は `s` に反転される」を読み取る。
repo 側の材料: `card_orderThreeGeneratedSubgroup` (`|⟨Q₀,K,t⟩| = |Q₀|·|K|·(|Q₀|+1)`
= 504、`OrderThreePSLInduction.lean`)。**PSL(2,8) の位数 3 元の中心化群が位数 9 巡回**
に相当する repo 補題の有無を先に実測すること (無ければそこが (15) の主コスト)。
`C_G(Z₁P) = RΣ` は landed 済なので「`L` normalizes `C_G(Z₁P) = RΣ` ⟹ `L ⊂ R₁`」
の行はすぐ使える。

## 📐 step (15) の構造分析 (2026-07-25 実測、main session)

書籍 p.113-114 の (15) 冒頭:
> `L := C_G(st) ⊓ ⟨Q₀,K,t⟩`。`⟨Q₀,K,t⟩ ≅ PSL(2,8)` ゆえ `L` は位数 9 の巡回群で、
> その元は `s` に反転される。

**核心の未形式化部品 = 「PSL(2,q) (q = 2ⁿ) の位数 3 元の中心化群は位数 q+1 の巡回群」**。

### repo 実測 (grep 済、名前まで確認)
- ✅ `natCard_projectiveSpecialLinearGroup_fin_two` : `|PSL(2,F)| = q(q−1)(q+1)`
  (`GroupTheory/SpecificGroups/ProjectiveSpecialLinear/RootGroupSylow.lean`)
  ⚠ 本 issue 上部の「mathlib に PSL の位数は無い」は mathlib についての記述で、
  **repo 側には自前の位数公式がある** (混同注意)
- ✅ `center_specialLinearGroup_fin_two_eq_bot` : char 2 で `Z(SL₂) = 1` (⟹ PSL = SL)
- ✅ `exists_orderThreeGeneratedSubgroup_mulEquiv_psl2` : `⟨Q₀,K,t⟩ ≃* PSL(2,F)`, `|F| = |Q₀|`
- ✅ root group (単数冪部分群) 系の infra 一式 (`RootGroup.lean`)
- ❌ **非分裂トーラス (位数 q+1 の巡回群) は無い**。既存の "torus" 記述は分裂トーラス
  (Borel の対角部分, PSU 側) のみ。⟹ ここが (15) の主コスト

### 実装計画 (generic な新 leaf を上流から積む)
1. **非スカラー 2×2 行列 `M` の `M₂(F)` 内中心化環は `F[M]`** (2 次元可換代数)。
   まず mathlib に既存が無いか確認 (`Matrix` の centralizer 系)。
2. `M ∈ SL₂(F)`、char 2、`M ≠ 1` かつ奇位数 ⟹ 特性多項式 `X² + tr(M)·X + 1` は
   重根なし (重根 ⟺ `tr M = 0` ⟺ `M` は unipotent ⟹ 位数 2 の冪)。
   ⟹ `F[M] ≅ F × F` (分裂) または `F_{q²}` (非分裂)。
3. `C_{SL₂}(M) = {A ∈ F[M] : det A = 1} = ker(代数ノルム)`
   — 分裂なら位数 `q−1` の巡回群、非分裂なら位数 `q+1` の巡回群
   (有限体乗法群の巡回性 + ノルム全射)。
4. char 2 で `PSL = SL` ゆえそのまま移送。
5. `q = 8` に特殊化: 位数 3 の元は `3 ∤ 7 = q−1`, `3 ∣ 9 = q+1` ⟹ 非分裂側
   ⟹ 中心化群は位数 9 の巡回群。`s` による反転は「トーラスを正規化する対合は
   反転する」(Weyl 元の作用) から。

規模: 複数 iteration。1 → 5 の順で積む。(15) の後半
(`|R₂ : LV| = 3`, `Z(LV) = Z₁Σ`, `Ω₁(LV) = Z₁ΣP`) は `L` が取れてからの群論で、
`C_G(Z₁P) = RΣ` (landed) がそのまま使える。

## ✅ step (15) 前半完了 + 非分裂トーラス infra (2026-07-25 深夜、main session)

### landed
**新 leaf `GroupTheory/SpecificGroups/ProjectiveSpecialLinear/NonsplitTorus.lean`**
(5 段計画をそのまま実装、`OddOrder.lean` 配線済):
- `normOneUnits` / `card_normOneUnits` : 二次拡大のノルム 1 単数群は位数 q+1
  (mathlib `FiniteField.unitsMap_norm_surjective`)、`isCyclic_normOneUnits`
- `normOneToSL` / `exists_isCyclic_card_eq_card_add_one` : `E¹ ↪ SL(2,F)`
  (`Algebra.leftMulMatrix`、det = ノルム は `Algebra.norm_eq_matrix_det`)
- `exists_isCyclic_card_specialLinearGroup_eq_card_add_one` : 任意の有限体で成立
  ⚠ **二次拡大の存在は mathlib の `FiniteField.Extension k p n` がそのまま使えた**
  (`finrank_extension`、Field/Finite/Algebra は derive 済) — 自前の ZMod/GaloisField
  plumbing は不要だった
- 位数 504 の群の generic 補題: `card_sylow_three_eq_nine` /
  `card_dvd_nine_of_isPGroup_three` / **`exists_isCyclic_card_nine_mem`** /
  `exists_isCyclic_card_nine_of_mulEquiv`
- `pslMulEquivSL` (char 2 の `Z(SL₂) = ⊥` から) /
  `exists_isCyclic_card_nine_projectiveSpecialLinearGroup`

**新 leaf `FirstCase/StepFifteen.lean`**:
- **`isCyclic_and_card_centralizer_inf_orderThreeGeneratedSubgroup`** :
  `L := C_G(st) ⊓ ⟨Q₀,K,t⟩` は**位数 9 の巡回群** (書籍 (15) 冒頭)。
  `V ≠ ⊥` → Lemma 4 の `exists_orderThreeGeneratedSubgroup_mulEquiv_psl2` →
  `|F'| = |Q₀| = 2^p = 8` → `|⟨Q₀,K,t⟩| = 504` → トーラス転送 → `st` を含む
  Sylow-3 `S` (巡回・位数 9) は可換ゆえ `S ≤ L`、逆に `L` は 3-群 ((13)) で
  `|L| ∣ 9` ⟹ `L = S`

### (15) の残りと必要な部品 (実測メモ)
1. **`Z₁ ≤ L`** : `st ∈ L` かつ `L` 巡回位数 9 ⟹ `Z₁ = ⟨st⟩` は唯一の位数 3 部分群。
2. **`L ⊆ R₁`** : 書籍は「`|LP : Z₁P| = 3` ⟹ `L` は `Z₁P` を正規化 ⟹
   `C_G(Z₁P) = RΣ` を正規化 ⟹ `L ≤ N_G(RΣ)`」。`R₁` は
   **`N_G(RΣ)` の 3-元が生成する部分群**として定義したので、
   **`L ≤ N_G(RΣ)` さえ出れば `L ≤ R₁` は定義から即出る** (L の元は全て 3-元)。
   - そのために要る鍵 = **`P` が `⟨Q₀,K,t⟩` を正規化する**
     (⟹ `P` は `L = C_G(st) ⊓ ⟨Q₀,K,t⟩` を正規化。`P` が `st` を中心化するのは
     `R` 可換から既出)。⚠ **repo に該当補題は grep で見つからない** ⟹ ここが次の主コスト。
     出れば `LP` は位数 27 の群で `Z₁P` は指数 3 ⟹ 正規 ⟹ `L` が `Z₁P` を正規化。
   - `C_G(Z₁P) = RΣ` は `centralizer_P_inf_centralizer_mul_t_eq_sup` として landed 済。
3. `s` が `L` を反転 / `V` が `L` を正規化 / `W` が `L` を中心化・`P` は非中心化。
4. 後半 (`|R₂ : LV| = 3`, `Z(LV) = Z₁Σ`, `Ω₁(LV) = Z₁ΣP`)。

### (15) `L ⊆ R₁` の完全論法 (2026-07-25 導出、部品実在確認済)

`P_le_normalizer_orderThreeGeneratedSubgroup` が landed したので、残りは次の連鎖:

1. **`P` は `L` を正規化**: `P` は `⟨Q₀,K,t⟩` を正規化 (landed) かつ `st` を中心化
   (`P ≤ R` 可換、`invImageF_mul_comm`) ⟹ `C_G(st)` を正規化 ⟹ 交わりを正規化。
2. **`Z₁ ≤ L`**: `st ∈ L` から `zpowers_le`。
3. **`L ⊓ P = ⊥`** — ここが唯一の非自明点。背理法: `L ⊓ P ≠ 1` なら `|P| = 3` 素より
   `P ≤ L`。`Z₁ ≤ L` も位数 3 で `Z₁ ⊓ P = ⊥` (`zpowers_inf_P_eq_bot`, landed)。
   ⟹ `Z₁ ⊔ P ≤ L` は位数 9 (`card_sup_eq_mul_of_commute`, StepFourteen) = `|L|`
   ⟹ `L = Z₁ ⊔ P` ⟹ `L` の全元は 3 乗が 1 (`pow_eq_one_of_mem_sup_of_commute`,
   StepFourteen)。しかし `L` は位数 9 の**巡回**群ゆえ位数 9 の元を持つ (矛盾)。
   ⟹ **既存の generic 補題 2 本だけで閉じる (新規 infra 不要)**。
4. **`LP` は位数 27、`Z₁P` は指数 3 ⟹ 正規** ⟹ `L` は `Z₁P` を正規化。
   (`card_sup_eq_mul_of_commute` は可換性を要求するので、ここは
   `Subgroup.card_mul_index` / `Subgroup.normal_of_index_eq_prime` 系を使う;
   `P` が `L` を正規化するので `L ⊔ P` の位数は `|L|·|P|/|L ⊓ P|`。)
5. `L` は `C_G(Z₁P) = RΣ` (`centralizer_P_inf_centralizer_mul_t_eq_sup`, landed) を
   正規化 ⟹ `L ≤ N_G(RΣ)`。
6. `L` の元は全て 3-元 (位数 9 の群) ⟹ **`R₁` の定義 (`N_G(RΣ)` の 3-元が生成) から
   `L ≤ R₁` が即出る** (`sylowThreeNormalizerRSigma_def` + `Subgroup.subset_closure`)。

## ✅ step (15) 完結 (2026-07-26、main session)

書籍 (15) の**全主張**が landed。フルビルド green (4755 jobs)、AxiomsCheck OK、
実 sorry は 9318 (model) 由来の 1 件のみ、非 sorry 警告 0。

### `StepFifteen.lean` (前半: `L` そのもの)
`L := C_G(st) ⊓ ⟨Q₀,K,t⟩` を **`nonsplitTorus`** と命名 (PSL(2,8) の非分裂極大トーラス)。

| 主張 | 宣言名 |
|---|---|
| `L` は位数 9 の巡回群 | `isCyclic_and_card_nonsplitTorus` |
| `Z₁ ≤ L` | `zpowers_le_nonsplitTorus` |
| `L ⊓ P = 1` | `nonsplitTorus_inf_P_eq_bot` |
| `P` が `⟨Q₀,K,t⟩` / `L` を正規化 | `P_le_normalizer_orderThreeGeneratedSubgroup` / `P_le_normalizer_nonsplitTorus` |
| `\|LP\| = 27`、`L` が `Z₁P` を正規化 | `card_nonsplitTorus_sup_P` / `nonsplitTorus_le_normalizer_zpowers_sup_P` |
| `L ≤ N_G(RΣ)`、**`L ⊆ R₁`** | `nonsplitTorus_le_normalizerRSigma` / `nonsplitTorus_le_sylowThreeNormalizerRSigma` |
| `⟨Q₀,K,t⟩ ≤ C_G(W)`、`L ≤ C_G(W)` | `Hypothesis.orderThreeGeneratedSubgroup_le_centralizer_W` / `nonsplitTorus_le_centralizer_W` |
| `L` の 3-torsion = `Z₁` | `mem_zpowers_st_of_mem_nonsplitTorus_of_pow_three` |
| `L ⊓ V = 1` (∵ `t ∉ H` ⟹ `st ∉ V`) | `nonsplitTorus_inf_V_eq_bot` |
| `V` が `L` を正規化 | `V_le_normalizer_nonsplitTorus` |
| **`s` が `L` を反転** | `conj_distinguishedInvolution_eq_inv_of_mem_nonsplitTorus` |
| **`RΣ` は指数 3** (書籍の「`TΣ` has exponent 3」) | `pow_three_eq_one_of_mem_sup_invImageF_centralizer_W` |
| **`L ⊄ RΣ`** ((17) でも使用)、**`P` は `L` を非中心化** | `not_nonsplitTorus_le_sup_invImageF_centralizer_W` / `not_nonsplitTorus_le_centralizer_P` |

- `s` 反転の機構: `x·x^s` は `s`-固定な `L` の元 ⟹ `L ⊓ C_G(s) ≤ L ⊓ V = 1`
  ⟹ `x^s = x⁻¹` (巡回群の Aut 計算を回避)。
- `RΣ` 指数 3 の機構: `x = rσ` (R·Σ 分解) で `c = ⁅σ,r⁆ ∈ ⁅RΣ,RΣ⁆ = Z₁ ≤ Z(RΣ) ⊓ R`
  ⟹ `σ` 共役が `r ↦ cr`, `cr ↦ c²r` ⟹ `(rσ)³ = r³c³ = 1`
  (class-2 cube 公式の具体化。subtype の `lowerCentralSeries` 配管は不要だった)。

### `StepFifteenLV.lean` (新 leaf、後半: `LV`)

| 主張 | 宣言名 |
|---|---|
| `\|LV\| = 27\|W\|`、`LV ≤ R₂` | `card_sup_nonsplitTorus_V` / `sup_nonsplitTorus_V_le_sylow` |
| **`\|R₂ : LV\| = 3`** | `index_subgroupOf_sup_nonsplitTorus_V_eq_three` |
| `LW` は可換、`\|LW\| = 9\|W\|`、`LV = (LW)P` | `mul_comm_of_mem_sup_nonsplitTorus_W` / `card_sup_nonsplitTorus_W` / `sup_nonsplitTorus_V_eq` |
| `C_L(P) = Z₁`、`C_{LW}(P) = Z₁Σ`、`C_{LV}(L) = LW` | `nonsplitTorus_inf_centralizer_P_eq_zpowers` / `sup_nonsplitTorus_W_inf_centralizer_P_eq` / `sup_nonsplitTorus_V_inf_centralizer_nonsplitTorus_eq` |
| **`Z(LV) = Z₁Σ`** | `inf_centralizer_sup_nonsplitTorus_V_eq` |
| `W` の 3-torsion = `Σ`、`Ω₁(LW) = Z₁Σ` | `mem_sigma_of_mem_W_of_pow_three` / `pow_three_eq_one_iff_mem_zpowers_sup_sigma` |
| **`Ω₁(LV) = Z₁ΣP`** | `pow_three_eq_one_iff_mem_zpowers_sup_sigma_sup_P` |

- `Ω₁(LV)` は **regular p-group 理論 ([H] III 1.3(b)) を使わずに閉じた**:
  `x = aq` (`a ∈ LW`, `q ∈ P`) で `d = a⁻¹a^q ∈ LW` は `d³ = a⁻³(a³)^q = 1`
  (∵ `a³ ∈ C_{LW}(P) = Z₁Σ`) ⟹ `d ∈ Z₁Σ ≤ C_G(P)` ⟹ `a^q = ad`, `(ad)^q = ad²`
  ⟹ `x³ = a³d³ = a³`。⟹ `x³ = 1 ⟺ a ∈ Ω₁(LW) = Z₁Σ ⟺ x ∈ Z₁ΣP`。
  (repo には `GroupTheory/RegularPGroup.lean` の BG E.2(a) engine もあるが、
  subtype の `lowerCentralSeries` 配管より直接計算が安上がりだった。)
- generic 追加: `card_sup_eq_mul_of_le_normalizer` / `mem_centralizer_singleton_conj_iff` /
  `centralizer_union` / `centralizer_sup` / `mem_zpowers_pow_of_pow_eq_one` /
  `mem_of_pow_eq_one_of_isCyclic_card_sq` / `mul_comm_of_mem_sup_of_commute` /
  `mul_comm_of_mem_of_isCyclic`。

### 次の一手 = step (16) (p. 114)

> **(16)** `Z₁PΣ ⊆ Z₂(R₁)`、`Z₁` は `Z₁PΣ` の中で強実元だけからなる唯一の位数 3
> 部分群、`N_G(Z₁PΣ) = N_G(Z₁) = R₂⟨s⟩`。

書籍の証明構造:
1. `Z(R₁) = Z₁ ⊆ Z₁P = Z(RΣ) ⊴ R₁` ((14)) ⟹ `Z₁P ⊆ Z₂(R₁)`;
   `Z₁Σ = Z(LV) ⊴ R₁` ((15)) ⟹ `Z₁Σ ⊆ Z₂(R₁)`。⟹ `Z₁PΣ ⊆ Z₂(R₁)`。
   - 要部品: `Z₁P ⊴ R₁` は landed (`N_G(RΣ)` が `Z₁P` を正規化 = StepFourteen)、
     **`Z₁Σ ⊴ R₁` は新規** (`Z(LV)` が `R₁` で正規 — `LV ⊴ R₁`? を要確認)。
     `Z₂` の定義/API (`upperCentralSeries` 2 段目) の repo/mathlib 側の形も要実測。
2. 強実元の一意性: `X ≤ Z₁PΣ` 位数 3・強実・`X ⊓ Z₁ = 1` を仮定 →
   `Z₁ = Z(R₁) ⊆ Z₁X ⊆ Z₂(R₁)` ⟹ `R₁` が `Z₁X` 内の `Z₁` 以外の位数 3 部分群を
   推移的に置換 ⟹ `Z₁X` の元が全部強実 ⟹ `(Z₁X) ⊓ (PΣ) ≠ 1` と矛盾
   (`P` の非自明元は強実でない = `not_isStronglyReal_of_mem_P`, landed)。
3. `N_G(Z₁PΣ) ⊆ N_G(Z₁) = C_G(Z₁)⟨s⟩ = R₂⟨s⟩` と `Z₁PΣ = Ω₁(LV) ⊴ R₂⟨s⟩`。

## 🚧 step (16) 進捗 (2026-07-26、main session、`FirstCase/StepSixteen.lean` 新 leaf)

### landed
- **`sup_invImageF_centralizer_W_sup_nonsplitTorus_eq` : `R₁ = RΣL`**
  (|RΣ| = 3⁴ / |R₁| = 3⁵ で RΣ 極大、`L ⊄ RΣ` (15))。(17) の「R̄₁ は R̄Σ と
  L̄ΣP で生成」の土台。
- **`commutator_zpowers_sup_sigma_sup_P_sylowThree_le` : `⁅Z₁ΣP, R₁⁆ ≤ Z₁`**
  = 書籍の `Z₁PΣ ⊆ Z₂(R₁)`。⚠ **Z₂ を対象として定義せず具体形で述べた** —
  下流が要るのはこの形 (`Z₁X ⊴ R₁` と `R̄₁` の class ≤ 2 が直に出る)。
  分解 = `R₁ = RΣL`、RΣ 側は `Z₁ΣP ≤ RΣ` + `⁅RΣ,RΣ⁆ = Z₁` (14)、L 側は
  `Z₁Σ` が `L` を中心化 + **`⁅P,L⁆ ≤ Z₁`**。
  - 部品: `inv_mul_conj_mem_zpowers_sup_sigma` (StepFifteenLV から抽出:
    `a ∈ LW, q ∈ P ⟹ a⁻¹a^q ∈ Z₁Σ`)、`nonsplitTorus_inf_zpowers_sup_sigma_eq`
    (`L ⊓ Z₁Σ = Z₁`)、`commutatorElement_mem_zpowers_of_mem_P_of_mem_nonsplitTorus`。
- **`not_isStronglyReal_of_mem_V`** (landed の `not_isStronglyReal_of_mem_P` を
  `V ⊇ PΣ` に一般化) と **`not_isStronglyReal_of_mem_P_sup_sigma`**
  (ΣP の非自明元は強実でない) — (16) 第二主張の矛盾側。

### 追加 landed (2026-07-26 続き)
- **`eq_zpowers_of_card_three_of_forall_isStronglyReal` : (16) 第二主張**
  (`X ≤ Z₁ΣP` 位数 3 で全元強実 ⟹ `X = Z₁`)。
  ⚠ 書籍の「`R₁` が `Z₁X` の線を推移的に置換」を**部分群の軌道でなく元の共役**で
  実装 — 軌道-固定点機構が不要になった: `X ≠ Z₁` なら `Z(R₁) = Z₁` より `X` を
  中心化しない `g ∈ R₁` があり、`w ∈ X#` に対し `d = w⁻¹w^g ∈ Z₁` が非自明 ⟹
  `⟨d⟩ = Z₁`、`conj_pow_eq_mul_pow` で `w^{g^m} = w·d^m` ⟹ 剰余類 `wZ₁` が
  丸ごと `w` の共役。`Z₁X ⊓ ΣP ≠ 1` (位数 27 の初等可換内の位数 9 二つ) の元が
  強実になり `not_isStronglyReal_of_mem_P_sup_sigma` と矛盾。
- 部品: `conj_pow_eq_mul_pow` / `isStronglyReal_conj` /
  `isStronglyReal_of_conj_eq_inv` (対合に反転される元は強実) /
  `zpowers_sup_sigma_inf_P_eq_bot` / `mul_comm_of_mem_zpowers_sup_sigma{,_sup_P}` /
  `card_zpowers_sup_sigma{,_sup_P}` (= 9, 27) /
  **`forall_isStronglyReal_mem_zpowers_st`** (Z₁ の全元が強実)。
- **`normalizer_zpowers_sup_sigma_sup_P_le_normalizer_zpowers` : `N_G(Z₁PΣ) ≤ N_G(Z₁)`**
  (第三主張の前半)。

## ✅ step (16) 完結 (2026-07-26、main session、`FirstCase/StepSixteen.lean` 1249 行)

書籍 (16) の**全 3 主張**が landed。フルビルド green (4756 jobs)、警告 0、
実 sorry は 9318 (model) 由来の 1 件のみ。

| 主張 | 宣言名 |
|---|---|
| `R₁ = RΣL` (構造前提) | `sup_invImageF_centralizer_W_sup_nonsplitTorus_eq` |
| **`Z₁PΣ ⊆ Z₂(R₁)`** (= `⁅Z₁ΣP, R₁⁆ ≤ Z₁`) | `commutator_zpowers_sup_sigma_sup_P_sylowThree_le` |
| **強実線の一意性** | `eq_zpowers_of_card_three_of_forall_isStronglyReal` |
| **`N_G(Z₁PΣ) = N_G(Z₁)`** | `normalizer_zpowers_eq_normalizer_zpowers_sup_sigma_sup_P` |
| **`N_G(Z₁) = R₂ ⊔ ⟨s⟩`** | `normalizer_zpowers_eq_sylow_sup_zpowers` |
| 部品: `⁅P,L⁆ ≤ Z₁` / `L ⊓ Z₁Σ = Z₁` | `commutatorElement_mem_zpowers_of_mem_P_of_mem_nonsplitTorus` / `nonsplitTorus_inf_zpowers_sup_sigma_eq` |
| 部品: `Z₁ΣP` は位数 27 初等可換 | `card_zpowers_sup_sigma{,_sup_P}` / `mul_comm_of_mem_zpowers_sup_sigma{,_sup_P}` / `zpowers_sup_sigma_inf_P_eq_bot` |
| 部品: 強実 | `not_isStronglyReal_of_mem_V` / `not_isStronglyReal_of_mem_P_sup_sigma` / `forall_isStronglyReal_mem_zpowers_st` / `isStronglyReal_conj` / `isStronglyReal_of_conj_eq_inv` |
| 部品: LV の正規化 | `distinguishedInvolution_mem_normalizer_sup_nonsplitTorus_V` / `sylow_le_normalizer_sup_nonsplitTorus_V` / `normalizer_sup_nonsplitTorus_V_le` |
| generic | `conj_pow_eq_mul_pow` / `eq_one_or_eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three` |

**設計上の要点 2 つ**:
- `Z₂(R₁)` を対象として定義せず **`⁅Z₁ΣP, R₁⁆ ≤ Z₁`** の具体形にした。
  下流が要るのはこの形 (`Z₁X ⊴ R₁`、`R̄₁` の class ≤ 2 が直に出る)。
- 書籍の「`R₁` が `Z₁X` の線を推移的に置換」は**部分群の軌道でなく元の共役**で実装。
  `w^{g^m} = w·d^m` (`conj_pow_eq_mul_pow`) で剰余類 `wZ₁` が丸ごと `w` の共役に
  なるため、軌道–固定点機構が不要になった。

### 次 = step (17) 結論 (p. 114)

書籍の流れ:
1. `x ∈ G` で `(Z₁PΣ)^x ⊆ R₂` を取る。`Z₁^x ⊄ LV` なら `R₂ = LV ⋊ Z₁^x` かつ
   `(Z₁PΣ)^x = A × Z₁^x` (A は `LV` の (3,3) 型部分群) → `A ⊆ Ω₁(LV) = Z₁PΣ` で
   (16) より `A^# は強実でない` ⟹ `A ⊓ Z₁ = 1`, `Z₁ΣP = Z₁A` ⟹ `Z₁^x` が `Z₁ΣP` を
   中心化 ⟹ `Z₁Σ ⊆ Z(R₂)` で (14) と矛盾。
2. よって `Z₁^x ⊆ Ω₁(LV) = Z₁ΣP` ⟹ (16) の一意性で `Z₁^x = Z₁` ⟹
   `x ∈ N_G(Z₁) = R₂⟨s⟩` ⟹ `x` は `Z₁PΣ` を正規化。
   ⟹ **`Z₁PΣ` は `R₂` 内で weakly closed**、しかも可換。
3. **Hall–Wielandt (p > 2, A abelian 版)** で `G/O³(G) ≅ R₂⟨s⟩/O³(R₂⟨s⟩)`。
4. `R̄₁ = R₁/Z₁` の構造 (`R̄Σ = T̄ × P̄ × Σ̄`, `L̄ΣP = L̄ × Σ̄ × P̄`, `L ⊄ RΣ` は landed)
   と class ≤ 2 (= (16) 第一主張) から `⁅R̄₁,R̄₁⁆` は位数 1 or 3 ⟹
   `R̄₁/⁅R̄₁,R̄₁⁆` に `s` 中心化の位数 3 商 ⟹ `|W| = 3` なら `R₂ = R₁` で (B2) と矛盾。
5. `|W| = 9` 側: `C_{R₁}(s) = PΣ`, `W ⊄ R₁`, `R₂ = R₁W`, `R₁⟨s⟩ ⊴ R₂⟨s⟩` ⟹
   再び (B2) と矛盾。

## 🚧 step (17) 進捗 (2026-07-26、`FirstCase/StepSeventeen.lean` 新 leaf)

### landed — **書籍 (17) の弱閉性パート (段 1–2) が完了**
- `isStronglyReal_inv` (generic) : 強実元の逆元は強実
- `mem_zpowers_of_isStronglyReal_of_mem` : **Z₁PΣ の強実元 = Z₁ の元**
  (強実 y ∉ Z₁ があれば ⟨y⟩ = {1,y,y⁻¹} が全元強実な位数 3 部分群 ⟹ (16) に反する)
- `map_conj_zpowers_le_sup_nonsplitTorus_V` : **`Z₁^x ⊄ LV` の排除** (書籍 (17) 段 1)
  A = (Z₁PΣ)^x ⊓ LV の位数 9 は `relIndex_dvd_index_of_normal` を ↥R₂ 内で使って
  (`relIndex_subgroupOf` で持ち上げ) 導く。A ⊓ Z₁ = 1 は「(Z₁PΣ)^x の強実元は
  Z₁^x のもの」から。⟹ Z₁A = Z₁PΣ を Z₁^x が中心化 ⟹ Z₁Σ = Z(LV) ⊆ Z(R₂) = Z₁ で
  |Z₁Σ| = 9 と矛盾。
- `map_conj_eq_of_map_conj_zpowers_le` / **`map_conj_eq_of_le_sylow`** :
  **`(Z₁PΣ)^x ≤ R₂ ⟹ (Z₁PΣ)^x = Z₁PΣ`** = Hall–Wielandt の仮説
  「A は R₂ 内で weakly closed」。

### 残り
1. **Hall–Wielandt (abelian 版)** = [issue 9503](9503-hall-wielandt-abelian-weakly-closed.md)
   (claim 済、hub band)。これが入れば `G/O³(G) ≅ R₂⟨s⟩/O³(R₂⟨s⟩)`。
2. 書籍 (17) 段 4–5 の最終矛盾 2 本 (`|W| = 3` 側と `|W| = 9` 側)。材料:
   `R₁ = RΣL` (landed)、class ≤ 2 (= (16) 第一主張、landed)、
   `N_G(Z₁) = R₂⟨s⟩` (landed)、(14) の「s は R₁/RΣ を反転」。

⚠ **唯一の新規 shared infra = Hall–Wielandt の abelian 版**
(`A ≤ Z(P)` でなく `p > 2 ∧ A abelian` 版; 本 issue 冒頭「Hall-Wielandt の所在」参照)。
着手時は **9500 番台で claim** してから (hub バンド)。それ以外の (17) の材料は
(14)(15)(16) で出揃っている。

### 旧メモ (消化済み)
0. ~~(16) 第三主張の残り~~ **完了**: (i) `N_G(Z₁) = C_G(Z₁)⟨s⟩`
   (`N/C ↪ Aut(Z₁) ≅ C₂`、`s` は `Z₁` を反転するので指数 2)、
   (ii) `C_G(Z₁) = R₂` (landed `sylow_eq_centralizer_zpowers`)、
   (iii) 逆包含 `R₂⟨s⟩ ≤ N_G(Z₁PΣ)`: `LV ⊴ R₂⟨s⟩` (`|R₂ : LV| = 3` で `R₂` 側は
   minFac 正規、`s` は `L` を反転し `V` を中心化) + `Z₁PΣ = Ω₁(LV)` (15) が
   自己同型不変 (元の 3 乗条件) ⟹ 正規。
1. ~~第二主張~~ **完了** (上記)。旧メモ: `X ≤ Z₁ΣP` 位数 3・全元強実・`X ⊓ Z₁ = 1` を仮定 →
   (a) `Z₁X ⊴ R₁` (`⁅Z₁ΣP,R₁⁆ ≤ Z₁ ≤ Z₁X` から即)、
   (b) `R₁` は `Z₁X` 内の `Z₁` 以外の位数 3 部分群 3 個に作用し**固定点なし**
   (固定線は `R₁` 正規の位数 3 ⟹ `Z(R₁) = Z₁` と交わる ⟹ `= Z₁` で矛盾) ⟹
   3-群が 3 元集合に固定点なしで作用 ⟹ 推移的、
   (c) ⟹ `Z₁X` の全元が強実 (Z₁ 側は `isStronglyReal_distinguishedInvolution_mul_t`)、
   (d) `(Z₁X) ⊓ (ΣP) ≠ 1` (位数 27 の初等可換 `Z₁ΣP` 内の位数 9 二つ) ⟹
   `not_isStronglyReal_of_mem_P_sup_sigma` と矛盾。
   - 要部品: `|Z₁ΣP| = 27` と初等可換性 (指数 3 は
     `pow_three_eq_one_iff_mem_zpowers_sup_sigma_sup_P` の ⟸ で既済)、
     位数 p² 群の「位数 p 部分群はちょうど p+1 個」系 (StepFourteen の
     `card_lineSet_eq` / `lineSetTwo` 周りの **generic 補題が再利用できるか要実測**)。
2. **第三主張**: `N_G(Z₁PΣ) ⊆ N_G(Z₁)` (共役は強実線を強実線に送る ⟹ 一意性で
   `Z₁` 固定)、`N_G(Z₁) = C_G(Z₁)⟨s⟩ = R₂⟨s⟩` ((13)(14) 由来)、
   逆向きは `Z₁PΣ = Ω₁(LV)` (15) が `R₂⟨s⟩` で正規。

