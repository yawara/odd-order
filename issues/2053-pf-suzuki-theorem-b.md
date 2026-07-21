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
    **残 = Half B のみ** (M 側で hB = `∃ a∈P, a≠1 ∧ ∀k∈K a·k·a⁻¹=k^r` を供給)。
    Half B 精緻化: M K-既約 → `exists_field_semilinear` (E:=M, T:=K, ψ:=K の
    M 上共役作用, hirr:=既約) で F'=𝔽_{r^p}, M 1-dim/F', 各 g=conj-by-a に σ_a:
    F'≃+*F' (semilinear law)。要点: (1) K↪F'ˣ (M≅F' 上 K が mult by unit),
    (2) K on M faithful (fpf `conjQByK_fixed_eq_one` ⟹ faithful), (3) σ: P→RingAut F'
    injective + |P|=p=|Gal(F'/𝔽_r)| ⟹ P≅Gal, (4) Frobenius x↦x^r ∈ Gal ゆえ
    ∃a∈P σ_a=Frobenius (A1 の r 版: RingAut 𝔽_{r^p}=x↦x^{r^j}), その a で
    a·k·a⁻¹=σ_a(k)=k^r。⚠ 全体は dichotomy 経由で 9318 継承 (AxiomsCheck 非登録)。
- [ ] (4) Wielandt fixed point (被覆調査 → 不足なら port)
- [ ] (5)–(9)
- [ ] (10) Lemma 5 消費の二分岐
- [ ] (11)–(12) (Cor 10.2 bridge: transfer range → G/O^p 同型)
- [ ] (13)–(16)
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
