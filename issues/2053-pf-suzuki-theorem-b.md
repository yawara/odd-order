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

- [ ] Ch.II hypothesis carrier ((B1)+(B2)) と leaf 構成の設計
      (`OddOrder/Peterfalvi/Appendices/Suzuki/FirstCase/` dir 化)
- [ ] (1) V = W ⋊ P ほか
- [ ] (2) C_G(P) の near-field 構造 (Appendix II 接続)
- [ ] (3) 素因数の合同条件
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
