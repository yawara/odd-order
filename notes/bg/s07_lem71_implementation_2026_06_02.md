# BG §7 proof 充填 — Lem 7.1 中心の実装計画 (2026-06-02)

> **scope**: S07_Transitivity の 6 sorry の充填計画。本セッション目標 = Lemma 7.1
> (Inductive Lemma, 全結果の核) + そのための API 層。出典 mmd L2131-2314。
> §5 完結 (Thm 5.5/5.6/5.7) 済が前提。survey は `s07_transitivity.md`。

## 依存グラフ (§7 内)

```
API 層 (AInvariantPiSubgroups + S07 helpers)
  → Note 補題 (π'-元 of C_G(A) ∈ K)     [Hyp 7.1 + simplicity]
  → 共通構成 (Prop 1.5(b)(c) 適用)       [§1B ✅]
  → Lem 7.1 (強帰納法)
       → Thm 7.2  [+ Prop 1.16 ← 未形式化 (G Thm 6.2.4)]
       → Thm 7.3  [+ Prop 1.16]
       → Thm 7.4 (propagation; Lem 1.14 ✅ + 7.3)
Prop 7.5 [§6 ✅ + p-stability]
  → Thm 7.6 = Prop 7.5(2) + Thm 7.2 (短)
```

**ゲート状況**: Prop 1.5(a)(b)(c) ✅ (S01 §1B, φ : A →* MulAut G 型レベル);
Lem 1.14 ✅; §6 sorry-free ✅; **Prop 1.16 のみ未形式化** (= **G** Thm 6.2.4 +
帰納; Isaacs に対応定理なし → Gorenstein 参照例外)。

## Phase A: API 層 (`AInvariantPiSubgroups.lean` 追記)

1. `smul_mem_hInvariant_top` / `smul_mem_hInvariantStar_top`:
   `k ∈ centralizer A` → `Q ∈ ℋ_⊤(A;π)` → `MulAut.conj k • Q ∈ ℋ_⊤(A;π)` (★版も)。
   - normalizer: `a (kQk⁻¹) a⁻¹ = k(aQa⁻¹)k⁻¹` (k⁻¹ak = a)。
   - π: card 不変 (`Subgroup.pointwise_smul_def` + equivMapOfInjective)。
   - ★: 逆向き `conj k⁻¹` で order-iso → maximality 移送。
2. `exists_le_hInvariantStar` [Finite G]: `Q ∈ ℋ_H(A;π)` → `∃ Q* ∈ ℋ*_H(A;π), Q ≤ Q*`。
   `Set.Finite.exists_maximal_wrt (f := Nat.card)` を s := {Q' ∈ ℋ | Q ≤ Q'} に適用
   + `Subgroup.eq_of_le_of_card_ge`。

## Phase B: S07 helper 層

1. **conj-action 橋**: `φA := MulAut.conj.comp A.subtype : ↥A →* MulAut G`。
   `IsAInvariant φA Q ↔ A ≤ normalizer Q` (両向き ~10行)。
   N ≤ G A-不変なら `restrictAction`/`IsAInvariant.restrict` で `↥A →* MulAut ↥N`;
   `X ≤ N` に対し `IsAInvariant (restrict) (X.subgroupOf N) ↔ A ≤ normalizer X`。
2. **`kSubgroup` API**: `kSubgroup_le_centralizer`, π'-群性, 「C_G(A) 内 normal」。
3. **Note 補題** `mem_kSubgroup_of_piPrime_mem_centralizer` (BG L2145 直後の Note):
   Hyp71 + hG → c ∈ C_G(A) π'-元 (`IsPiSubgroup π' (zpowers c)`) → c ∈ K。
   証明: X := A ⊔ C_G(A) ≤ N_G(A) < G (simplicity: A ⊴ G なら A=⊥/⊤ 矛盾)。
   Hyp71(2): ⟨c⟩ ∈ ℋ_X(A;π') → c ∈ O_{π'}(X)。O∩C ⊴ C は π'-群 → ≤ K。
4. **共通構成** (Lem 7.1 の段落 1, H 可変):
   入力: Hyp71, q∈π', Q₁ Q₂ ∈ ℋ*_⊤(A;q), H < ⊤, A ≤ H, H⊓Q₁ ≠ ⊥ ≠ H⊓Q₂。
   出力: `∃ h ∈ K, ∃ Q₃ ∈ ℋ*_⊤(A;q), conj h • Q₁ ∈ ℋ*(既知) ∧
   ⊥ < (conj h • Q₁) ⊓ H ∧ (conj h•Q₁) ⊓ H ≤ Q₃ ∧ ⊥ < Q₂ ⊓ H ∧ Q₂ ⊓ H ≤ Q₃ ∧
   card ((conj h•Q₁) ⊓ H) = card (Q₁ ⊓ H)`。
   - 手順: N := opiCoreInG π' H。Hyp71(2) で H⊓Qᵢ ≤ N (H⊓Qᵢ ∈ ℋ_H(A;π') → ≤ sSup)。
   - ↥N: solvable (hG.properSolvable, N ≤ H < ⊤), A-作用 coprime (π vs π')。
   - Prop 1.5(b) ({q}, ↥N): (H⊓Qᵢ).subgroupOf N ≤ Rᵢ A-不変 Hall {q}。
   - Prop 1.5(c): R₁^c = R₂, c は A-固定 = (c:G) ∈ C_G(A) ∩ N。h := c, Note 補題で h ∈ K。
   - R₂ を G に戻し `exists_le_hInvariantStar` で Q₃。
   - (conj h • Q₁) ⊓ H = conj h • (Q₁ ⊓ H) (h ∈ H) → card 等式 + ≤ R₂ ≤ Q₃。
5. **Lem 7.1**: 強帰納法 on `Nat.card G - Nat.card (Q₁ ⊓ Q₂)`
   (BG の |G|_q/|Q₁∩Q₂| と同値な減少測度; 交わり増大 = 測度減少)。
   - Case A `Q₁ ⊓ Q₂ = ⊥`: 共通構成 → 測度減 2 回 (対 (conj h•Q₁, Q₃), (Q₃, Q₂),
     witness H 同一) → 合成 k = g·f·h (Lean conj 左作用は積が逆順)。
   - Case B `Q := Q₁ ⊓ Q₂ ≠ ⊥`: H' := N_G(Q) (proper: simplicity + Q ≠ ⊥ q-群;
     A ≤ H' ✓; H'⊓Qᵢ ⊇ N_{Qᵢ}(Q) ≠ ⊥)。共通構成 on H'。
     - B1 両交わり > |Q|: Case A と同じ合成。
     - B2 片方 ≤ |Q|: |Q| ≥ |N_{Q᷊ᵢ}(Q)| → normalizer 増大 (q-群 nilpotent →
       `normalizerCondition_of_isNilpotent`, subgroupOf 形) → Q = Qᵢ → Qᵢ ≤ Q_{3-i}
       → ★maximality → Q₁ = Q₂, k = 1。

## Phase C (後続): Prop 1.16 → Thm 7.2/7.3

- Prop 1.16 = **G** Thm 6.2.4 (`references/gorenstein/finite-groups.mmd` p.225) +
  |G| 帰納。配置: S01 §1E。statement 案:
  `(hA : IsElementaryAbelian-ish noncyclic abelian p) (φ : A →* MulAut G faithful?)
   (hG : ¬ p ∣ |G|) : (⨆ x ∈ A^#, fixedPoints ⟨x⟩-action) = ⊤` の 2 形。
- Thm 7.2: B ≤ Z(A) elem-ab p³ → Prop 1.16 第 2 形で C_{Q₁}(C) ≠ 1 (C 位数 p²)
  → C noncyclic → 第 1 形で C_{Q₂}(z) ≠ 1 (z ∈ C^#) → H := C_G(z) で Lem 7.1。
- Thm 7.3: B ∈ ℰ_p²(Z(A)), R ⊇ Syl_q(C_G(A)) A-inv maximal; C_R(A) ≠ 1;
  第 1 形で C_{Qᵢ}(x) ≠ 1 → H := C_G(x) で Lem 7.1 を R 経由で連鎖。

## 罠・注意

- BG の `Q^k` は右共役; Lean `MulAut.conj k • Q = kQk⁻¹` 左作用 — 合成順が逆になる。
- `kSubgroup = opiCoreInG π' (centralizer A)` は **map-of-subgroupOf** 形;
  membership は `Subgroup.mem_map` 経由。oPiCore の normality は ↥C 内。
- π = primesOf A は `Set ℕ` (primeFactors の coe); `π'` = `(primesOf A)ᶜ`。
  q ∈ π'ᶜᶜ 系の集合論は `Set.mem_compl_iff` で都度展開。
- `hInvariantStar ⊤ A {q}` の `≤ ⊤` 成分は trivial — mem 構成時は `le_top`。
