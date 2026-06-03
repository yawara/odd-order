# 引き継ぎ: Peterfalvi (6.8) T7 — `Xset_eq` 特徴付け (H1 から再開)

**作業場所**: `/home/ywr/odd-order-pf-engine` (branch `pf-engine-support`)。Bash cwd は毎回 main にリセット
されるので全コマンド `cd /home/ywr/odd-order-pf-engine && …`。main 不可侵 / repr-infra は別セッション。

## 現状 (出発点)
- **B engine surgery 完了済** (T8 blocker 解消, `peterfalvi_66_coherence_of_X_from_dade` が X で instantiate 可)。
- **T7 char H0 完了・commit 済 (3bb133a)**: `isCharacter_restrict` @ `S08_CoherenceTheorems.lean`
  (`variable {L G …}` の直後, ~L39, namespace `OddOrder.Peterfalvi.S08`):
  `{Γ}[Group Γ][Finite Γ]{φ}(hφ:IsCharacter φ)(H:Subgroup Γ) : IsCharacter (ClassFunction.restrict H φ)`。
- `lake build OddOrder` 3562 + AxiomsCheck 3521 green, 新 sorry 0, worktree clean。

## ゴール: `Xset_eq` (mmd 04.8 L74-76, (6.6) 特徴付け)
`SibleyDadeHypothesis` namespace (S08, 既存 `Xset`/`SsubFiltration` defs の近く ~L600) に:
```
theorem Xset_eq_irreducible_not_subset_characterKernel
    (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    hyp.Xset Z = {χ : ClassFunction ↥L ℂ | IsIrreducibleCharacter χ ∧
      ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ)}
```
**最小 Z-仮説 = `Z≤H` + `[Z.Normal]` のみ** (Z⊆Z(H)/Z≠⊥ は本 lemma 不要・upstream)。
T9 の degree-sum (mmd L176 regular char collapse) が消費。**🟢 [Is] 2.21 は不要** (両方向とも genuine char
`Res_H φ`(⊆) / `Ind θ`(⊇) 経由で G2.2 を使い、Dade を unsupported χ に当てない)。

## 残り部品 (H1 → H2 → Xset_eq、S08 に general theorem として H0 の隣に)

### H1 (~50 LOC, fiddly だが確実): constituent が kernel 包含を継承
```
theorem characterKernel_subset_of_isCharacter_of_inner_ne_zero
    {Γ}[Group Γ][Fintype Γ][Invertible (Nat.card Γ:ℂ)] {ψ}(hψ:IsCharacter ψ)
    {χ}(hχ:IsIrreducibleCharacter χ)(hχψ:ClassFunction.inner ψ χ ≠ 0)
    {g:Γ}(hg : g ∈ characterKernel ψ) : g ∈ characterKernel χ
```
proof: `obtain ⟨m,hsupp,hsum,hcoeff⟩ := hψ.exists_natFinsupp_eq_sum` (Clifford:1009)。
G2.2 の family を **dite で total 化**:
- `χfam : ClassFunction Γ ℂ → IrreducibleCharacter Γ := fun a => if h:IsIrreducibleCharacter a then ⟨a,h⟩ else trivialIrreducibleCharacter Γ`
- `d : … → ℕ := fun a => if h:IsIrreducibleCharacter a then (h.exists_natDegree_charValue_one_dvd_card).choose else 0`
- a∈m.support ⟹ `IsIrreducibleCharacter a` (`mem_irreducibleCharacters.mp (hsupp (Finset.mem_coe.mpr ha))`); `(χfam a:CF)=a` via `dif_pos`。
- `hd : ∀a∈m.support, (χfam a:CF) 1 = (d a:ℂ)`: `(…exists_natDegree…).choose_spec.1`。
- `hval`: hg ⟹ `ψ g = characterDegree ψ = ψ 1` (mem_characterKernel S03:326 + characterDegree_def); hsum で
  `ψ g = ∑(m a)*(a g)`, `ψ 1 = ∑(m a)*(a 1)` (ClassFunction の `sum_apply`/`smul_apply` 要確認名)。⟹ G2.2 の hval。
- `irreducibleCharacter_mem_characterKernel_of_natSum_value_eq g m.support (fun a=>m a) χfam d hd hval` →
  `∀a∈m.support, m a≠0 → g∈characterKernel (χfam a:CF)`。
- χ∈m.support & m χ≠0: `hcoeff χ hχ : (m χ:ℂ)=⟨ψ,χ⟩` (≠0 by hχψ) ⟹ m χ≠0 ⟹ `Finsupp.mem_support_iff`。
  (χfam χ:CF)=χ ゆえ g∈characterKernel χ。**inner orientation: hcoeff は ⟨ψ,χ⟩ (genuine,irr)。hχψ も ⟨ψ,χ⟩ で揃える**。

### H2 (~60 LOC, 唯一の不確実点): `Ind θ` の ℕ分解 (or Ind-flavored 継承)
`induce` は class-function-level only ⟹ `IsCharacter (Ind θ)` は直接存在しない。代わりに **Ind θ の natFinsupp 分解**を
ZIrr+Frobenius-nonneg で再現 (exists_natFinsupp_eq_sum @Clifford:1009-1054 を template に):
- `Ind θ ∈ ZIrr G`: `induce_mem_ZIrr` (InducedCharacter:792, θ∈ZIrr から)。
- Fourier 係数 ≥0: `⟨Ind θ, ψ⟩ = ⟨θ, Res ψ⟩` (Frobenius `inner_induce_eq_inner_restrict` InducedCharacter:531,
  **orientation 要確認**) で、`⟨θ(genuine), Res ψ(genuine via H0)⟩ ≥ 0`。
  ⟨genuine,genuine⟩≥0 は: θ を `exists_natFinsupp_eq_sum` で ∑nᵢθᵢ に分解 → `∑nᵢ⟨θᵢ,Res ψ⟩`,
  各 `⟨θᵢ(irr),Res ψ(genuine)⟩ = conj⟨Res ψ,θᵢ⟩ ≥0` (`inner_irreducible_nonneg` Clifford:988 + `inner_conj_symm`)。
- ZIrr + nonneg 係数 ⟹ `Int.toNat` packaging で ℕ分解 (mem_ZIrr_repr + inner_eq_coeff_of_repr, Clifford:1015-1054 参照)。
**代案**: 直接 `characterKernel_subset_of_inner_induce_ne_zero` (Ind版 H1) を上記分解+G2.2 で。どちらでも可。

### Xset_eq 本体 (~100 LOC, H0/H1/H2 + 既存 S03 atom)
unfold: `hyp.mem_Xset` (φ∈S ∧ φ∉SsubFiltration Z), `hyp.mem_SsubFiltration`, `hyp.S_eq` (既存, S08)。
`Set.eq_of_subset_of_subset`:
- **(⊆)** φ∈Xset ⟹ φ既約(hX) ∧ Z⊄Ker φ。φ=Ind θ(θ≠1, S_eq)。`intro hZker`(Z⊆Ker φ); `apply (mem_Xset の φ∉S(Z))`;
  `rw mem_SsubFiltration; exact ⟨θ,hθ_ne, ?_, rfl⟩`; 残 `Z.subgroupOf H ⊆ characterKernel θ`:
  各 n∈Z.subgroupOf H で **H1** (ψ:=Res_H φ via H0 genuine, χ:=θ, ⟨Res φ,θ⟩≠0 via Frobenius+⟨φ,φ⟩=1,
  n∈Ker(Res φ) from Z⊆Ker φ) ⟹ n∈Ker θ。φ∈S(Z) 構成して hφ∉S(Z) と矛盾。
- **(⊇)** χ既約∧Z⊄Ker χ ⟹ χ∈Xset。`exists_inner_induce_ne_zero`(S03:636)→θ (⟨Ind θ,χ⟩≠0)。
  θ≠1: θ=1⟹Z.sub⊆Ker θ=univ⟹(1.6.a fwd `subsetCharacterKernel_induce_of_subgroupOf` S03:563)Z⊆Ker(Ind θ)⟹
  (**H2** constituent χ 継承)Z⊆Ker χ, 矛盾。Ind θ∉S(Z): θ'witness で同様 H2 ⟹ Z⊆Ker χ 矛盾。
  ⟹ Ind θ∈Xset → hX → Ind θ既約 → `irreducibleCharacter_inner_eq_ite`(ZIrrFourier:40)で Ind θ=χ → χ∈Xset。

## Lean 罠 (本セッションで判明)
- `restrict_repCharacterClassFunction` は `OddOrder.RepresentationTheory.ClassFunction` namespace
  ⟹ `ClassFunction.restrict_repCharacterClassFunction` (S08 は RepresentationTheory のみ open)。
- `IsCharacter` 分解 = 6 成分 `obtain ⟨V,_,_,_,ρ,hρ⟩` (hρ:(φ:Γ→ℂ)=ρ.character)。匿名 instance は inferInstance で拾われる。
- `φ = repCharacterClassFunction ρ` は `ClassFunction.ext fun g => by rw [repCharacterClassFunction_apply]; exact congrFun hρ g`
  (plain rw は unsolved goal; `exact congrFun` が coe を処理)。
- `IrreducibleCharacter Γ = {φ // IsIrreducibleCharacter φ}` (subtype, IrrIndexing:28)。`irreducibleCharacters Γ = {φ|IsIrr φ}` (Set, ZIrr:145), `mem_irreducibleCharacters` (ZIrr:148)。
- inner smul: `ClassFunction.inner_smul_left (c•u) v = c*⟨u,v⟩`; `OddOrder.RepresentationTheory.inner_smul_right u (c•v) = star c*⟨u,v⟩`; nsmul は `← Nat.cast_smul_eq_nsmul ℂ a u` で ℂ-smul 化, `star_natCast`。

## 実装順 (build-green incremental, anti-scaffold: sorry 足さない)
1. H1 → `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` (速い) green。
2. (⊆) 方向だけ先に landable (H0/H1+Frobenius のみ, H2 不要) — 中間 commit 可。
3. H2 → (⊇) 方向 → Xset_eq 完成。`lake build OddOrder` + AxiomsCheck green, commit。
正本設計 = `s08_6_8_assembly_plan.md` §H + 本 file。
