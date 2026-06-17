> ⚠️ **2026-06-17 STATUS 訂正**: (6.8)/(6.8.3)/case-B capstone の現状は [`s08_6_8_3_gap_resolution.md`](s08_6_8_3_gap_resolution.md) が正本。
> 本ロードマップ内の「(6.8.3) very hardest / final contradiction 未実装 / Wave 5 7-10日 / ★★★★★」は **stale**:
> (6.8.3) の数学 gap=0、final contradiction (`false_of_caseB_break_of_bounds` @ S08_CaseBEndgame) + counting (`sum_re_sq_Xset_eq`) + 重み付き (5.6) (`S08_CoherenceWeighted`) は**既に sorry-free 着地済**。残務は case-B glue のみ（唯一 sorry `S08_CoherenceTheorems:59`）。

# Peterfalvi §8: Some Coherence Theorems — mini-roadmap

**スコープ**: Peterfalvi §8 (pp. 30-37), mmd `04.8_pp_30_37_*.mmd` (243 行), **8 結果 ((6.1)-(6.8)) 全て同格 named results** ⚠️ audit 訂正 (旧記載「4+2 結果」は `**(N.M)**` grep artifact).

形式化先 (予定): `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean`.

ROADMAP 上の位置: **Phase 2b 第 3 波** (§7 Coherence 完成直後).

役割: **§7 で定義した Coherence の応用定理群**. Sibley 系の表現論的特性化. §9-§16 構造分析の重要な道具.

## Audit log (2026-05-23 audit 訂正)

統合 doc: [`notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md`](../meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md).

- **L3 "4 + 2 結果 (6.1)-(6.4), (6.5)-(6.8) は拡張"** → **重大誤認: 実際 8 結果 (6.1)-(6.8) 全て同格 named results**. overview の "4 結果" は `**(N.M)**` grep artifact.
- **L18, L137, L142, L257 "Sibley 1984 Contemp. Math. 47"** → **完全捏造**. 訂正: Peterfalvi Notes §SS6 (mmd 04.17 L11) 明示「(6.3), (6.5) は **[FT] §11** から; (6.8) only is Sibley」. Sibley 参照は実際 **[Si1] = Sibley 1976 *Illinois J. Math.* 20:434-442** "Coherence in finite groups containing a Frobenius section" + [Si2] unpublished lectures. **"Contemp. Math. 47" は存在しない**.
- **L20, L158, L181, L261-273 "Reynolds 1965 Duke Math. J."** → **完全捏造**. Reynolds は Peterfalvi 参考文献 (`04.18`) + Notes (`04.17`) **両方に存在せず**. (6.7) は無名 internal lemma. **L261-273 sub-section 全削除推奨**.
- **L24 "mathlib coverage ~5%"** → (6.7)/(6.8) は **0%**. 既存「statement-level」評価は表面のみ; proof-internal で 10 helper lemma + 2 新規 module 要.
- **(6.7) は character-class congruence 単独 theorem**, (6.8) Sibley の前段補題. proof で **[Is] p.35 class-sum algebra hom `ω : ZC[G] → C`** (mathlib 不在) + **algebraic integer congruence** (mathlib 不在) + **TI-subset (§4-§5)** + **[Is] Lem 7.7** (§8 で 2 回) 利用. **`OddOrder/RepresentationTheory/ClassSumAlgebraHom.lean` + `AlgInt.cong.lean` 新規** 要.
- **(6.8) は §9, §12 (Type V), §14 (Type I) の各章 single decisive use** で「全 type を一発で消す」道具. forward は §13=6, §12=3, §9=1, §14=1.
- **[Is] cites in §8 = 8 件** (Lem 7.7 ×2, Thm 6.34 ×3, Cor 2.30 ×2, p.35 ω, Lem 2.27). 全 proof body cite, mathlib 対応**ゼロ**.
- **L405-408 "30 days"** → **35-45 days realistic** ((6.7) class-sum module + (6.8) full Sibley apparatus).
- §8 mmd 243 行は §3-§8 中 **最大**, 結果数 8 で **§3-§8 implementation effort の ~40% 単独占有**.
- **File 分割推奨**: A_Descent ((6.1)-(6.3)), B_OddOrderStructure ((6.4)-(6.6)), C_SibleyMainTheorem ((6.7)-(6.8)).

## TL;DR

§8 は **8 つの主定理** ((6.1)-(6.8)) 全て同格:

1. **(6.1) Hypothesis**: 仮説セットアップ (K solvable normal, S = 導入指標集, S(A) filtration)
2. **(6.2) Lemma**: Coherence の「失敗」判定式 — 不等式で coherence 喪失の条件をバウンド
3. **(6.3) Theorem**: nilpotent 商での Coherence 伝播 — M から H_1 へ下降
4. **(6.4) Hypothesis**: **奇数位数下の特殊化** — Frobenius + TI-subset + cyclic normalizer の総合
5. **(6.5)-(6.6)**: ⚠️ audit 訂正: 本書 Notes §SS6 (mmd 04.17 L11) 明示「(6.3), (6.5) は **[FT] §11** から; Sibley とは無関係」. (6.6) は center coherence
6. **(6.7)**: character-class congruence (Galois 整数性). proof で [Is] p.35 class-sum algebra hom + AlgInt congruence (両方 mathlib 不在). ⚠️ audit 訂正: 旧記載「Reynolds 1965 Duke Math. J.」は **完全捏造** (Peterfalvi 参考文献/Notes に Reynolds **不在**); (6.7) は無名 internal lemma
7. **(6.8) Main Theorem (= Sibley の唯一の寄与)**: L が Frobenius or Dade condition 満たす時 S が coherent. ⚠️ audit 訂正: **Sibley 参照は [Si1] Sibley 1976 *Illinois J. Math.* 20:434-442** "Coherence in finite groups containing a Frobenius section" + [Si2] unpublished lectures. "Sibley 1984 Contemp. Math. 47" は **存在しない**

**mathlib カバレッジ**: ~5% statement-level (表面のみ); **(6.7)/(6.8) は実 0%**. proof-internal で 10 helper lemma + 2 新規 module (`ClassSumAlgebraHom.lean` + `AlgInt.cong.lean`) 要. Coherence framework (§7) の上に全面構築.

**FT 必須度**: ☆☆ (§8 自体は局所的に完結しているが、§9-§16 では頻出. 特に (6.8) が §10-§14 の Type I-V 構造分析の土台)

## Lean status (2026-05-26)

`OddOrder/Peterfalvi/S08_CoherenceTheorems.lean` currently records the carrier
structures for §8:

- `DescentHypothesis`: (6.1) の solvable-normal filtration setup。
- `FiltrationData`: (6.1) の `S(A)` を、基底集合 `S` への包含と
  `A ≤ B → S(B) ⊆ S(A)` という kernel filtration の向き付きで保持。
  `zSupportedSpan` への lift も持つので、`Z[S(A),B]` から `Z[S,B]`
  への戻しと filtration の単調性を直接使える。
- `OddOrderSpecialization`: (6.4) の odd-order specialization carrier。
- `SibleySetup`: (6.8) の final setup with TI-subset condition。
- `SibleySetup.CoherenceTarget`: §7 `IsCoherent` target attached to the setup。
- `coherence_tau_inner_eq`: §7 hypothesis に含まれる `tau_isometry` を §8
  setup から直接使う。
- `coherence_inner_eq_on_supported`: proved coherence target があるとき、
  `Z[S,A]` 上で `τ` 自身が inner product を保存することを §8 setup から直接使う。

### (2026-05-31) §7 (5.6) coherence-union 依存の sub-lemma 진척

§8 (6.2)/(6.6)이 반복 invoke하는 **§7 Theorem (5.6)** (coherence-union hub)의
family-free honest sub-lemma 2개를 `S07_Coherence.lean`에 landing (sorry/axiom 無):
`int_eq_zero_of_sq_mul_le_of_two_mul_lt` ((5.6.2) integer-forcing core, division-free
`2a < D, λ²D-2λa+z ≤ 0 ⇒ λ=0`) + `CharacterPsiDecomposition.inner_self_Y_re_le_inner_self_psi`
((5.6.2) 첫 norm bound `‖Y‖² ≤ ‖ψ‖²`). 상세·잔여는 `notes/peterfalvi/s07_coherence.md`
"(2026-05-31)" 절. (5.6) main `IsCoherent(S₁∪{χ,χ̄})`의 단일 blocker = `τ₂`의
**전역** `IsIntegralIsometry` 확장 생성자 (repo/mathlib 부재; orthonormal-basis → 전역 등거리).

### (2026-05-31, pass 5) USER-APPROVED def 약화 → general (5.6) UNCONDITIONAL 완성 (commit b14a987)

위 blocker를 **정의 약화**로 해소하여 §5 coherence hub (5.6)을 일반형으로 닫음
(`S07_Coherence.lean`/`S08_CoherenceTheorems.lean`/`AxiomsCheck.lean`; sorry/axiom 無 —
`#print axioms retarget_isCoherent` = {propext, Classical.choice, Quot.sound}; full
`lake build OddOrder`/`OddOrder.AxiomsCheck` 緑).

- **`IsCoherent` 약화** (USER-APPROVED, 이 branch 한정): 전역 필드
  `extension_isometry : IsIntegralIsometry extension` → 격자-相對
  `extension_inner_eq : ∀ φ ψ ∈ zSpan S, ⟨ν φ, ν ψ⟩ = ⟨φ, ψ⟩`. 이유: FT에서
  `dim CF(L) > dim CF(G)`이라 character-difference 격자를 `CF(G)`로 보내는 **전역** 등거리는
  일반적으로 부재; Peterfalvi (5.6.3)이 실제로 주장하는 대상은 **격자** 등거리이고, 모든 하류
  consumer가 격자원 `ζ∈S`에만 inner-preservation을 쓴다.
- **신규 keystone** (`namespace IntegralCharacterMap`, AxiomsCheck 등록 2건):
  - `orthoResidualMap_mem_zSpan`: {χ,χ̄} Gram–Schmidt 잔차가 `ℤ[S₁∪{χ,χ̄}] → ℤ[S₁]`
    (`span_induction`; 생성원 x∈S₁↦x [x⊥{χ,χ̄}], χ↦0, χ̄↦0). 이것이 전역 등거리 없이 격자
    등거리를 가능케 하는 핵심 격자 사실.
  - `retarget_inner_eq_on_zSpan_union`: `retarget_inner_eq_on`의 정직 충족형 integral-span 판.
    재타게팅이 `ℤ[S₁∪{χ,χ̄}]` 전체에서 `⟨·,·⟩` 보존, **τ₁의 `ℤ[S₁]`-등거리** (= S₁ coherence)
    + 격자 직교 `X,X̄ ⊥ τ₁ξ` (ξ∈ℤ[S₁]) 만 사용 (전역 등거리/over-strong 입력 불요). 잔차∈ℤ[S₁]
    ⟹ `inner_block_expand`로 폐합.
- **`retarget_isCoherent` 이제 UNCONDITIONAL general (5.6)**: `hX_ortho`/`hXbar_ortho`를 정직한
  격자형 (`∀ξ∈ℤ[S₁]`)으로 약화 (전역 `∀ξ⊥{χ,χ̄}`보다 약한 가설 = 더 강한 정리), τ₂:=retarget
  구성, `retarget_inner_eq_on_zSpan_union`로 약화된 `IsCoherent` 산출. **special-position 제한
  제거**; X,X̄⊥S₁^{τ₁}는 진짜 (5.5)+(5.2.e) 격자 사실 (posit 無).
- **S08 consumer 적응**: `IndChainDecomposition.ofIsCoherent`에 `hζ_mem : ∀ t, ζ t ∈ S` 추가,
  `Submodule.subset_span` (ζt∈S⊆zSpan S)로 격자 `extension_inner_eq` 공급. 약화는 consumer
  증명을 **쉽게** 만들 뿐 (전역성 미사용이었음). `sibleySetup_is_coherent` (S08:188, 여전히
  sorry)는 약화된 `CoherenceTarget`에 그대로 typecheck — 향후 증명도 약화로 더 쉬워짐.
- **2026-06-04 追記**: `IndChainDecomposition` consumer helper 5 件 (`image_eq_zero`,
  `inner_chi_eq_ite`, `inner_chi_weightedOutput`, `weightedOutput_inner_self_eq_sum_sq`,
  `ofIsCoherent`) を AxiomsCheck に登録。(7.10) 側がこの interface を使うとき、`sibleySetup_is_coherent`
  の未完成 proof と独立に consumer packaging が axiom-clean であることを CI で固定した。
- **2026-06-04 追記 2**: `weightedDifferenceInput` / `image_weightedDifferenceInput` を追加。
  (7.10) で使う整数係数付き source difference `∑ d_t(ζ_t - d_tζ_0)` へ `image_eq` を合成する
  ℤ-linear consumer lemma。`IntegralCharacterMap` は ℂ-linear ではないため、source 側は `zsmul`
  で表現し `map_zsmul` で証明する。AxiomsCheck 登録済み、3 axiom allowlist 内。
- **의의**: (5.6)은 쌍 인접으로 coherence를 짓는 **귀납 엔진**, §6 (case-A/B coherence) 및
  궁극적으로 S08:188 `sibleySetup_is_coherent`로의 관문. 상세는 issue 0046 pass-5.

### (2026-05-31, pass 6) (6.8.1)/(6.8.2) `τ₃`-gluing의 algebraic heart landing (PARTIAL)

`S07_Coherence.lean`에 **orthogonal coherent union** 항등식 2건 landing (sorry/axiom 無 —
`#print axioms` = {propext, Classical.choice, Quot.sound}; AxiomsCheck 등록 2건 각 3 axiom 전
allowlist; full `lake build OddOrder` 緑 3351 jobs). **roadmap의 recommended first leaf
`case_A_X_union_Y_coherent` (L2.2)는 NOT tractable로 판정** (아래), 대신 그 leaf와 case (B)가
*공통으로* 소비하는 가장 foundational한 honest primitive를 landing:

- **`inner_orthogonal_glued_eq`** (two-lattice block identity): `a,a'∈ℤ[X]`, `b,b'∈ℤ[Y]`에 대해
  `νX`가 `ℤ[X]`에서, `νY`가 `ℤ[Y]`에서 `⟨·,·⟩` 보존 + source 직교 (`⟨a,b'⟩=⟨b,a'⟩=0`) + image
  직교 (`⟨νX a, νY b'⟩=⟨νY b, νX a'⟩=0`) ⟹
  `⟨νX a + νY b, νX a' + νY b'⟩ = ⟨a + b, a' + b'⟩`. `inner_block_expand`의 two-lattice 판; 양변이
  대각 블록 `⟨a,a'⟩+⟨b,b'⟩`로 collapse. Peterfalvi의 "`τ₃`는 `τ₁`을 `Y`에, `τ₂`를 `X`에 일치"
  (mmd L176/L224) gluing의 **대수적 심장**.
- **`inner_eq_on_zSpan_union_of_orthogonal`**: 위 항등식을 `ℤ[X∪Y]=ℤ[X]⊔ℤ[Y]`
  (`Submodule.span_union`) 전체로 lift — `νX`를 `ℤ[X]`에, `νY`를 `ℤ[Y]`에 일치시키는 **임의**의 map
  `ν`에 대해 `ν`가 `ℤ[X∪Y]`에서 `⟨·,·⟩` 보존. `φ∈ℤ[X∪Y]`를 `a+b` (`mem_sup`)로 분해 ⟹
  `ν φ=νX a+νY b` ⟹ `inner_orthogonal_glued_eq`로 폐합. = 합집합 `X∪Y`의 glued map `τ₃`에 대한
  약화된 `IsCoherent.extension_inner_eq` field 그 자체.
- **honest 판정 — L2.2가 NOT tractable인 이유** (roadmap의 "(5.6) direct consumer ~100-140 LOC"는
  과대평가): (6.8.1) 증명 (mmd L158-176)은 `retarget_isCoherent` 1회 호출이 **아니다** —
  (1) **(6.6)** coherence-of-`X` (별도의 ~8-step character theorem, 미형식화),
  (2) **(6.7)** congruence forcing `b≡c≡0 (mod a)` + 명시적 `X=χ₁^{τ₁}` 동정 (미형식화),
  (3) `τ₃` = **두 family** `X`, `Y` (임의 크기)의 orthonormal union — repo에는 single-pair
  `retarget` closed-form만 있고 two-family union 구성 (free-module/orthonormal-basis extension)이
  부재. 게다가 thin `SibleySetup`은 `S=Ind`/Dade isometry/`X`/`Y`/`τ₁`/`τ₂`/(6.6)를 전혀 안 들고
  있어 statement화하면 case content를 가설로 외출 = memory `scaffold-sorry-free-not-done`가 금하는
  scaffolding. 따라서 정직하게 **두 항등식 (gluing의 hard algebraic step)만 landing**.
- **정밀 잔존 (full `case_A_X_union_Y_coherent` = L2.2)**:
  (i) **(6.6)** coherence-of-`X` witness (별 issue/leaf),
  (ii) `νX`(=τ₂)/`νY`(=τ₁) coherence extension 및 image 직교 `himg_ortho`를 case-A/B character
  theory ((6.7) 포함)에서 *생성* (위 두 항등식의 honest 가설들을 채우는 작업),
  (iii) glued map `ν=τ₃`의 **well-defined 구성** = orthonormal `X∪Y`의 ℤ-linear independence ⟹
  free-module basis extension (repo/mathlib 부재 infra) + `extends_on_supported`
  (`eq_on_zSpan_of_eq_on` generator 패턴, case별 difference-generator 구조 필요). (iii)이 본 leaf의
  핵심 missing infra. 상세는 issue 0046 pass-6.

### (2026-05-31, pass 7) (6.8.1)/(6.8.2) `τ₃` 두-family `IsCoherent` 조립기 landing (PARTIAL)

`S07_Coherence.lean`에 **`coherentUnion_of_glued`** landing (sorry/axiom 無 —
`#print axioms` = {propext, Classical.choice, Quot.sound}; AxiomsCheck 등록 1건 3 axiom 全 allowlist;
full `lake build OddOrder` 緑 3351 jobs). pass-6의 두 gluing 항등식의 **자연스러운 소비자** = 실제
`IsCoherent (X∪Y) A` witness 산출, single-pair `retarget_isCoherent`의 **두-family 유사물**:

- **`coherentUnion_of_glued`** (`noncomputable def`): 입력 = `hX : IsCoherent τ X A`,
  `hY : IsCoherent τ Y A` (**공급** 데이터, posit 無; (6.6) 와 (1.1)·(1.4)의 결론), 글루 map
  `ν : IntegralCharacterMap L G` (`hX.extension`에 `ℤ[X]`, `hY.extension`에 `ℤ[Y]`에서 일치 =
  Peterfalvi의 `τ₃`), source 직교 `hsrc_ortho`, image 직교 `himg_ortho`, (5.1)-type 생성 가설 `hgen`.
  출력 = `IsCoherent τ (X∪Y) A`. 두 field 방전: `extension_inner_eq` =
  `inner_eq_on_zSpan_union_of_orthogonal` (격자 등거리 `hX`/`hY.extension_inner_eq` + 직교성 투입),
  `extends_on_supported` = `eq_on_zSpan_of_eq_on` over generator `Z[X,A]∪Z[Y,A]` (각 lattice 위
  `ν=νX=τ` / `ν=νY=τ`, `hagreeX`+`hX.extends_on_supported` 등), `nonzero`는 `X⊆X∪Y`에서 상속.
- **honest 판정**: 조립기는 character theory 미포함 — 입력 `hX`/`hY`/`hagreeX`/`hagreeY`/직교성/`hgen`을
  *생산*하는 ((6.7) congruence, 명시 `X=χ₁^{τ₁}` 동정, Dade isometry) 가 별도 작업으로 남음. glued map
  `ν=τ₃` 자체의 canonical 구성은 ℂ-valued 공간이라 ℤ-projection이 비정수 계수 ⟹ free-module 기저 확장
  infra 필요 (부재) ⟹ `ν`를 supplied data로 받음 (Peterfalvi의 `τ₃`가 orthonormal 기저에서 실제로
  구성되는 정직한 입력). **조립기는 완결**; 남은 건 (i) (6.6) coherence-of-X `hX`, (ii) case-A/B
  character theory (가장 무거운 덩어리), (iii)-canonical glued-map 구성. 상세는 issue 0046 pass-7.

### (2026-05-31, pass 8) (6.6) "repeated use of (5.6)" iteration engine `coherentPairChain` landing

`S07_Coherence.lean`에 **(6.6) 증명의 결론 단계** "Repeated use of Theorem (5.6) then shows that X is
coherent" (mmd L84)를 형식화한 **반복 엔진** landing (sorry/axiom 無 — `#print axioms coherentPairChain`
= {propext, Classical.choice, Quot.sound}; AxiomsCheck 등록 2건 각 3 axiom 전 allowlist; full
`lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3351/3334 jobs). single-pair `retarget_isCoherent`를
pair 수에 대한 induction으로 fold하는 정직한 핵심:

- **`pairSet pair i`** (= `{(pair i).1, (pair i).2}` = i-번째 pair `{χᵢ, χ̄ᵢ}`), **`pairUnion S₀ pair`**
  (`0 ↦ S₀`, `i+1 ↦ pairUnion … i ∪ pairSet … i` = i번 adjoin 후 누적집합), `pairUnion_zero`/
  `pairUnion_succ` (simp), `subset_pairUnion_succ`, **`pairUnion_mono`** (`i≤j ⟹ ⊆`).
- **`coherentPairChain`** (`noncomputable def`): `h0 : IsCoherent τ S₀ A` (base = (1.1)/(1.4) prefix
  coherence) + `hstep : ∀ i<N, IsCoherent τ (pairUnion S₀ pair i) A → IsCoherent τ (pairUnion S₀
  pair (i+1)) A` (각 step = (5.6) 1회 = `retarget_isCoherent`) ⟹ `IsCoherent τ (pairUnion S₀ pair N) A`.
  proof는 `N`에 대한 recursion (`0↦h0`, `N+1↦hstep N _ (recurse N, step 약화)`). 엔진은 induction
  자체만 기여 — 최종 coherence는 **derived** (posit 無). general·reusable (임의 chain). 각 `hstep i`의
  (5.6) data (`hX_ortho`/`himg` 등)는 *현재* 확장 `hcoh.extension`을 참조하므로 running witness의
  함수로 주어짐 = "repeated use"의 본질 구조.
- **honest 판정 (G1 skip)**: 이번 round의 G1 plumbing (L1.1 Dade 추출 / L1.2 case-A/B split)은 honest
  하지 않아 skip. `SibleySetup`는 Dade isometry 필드/X·Y 집합/case-A/B flag (`Z(H)∩[H,H]` vs `W₂`)/
  (6.6) data를 **보유하지 않음** (필드 = `coherence`/`K`/`H`/`W1`/`H_sharp_ti`/normality). L1.1은
  `hyp.coherence.tau` 필드 접근 (이미 `coherence_tau_inner_eq`로 노출) = thin wrapper (규약 금지);
  L1.2는 `Z`·`W₂`·case 술어를 새 가설로 외출해야 함 = scaffolding (memory `scaffold-sorry-free-not-done`
  금지). 상세는 issue 0046 pass-8.
- **(6.6) 남은 작업**: 각 step의 (5.6) data 생산 (degree sort / θᵢ(1) = p-power / [Is] Cor 2.30
  `θᵢ(1)²≤|K:Z|` / (6.4.c) `(|L:K|,p)=1` ⟹ `χᵢ(1)²∣∑_{j<i}χⱼ(1)²` ⟹ degree 부등식
  `2χᵢ(1)χ₁(1)<∑_{j<i}χⱼ(1)²`) + base prefix coherence ((1.1)/(1.4)). 이들이 `coherentPairChain`의
  `hstep`/`h0`를 채움.

### (2026-06-04) T8.11l `XAdjoinStepInput` assembly from member-family degree ratios

`S08_CoherenceTheorems.lean` に
`SibleyDadeHypothesis.xAdjoinStepInput_of_memberFamily_degreeRatios` を landing。これは
`pairUnion (xBaseBlock Z) pair i` の member-family cover と anchor `χ₁` に対する explicit degree ratios を
受け取り、per-step `XAdjoinStepInput` を直接構成する bridge。

放電済み field:

- new pair core: `hrealχ`/`hdiffsuppχ`/4 orthogonality/prefix orthogonality は
  `xPair_stepCoreFacts_of_irreducible_X` から。
- member scaled supports: `hmemdegdiffsupp` は `xMember_scaledDiffSupports_of_degreeData` から。
- new scaled support and ZIrr: `hdiffasuppχ` と `htau1_memaχ` は
  `xMember_scaledDiffSupport_of_degreeData` + `scaledDiff_dadeImage_mem_ZIrr` から。
- `hSgen`: prefix cover `hcover` と member scaled supports を
  `S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs` に渡して構成。

この bridge の残 input は意図的に純算術側へ押し込めている:

- `ha1 : deg i₁ = 1`
- `hdeg_mem : χmem j (1) = deg j * χ₁(1)`
- `hdegχ : χᵢ(1) = a * χ₁(1)`
- `hDeg : 2 * (a : ℝ) < ∑ j∈s, (deg j : ℝ)^2`

追加で `normalizedDegreeGap_of_realDegreeBound` を landing。絶対次数不等式
`2 * χᵢ(1) * χ₁(1) < ∑ χmem(j)(1)^2` と同じ anchor に対する ratio data から、anchor の正の
次数 `χ₁(1)^2` で割って normalized `hDeg` を得る。

これで `xAdjoinStepInput_of_memberFamily_degreeRatios` に渡す `hDeg` は、§6.6 側が absolute bound を
出せば直接変換できる形になった。ratio 生成は `exists_pos_natDegreeRatioFamily_of_dvd` と
`exists_pos_natDegreeRatio_of_dvd` で用意済み。

さらに `realDegreeBound_of_natDegreeSumPrimePowerGap` と
`normalizedDegreeGap_of_natDegreeSumPrimePowerGap` を landing。§7 の純算術 leaf
`two_mul_lt_sq_of_primePow_gap` + `two_mul_lt_of_sq_dvd_of_gap` を、S08 の real absolute degree bound
および normalized `hDeg` へ直接接続した。caller が自然数 degree 値、member square-sum identity
`∑ dmem(j)^2 = D`、prime-power gap data、square-divisibility `dχ^2 ∣ D` を供給すれば、
`xAdjoinStepInput_of_memberFamily_degreeRatios` の `hDeg` まで一気に得られる。

残る真正 §6.6 入力は、real/normalized 変換ではなく、character theory から自然数 degree 値・
member square-sum identity・prime-power gap・square-divisibility data を生成する部分。

同日追記: `exists_natDegreeData_for_xAdjoinMemberFamily` と
`SibleyDadeHypothesis.xAdjoinStepInput_of_memberFamily_natDegreeGap` を landing。前者は新規文字・
anchor・finite member family の自然数 degree witness と member square-sum `D`、および `i₁ ∈ s`
からの `0 < D` を package する。後者は member-family cover + degree-ratio equations + natural degree
witnesses + prime-power/square-divisibility gap data から、normalized `hDeg` を別途渡さず直接
`XAdjoinStepInput` を構成する bridge。これで §6.6 側の frontier は、ratio equation 自体と
square-divisibility/prime-power data を実際の character theory から生成する部分にさらに絞られた。

同日追記 2: `SibleyDadeHypothesis.xAdjoinStepInput_of_memberFamily_degreeDivisibility_natGap`
を landing。`exists_pos_natDegreeRatioFamily_of_dvd` / `exists_pos_natDegreeRatio_of_dvd` で
member-family ratio function `deg` と新規 scalar `a` を divisibility hypotheses から非計算的に選び、
上の nat-gap bridge に接続する。§6.6 caller は ratio equation を直接作らず、degree divisibility +
natural degree values + prime-power/square-divisibility gap data を出せば `XAdjoinStepInput` まで
進める形になった。残 frontier はこの divisibility と square-divisibility/prime-power data の
実 character-theoretic producer。

### (2026-05-31, pass 2) (6.6) prime-power degree gap (mmd L82) leaf — degree 부등식 방전

`coherentPairChain`의 각 `hstep`이 소비하는 **strict degree-ratio bound** `2·χᵢ(1)·χ₁(1) <
∑_{j<i}χⱼ(1)²`을 (6.6)의 prime-power 구조에서 정직하게 도출하는 number-theoretic leaf 3건을
`S07_Coherence.lean` (`int_eq_zero_of_sq_mul_le_of_two_mul_lt` 직후 (5.6) section 안)에 landing
(sorry/axiom 無 — `#print axioms` = {propext, Classical.choice, Quot.sound}; AxiomsCheck 등록 2건 각
3 axiom 全 allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3351/3334 jobs):

- **`two_mul_lt_sq_of_primePow_gap`** (ℕ): `dᵢ = q·d₁`, `q = p^m`, `p ≥ 3`, `d₁ < dᵢ` ⟹
  `2·dᵢ·d₁ < dᵢ²`. proof: `q > 1` (else `dᵢ ≤ d₁`) + `q = p^m > 1` ⟹ `m ≥ 1` ⟹ `p ≤ q` ⟹
  `dᵢ = q·d₁ ≥ p·d₁ ≥ 3·d₁`, `nlinarith`. = mmd L82의 `2χᵢ(1)χ₁(1) < pχᵢ(1)χ₁(1) ≤ χᵢ(1)²`의
  load-bearing 산술 (χⱼ(1)=|L:K|·θⱼ(1), θⱼ(1) p-power ⟹ χᵢ(1)/χ₁(1)=p^m; `|L| odd ⟹ p ≥ 3`).
- **`two_mul_lt_of_sq_dvd_of_gap`** (ℕ): gap + `dᵢ² ∣ D` (= `χᵢ(1)² ∣ ∑_{j<i}χⱼ(1)²`) + `0 < D` ⟹
  `2·dᵢ·d₁ < D` (positivity로 `dᵢ² ≤ D`).
- **`two_mul_degree_lt_sum_ratCast`** (ℚ, consumer-facing): 위 둘 합성 ⟹
  `2·((dᵢ:ℚ)·(d₁:ℚ)) < (D:ℚ)` = (5.6) core의 `2·a < D` 전제 직접 공급. 각 `coherentPairChain` step의
  (5.6.2) integer-forcing의 degree 가설이 ℕ degree data에서 방전됨.
- **honest 판정**: prime-power gap (`dᵢ = q·d₁`)와 square-divisibility (`dᵢ² ∣ D`)는 둘 다 (6.6) data의
  정직한 귀결 (K = p-group ⟹ θ degree p-power; (6.4.c) coprimality + sum identity). posited 아님.
- **(6.6) 잔여 (pass-2 이후)**: degree sort + per-index prime-power gap 가설 (`χᵢ(1)=q·χ₁(1)`, `q=p^m`) +
  square-divisibility (`χᵢ(1)² ∣ ∑_{j<i}`; [Is] Cor 2.30 + sum identity + (6.4.c)) 를 본 leaf에 plug +
  base prefix coherence ((1.1)/(1.4)). degree-bound 부분은 본 leaf가 공급. 상세는 issue 0046 pass-2.

**leaf 2 (square-divisibility producers, mmd L78-80)**: leaf 1의 `hdvd` (`χᵢ(1)² ∣ ∑_{j<i}χⱼ(1)²`)을
*생산*하는 mmd L80 chain의 두 산술 step을 `S07_Coherence.lean` (`two_mul_degree_lt_sum_ratCast` 직후)에
landing (sorry/axiom 無 — `#print axioms` = {propext, Quot.sound}; AxiomsCheck 등록 2건 각 2 axiom 全
allowlist):

- **`dvd_of_add_eq_of_dvd_dvd`** (ℕ): `head + tail = total`, `a∣tail`, `a∣total` ⟹ `a∣head`. mmd
  L78+L80 combination (`head=∑_{j<i}`, `tail=∑_{j≥i}`, `total=|L|-|L:Z|`; `θᵢ(1)²∣tail` + `θᵢ(1)²∣total`
  ⟹ `θᵢ(1)²∣head`). **additive equation**로 진술해 ℕ subtraction 회피.
- **`sq_dvd_of_factored_coprime`** (ℕ): `χᵢ(1)=idx·θ`, `θ²∣D`, `idx²∣D`, `Coprime idx θ` ⟹ `χᵢ(1)²∣D`.
  mmd L80 coprimality forcing (`(|L:K|,p)=1` & θ p-power ⟹ `Coprime idx² θ²`; coprime divisors 곱).
- **2026-06-04 追記**: **`sq_dvd_of_factored_coprime_add_complement`** を追加。`head+tail=total`,
  `θ²∣tail`, `θ²∣total`, `idx²∣head`, `χᵢ(1)=idx·θ`, `Coprime idx θ` から `χᵢ(1)²∣head` を直接返す
  consumer-facing 版で、上の additive complement と coprime forcing を S08 `hdvd` 入力の形に合成する。
- **2026-06-04 追記 2**: **`sq_dvd_sum_sq_mul_of_dvd`** を追加。`∀ j∈tail, θ∣θⱼ` から
  `θ²∣∑_{j∈tail}(idxⱼ·θⱼ)²` を返し、`θᵢ(1)²∣∑_{j≥i}` の `Finset.dvd_sum` 部分を独立に閉じる。
- **2026-06-04 追記 3**: **`sq_dvd_primePow_of_sq_le`** / **`sq_dvd_primePow_mul_of_sq_le`** を追加。
  `θ=p^m`, `q=p^n`, `θ²≤q` から `θ²∣q`、さらに `θ²∣q*c` を返し、[Is] Cor 2.30 の
  `θᵢ(1)²≤|K:Z|` を p-power 比較で total 側 divisibility へ落とす算術部分を切り出した。
- **2026-06-04 追記 4**: **`dvd_primePow_of_le`** / **`dvd_primePow_of_mul_le_mul`** /
  **`sq_dvd_sum_sq_mul_const_of_primePow_mul_le`** を追加。degree-sort の `idx·θ≤idx·θⱼ` から
  固定正 `idx` をキャンセルし、同じ `p` の冪比較で `θ∣θⱼ`、さらに tail 側 `θ²∣∑(idx·θⱼ)²`
  まで直接返す producer。
- **2026-06-04 追記 5**: **`mul_primePow_dvd_mul_primePow_of_le`** /
  **`sq_dvd_head_of_commonIndex_primePower_sums`** と S08 adapter
  **`natDegreeDvd_of_commonIndex_primePowerData`** /
  **`degreeDivisibilityInputs_of_commonIndex_primePowerData`** /
  **`xAdjoinStepInput_of_memberFamily_degreeDivisibility_primePowerSums`** を追加。common `idx`
  + p-power 残差 + degree sort から degree-ratio 用 divisibility を作り、さらに tail/total/head
  算術 chain から `dχ²∣D` を内部構成して `XAdjoinStepInput` へ渡す。
- **2026-06-04 追記 6**: **`xAdjoinStepInput_of_memberFamily_commonIndexPrimePowerSums`** を追加。
  前項の `degreeDivisibilityInputs_of_commonIndex_primePowerData` と `primePowerSums` constructor を接続し、
  `XAdjoinStepInput` interface から抽象 `hdvd_mem` / `hdvdχ` / `dχ²∣D` 入力をすべて外した。残る入力は
  member-family の character-theory data、common `idx` + p-power 残差 factorization、degree sort、sum identity、
  Schur-bound 側の p-power 比較、coprimality などの 6.6 本文由来 data。
- **2026-06-04 追記 7**: **`natDegree_pos_of_irreducibleCharacter_apply_one_eq`** /
  **`natDegreeSquareSum_pos_of_memberFamily`** を追加し、`primePowerSums` / `commonIndexPrimePowerSums`
  constructors から `hpos₁ : 0<d₁` と `hDpos : 0<D` を削除。さらに common-index 版の
  `hleχ : d₁≤dχ` は既存の strict gap `hlt : d₁<dχ` から内部導出する形にした。
- **2026-06-04 追記 8**: **`xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums`** を追加。
  caller が actual accumulator `pairUnion (xBaseBlock Z) pair i` の injective finite enumeration を渡せば、
  cover / non-real / conjugate-support / conjugate-membership / orthonormality を `Xset` facts と pairUnion
  closure から内部構成し、残入力を同じ enumeration 上の genuine (6.6) degree・p-power・sum・coprimality data
  だけにした。
- **2026-06-04 追記 9**: **`PairUnionCommonIndexPrimePowerStepData`** と
  **`Xset_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_irreducible_X`** を追加。chain-level の
  `hstep` callback は `XAdjoinStepInput` を直接返さず、actual pair-cover prefix ごとの common-index/p-power
  degree data package を返せばよくなった。adapter が各 step で `pairUnion` bookkeeping と arithmetic constructor
  を接続し、`Xset_isCoherent_from_adjoinSteps_of_irreducible_X` に fold する。
- **2026-06-04 追記 10**: **`natDegree_le_of_xBaseBlock_anchor`** /
  **`natDegree_lt_of_xBaseBlock_anchor_of_not_mem`** と
  **`xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums`** を追加。chosen anchor `χ₁` が
  minimal-degree base block にいることから prefix member 全体の `d₁≤dmem j` を導出し、current pair が
  prefix と disjoint であることから `χs i∉xBaseBlock Z`、従って `d₁<dχ` を内部化した。
- **2026-06-04 追記 11**: **`PairUnionBaseAnchorCommonIndexPrimePowerStepData`** と
  **`Xset_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_irreducible_X`** を追加。
  追記 10 の base-anchor step adapter を chain-level consumer に持ち上げ、per-step data package から
  `hlt : d₁<dχ` と `hlemem : ∀j, d₁≤dmem j` を削除。caller は actual pair-cover prefix の enumeration,
  base-block anchor, common-index/p-power/sum/coprimality data を渡せば、chain fold が `X` coherence
  まで進む。
- **2026-06-05 追記 13**: **`two_mul_lt_sq_of_commonIndex_primePower_gap`** と
  S08 側の **`realDegreeBound_of_natDegreeSumCommonIndexPrimePowerGap`** /
  **`normalizedDegreeGap_of_natDegreeSumCommonIndexPrimePowerGap`** /
  **`xAdjoinStepInput_of_memberFamily_degreeDivisibility_commonIndexNatGap`** を追加。common `idx`
  + p-power residual factorizations + `d₁ < dχ` から直接 degree gap を作るため、common-index
  constructor/`PairUnion*CommonIndexPrimePowerStepData` から quotient data
  `q`, `m`, `q = p^m`, `dχ = q*d₁` を削除した。これで §6.6 step data は別途 ratio を命名せず、
  character degree factorizations・degree sort・sum/coprimality data だけを渡せばよい。

- **2026-06-04 追記 12**: **`sq_dvd_natDegreeSquareSum_of_commonIndex`** を追加し、common-index
  member factorizations `dmem j = idx·θmem j` と prefix square-sum identity `∑ dmem(j)^2 = D` から
  `idx²∣D` を内部導出。これにより `xAdjoinStepInput_of_memberFamily_commonIndexPrimePowerSums`,
  `xAdjoinStepInput_of_pairUnion_commonIndexPrimePowerSums`, base-anchor 版, および両 `PairUnion*StepData`
  から caller-supplied `hidx_D` を削除した。低層 `degreeDivisibility_primePowerSums` は `hdmem` を持たないため、
  common-index adapter 内で局所 witness としてのみ `hidx_D` を作って渡す。
- **2026-06-04 追記 13**: actual `Fin k` prefix 版の common-index adapters と両 `PairUnion*StepData`
  から `D` / `hDsum` を削除。prefix square sum は `Dprefix := ∑ j : Fin k, dmem j*dmem j` として
  adapter 内で定義し、generic member-family adapter へ `hDsum` を局所 `simp` witness として渡す。
  caller 側の sum data は `D + tail = total` ではなく、直接
  `(∑ j : Fin k, dmem j*dmem j) + tail = total` を渡す形になり、actual prefix enumeration から
  自明に決まる `D` witness を保持しなくてよくなった。
- **2026-06-04 T6 guard**: T6/Y-family 側の S08 landed bricks を AxiomsCheck に登録。
  `induce_apply_one_eq_card_W1_of_degree_one`, degree-one induced difference support,
  `coherentInducedDegreeOneFamily`, `inertia_eq_H_of_c2`, `inertia_eq_H_of_c2_caseA`,
  `isIrreducibleCharacter_induce_of_degree_one`, `coherentYFamily`, Frobenius/case-A Xset
  irreducibilityがいずれも 3 axiom allowlist 内。これで c2 inertia discharge と Y-family coherence
  engine call は CI guard 下に入り、残る T6 は `Yset = S(H')` との exact family/range wiring。
- **2026-06-04 T6 adapter**: **`coherentYFamily_of_pairwiseNonconj`** を追加。
  caller は nontrivial linear source family と pairwise non-`L`-conjugacy だけを渡し、
  各 `Ind_H^L θ_j` の既約性は T6/c1-c2 brick
  `isIrreducibleCharacter_induce_of_degree_one` で adapter 内部に discharge する。AxiomsCheck
  にも登録済みで、残る T6 exact wiring は `Yset = S(H')` の enumeration/range 同一視。
- **2026-06-04 T6 Yset bridge**: **`induce_linearIrreducibleCharacter_mem_Yset`** と
  **`range_induce_linearIrreducibleCharacter_subset_Yset`** を追加。nontrivial linear source
  `χ : H →* ℂˣ` について `Ind_H^L(linear χ) ∈ Yset = S(H')` を、`linear χ` が commutator
  subgroup を殺すことから直接証明する。これで constructed Y-family の range は `Yset` に入る。
- **2026-06-04 T6 Yset reverse bridge**: **`exists_linear_source_of_mem_Yset`** と
  **`mem_Yset_iff_exists_linear_source`** を追加。`Yset` witness の source `θ` を
  `Abelianization.of : H → H/H'` で factor し、finite commutative group の irreducible character
  が degree-one/linear であることから、任意の `Yset` member を nontrivial linear source の
  induced character として表す。
- **2026-06-04 T6 exact range adapter**:
  **`range_induce_linearIrreducibleCharacter_eq_Yset_of_induce_surjective`** と
  **`coherentYset_of_pairwiseNonconj`** を追加。caller が `Fin n` で nontrivial linear
  characters の induced `Yset` members を覆う orbit representatives を列挙し、その cover と
  pairwise non-`L`-conjugacy を渡せば、constructed equal-degree family の coherence を
  `hyp.Yset` へそのまま rewrite できる。残る T6 wiring は concrete representative
  construction とその cover/pairwise 入力の構成。
- **2026-06-04 追記 14**: **`commonIndex_pos_of_natDegree_factor`** を追加し、common-index
  adapters と両 `PairUnion*StepData` から caller-supplied `hidxpos : 0 < idx` を削除した。
  `idx > 0` は current character の自然次数正性と factorization `dχ = idx*θχ` から adapter 内で
  局所導出されるため、§6.6 caller は fixed induction index の positivity witness を別途保持しなくてよい。
- **2026-06-04 追記 15**: **`coprime_commonIndex_primePower`** を追加し、common-index
  adapters と両 `PairUnion*StepData` から caller-supplied `hcop : Nat.Coprime idx θχ` を削除した。
  caller は §6.6 / (6.4.c) に対応する `hidx_p : Nat.Coprime idx p` だけを渡し、各 step の
  residual degree `θχ = p^mχ` から adapter 内で `Nat.Coprime idx θχ` を局所導出する。
- **(6.6) 잔여 (leaf-2 이후)**: 이 producer들의 *입력* divisibility 생산 — sum identity
  `∑_{j<i}+∑_{j≥i}=|L|-|L:Z|` (column-orthogonality character theory), `θᵢ(1)²∣∑_{j≥i}`
  (`Finset.dvd_sum`+`pow_dvd_pow`), `θᵢ(1)²≤|K:Z|` ([Is] Cor 2.30), `(|L:K|,p)=1` ((6.4.c)) — + degree
  sort + base prefix coherence ((1.1)/(1.4)). 상세는 issue 0046 pass-2 leaf 2.

### (2026-05-31, G2.0) (6.6) opening "By (1.1), n ≥ 2" (mmd L76)

(6.6) 증명의 *첫* 단계 "Let `n=|X|`. By (1.1), `n ≥ 2`"를 `S07_Coherence.lean` ((6.6) section의
`pairSet` def 직전)에 landing (sorry/axiom 無 — AxiomsCheck 등록 1건 3 axiom 全 allowlist; full
`lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3351/3334 jobs):

- **`two_le_ncard_of_conjugate_closed_of_noReal`**: `X : Set (ClassFunction L ℂ)`가 finite +
  nonempty + `ClosedUnderConjugate` + `HasNoRealCharacters` ⟹ `2 ≤ X.ncard`. mmd L76의 정직한
  일반형 — (1.1)이 공급하는 두 사실 [conjugation 폐쇄 (`χ∈X ⟹ χ̄∈X`; `Z` normal로 `Ker χ̄=Ker χ`),
  non-self-conjugate (`χ̄ ≠ χ`; `|L|` odd & nontrivial)]가 nonempty와 결합해 `χ`, `χ̄` 두 distinct
  member를 주어 `1 < X.ncard` (`Set.one_lt_ncard`) → `2 ≤ X.ncard` (`omega`). 사실 `|X|`은 even이나
  (6.6)은 `≥ 2`만 사용 (= `Z[X,L^#] ≠ 0` 보증 + (1.4) prefix 시작).
- **honest 판정**: thin wrapper 아님 — `Set.one_lt_ncard`는 bridge일 뿐, 내용은 conjugation
  involution으로부터 distinct witness `χ̄ ≠ χ`를 *구성*하는 부분. 두 가설은 §7 `Hypothesis` 필드
  (`conjugate_closed`/`no_real_characters`)이고 `X ⊆ S`로 상속 (`HasNoRealCharacters.mono`;
  `ClosedUnderConjugate`는 caller가 `S(Z)` conj-폐쇄성과 함께 공급) — posited 아님.
- **caller 측 잔여 (G2.0 이후)**: (6.6) 본문이 instantiate하려면 `X = S − S(Z)`의 nonemptiness
  (`Z ≠ 1` ⟹ `Z ⊄ Ker χ`인 irreducible 존재) + `S(Z)` conj-폐쇄성 (→ `X` conj-폐쇄)을 공급해야
  함 — §6 setup-specific character theory의 별도 leaf. 상세는 issue 0046 G2.0.

### (2026-05-31, G2.1) (6.6) opening "Set X = {χ₁,…,χₙ} where χ₁(1) ≤ ⋯ ≤ χₙ(1)" (mmd L76)

(6.6) 증명이 `n=|X|` 다음 곧바로 하는 **degree-sort** "Set `X = {χ₁,…,χₙ}`, where `χ₁(1) ≤ ⋯ ≤
χₙ(1)`"를 `S07_Coherence.lean` ((6.6) section, `two_le_ncard_…` 직전)에 landing (sorry/axiom 無 —
`#print axioms exists_monotoneDegreeEnum` = `[propext, Classical.choice, Quot.sound]`; AxiomsCheck
등록 1건 全 allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑):

- **`exists_monotoneDegreeEnum`**: `X : Set (ClassFunction L ℂ)` finite ⟹ `∃ e : Fin X.ncard →
  ClassFunction L ℂ`, `e` injective + `∀ i, e i ∈ X` + `∀ χ∈X, ∃ i, e i = χ` (range = X) + real
  degree key `χ ↦ (characterDegree χ).re` 따라 monotone (`i ≤ j ⟹ (deg (e i)).re ≤ (deg (e j)).re`).
  구성: 유한성 → `Fintype.equivFinOfCardEq` 로 `g : X ≃ Fin n` (`n = X.ncard`, bridge `Fintype.card
  = Nat.card = ncard`), key `k i := (deg (g.symm i)).re`, `σ := Tuple.sort k`, `e i := g.symm (σ i)`.
  injective = `Subtype.val ∘ g.symm ∘ σ` 세 합성; surjective = `i = σ⁻¹(g⟨χ,_⟩)`; monotone =
  `Tuple.monotone_sort k` (`k ∘ σ` monotone, 그리고 `(deg (e i)).re = (k∘σ) i` 정의적).
- **honest 판정**: thin wrapper 아님 — `Tuple.sort`/`Tuple.monotone_sort`만으로는 *set*의 monotone
  enumeration이 안 나옴 (set → 임의 `Fin n ≃ X` 선택 + key pull-back + injective/surjective/range 재조립
  필요). 순수 order-이론적 "finite family를 real key로 sort" 단계로, irreducibility/induced-from-K/p-power
  degree 사실 전혀 사용 안 함 — 임의 finite class-function set에 대해 일반형으로 statement.
- **caller 측 잔여 (G2.1 이후)**: 이 enumeration을 `coherentPairChain`의 `pair : ℕ → χ×χ̄`와 base
  prefix `{χ₁,…,χₖ}` (equal-minimal-degree, (1.1)+(1.4) coherent)로 연결 + per-step (5.6) data 생산
  (θᵢ(1)=p-power, [Is] Cor 2.30, `χᵢ(1)² ∣ ∑_{j<i}χⱼ(1)²` → `two_mul_lt_sq_of_primePow_gap`).
  enumeration 자체는 `Fin n` 인덱스 monotone; pair-인덱스(`ℕ`)로의 캐스팅·base 분리는 별도 leaf.

### (2026-05-31, G2.3) (6.6) "For all j, θⱼ(1) is a power of p" (mmd L80)

(6.6) 証明 L80 の degree datum「`K` が `p`-群なら各 `θ ∈ Irr K` の `θ(1)` は `p` の冪」を **2 層**で
landing (sorry/axiom 無 — `#assert_only_allowed_axioms` 各 3 axiom 全 allowlist, no `sorryAx`; full
`lake build OddOrder`/`OddOrder.AxiomsCheck` 緑):

- **`IsIrreducibleCharacter.exists_charValue_one_eq_prime_pow_of_isPGroup`** (`ZIrr.lean` の `Degree`
  section, `exists_natDegree_charValue_one_dvd_card` 直後): `[Finite G]`, `[Fact p.Prime]`,
  `IsPGroup p G`, `IsIrreducibleCharacter φ` ⟹ `∃ k, φ 1 = (p^k : ℂ)`。既存
  `exists_natDegree_charValue_one_dvd_card` (`φ 1 ∣ |G|` のみ) を、より鋭い
  `exists_finrank_eq_prime_pow_of_isPGroup` (証言表現の `dim V = p^k`) + `char_one` (`φ 1 = dim V`)
  で精密化。証明は `exists_natDegree_charValue_one_dvd_card` を mirror し `finrank_dvd_card` の代わりに
  p-群版を呼ぶだけ (~12 LOC)。
- **`exists_characterDegree_eq_prime_pow_of_isPGroup`** (`S03_PreliminaryCharacter.lean`,
  `exists_natDegree_characterDegree_dvd_card` 直後): `IrreducibleCharacter G` subtype + `characterDegree`
  経由で `∃ k, characterDegree χ = (p^k:ℂ)`。`characterDegree_def` rewrite で RT 形を
  bundled-character API に橋渡し (既存 `dvd_card` 版と同一の二層パターン = predicate→subtype +
  `φ 1`→`characterDegree` の convention 適応)。これが (6.6) 本文が消費する形。
- **2026-06-04 追記**: **`exists_natDegree_characterDegree_eq_prime_pow_of_isPGroup`** を追加。
  `∃ d k, 0<d ∧ characterDegree χ = (d:ℂ) ∧ d=p^k` という同一 witness 版で、S08 の
  natural-degree witness と prime-power gap data を直接接続する。
- **依存 verify**: (6.5.b) の "`K` 非可換 `p`-群" は本 leaf では `IsPGroup p K` を**引数**で受ける
  (honest fully-general; `p`-群結論を posit せず、それを供給する (6.5) は別 leaf)。消費 landed lemma
  `exists_finrank_eq_prime_pow_of_isPGroup` は `ClassSumAlgebra.lean:1564` に既存・AxiomsCheck 済 — 確認済。
- **honest 판정**: thin wrapper 아님 — 既存 `dvd_card` lemma 들은 `θ(1) ∣ |G|` 밖에 안 주므로
  p-power 결론을 *재진술*이 아니라 더 강한 primitive (`exists_finrank_eq_prime_pow_of_isPGroup`)에서
  새로 끌어옴. 二層 (RT predicate 형 + Peterfalvi `characterDegree`/subtype consumer 형)은 repo의
  기존 `dvd_card` 쌍과 동일한 확립된 패턴.

### (2026-05-31, G2.2) (6.6) coherence-of-X equality residual: 真正 character の ℕ-分解

(6.6) の coherence-of-X equality case (Round-19 residual) が end-to-end で消費する
**「真正 character は非負整数係数で irreducible に分解する」**を honest 一般形で
`OddOrder/GroupTheory/RepresentationTheory/Clifford.lean` (+ `IsCharacter` 述語を `ZIrr.lean`)
に landing (sorry/axiom 無 — `#print axioms` = {propext, Classical.choice, Quot.sound}; AxiomsCheck
登録 4 件 各 3 axiom 全 allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3360/3343 jobs):

- **`IsCharacter`** (`ZIrr.lean`, `IsIrreducibleCharacter` の隣に新設): `φ : ClassFunction G ℂ` が
  **有限次元 ℂ-表現 `ρ` の character** (= `(φ : G→ℂ) = ρ.character`, irreducibility を落とした版)。
  `IsIrreducibleCharacter.isCharacter` (irreducible ⟹ genuine) /
  `repCharacterClassFunction_isCharacter` で導入。virtual character (`ZIrr` の任意 ℤ-結合) と区別される
  「実モジュールの character」の述語。
- **`IsCharacter.mem_ZIrr`**: 真正 character ∈ ZIrr (`character_mem_ZIrr` を canonical class-function
  同定後に適用; `[Finite G]` のみ要)。
- **`IsCharacter.exists_natCast_inner_irreducible`** (非負性の核): 真正 `χ=χ_ρ`・irreducible `ψ=χ_σ` で
  `⟨χ,ψ⟩ = dim_ℂ Hom_{ℂ[G]}(σ,ρ)` (cast ℕ)。これは Clifford `restrictionMultiplicity_nonneg`
  (H-level の `⟨Res^G_H χ,θ⟩ ≥ 0`) の **G-level 版**: `inner χ ψ = ⅟|G| · ∑_g χ(g)·star(ψ g)` を
  `star(χ_σ g)=χ_σ(g⁻¹)` (`character_inv`) で書き換え, mathlib の
  `Representation.card_inv_mul_sum_char_mul_char_eq_finrank` (character scalar product = Hom-dim) に
  `σ ρ` swap で流す。`inner_irreducible_nonneg` は `0 ≤ ⟨χ,ψ⟩` の即系。
- **`IsCharacter.exists_natFinsupp_eq_sum`** (= GOAL, G2.2 が食う形): `∃ m : ClassFunction G ℂ →₀ ℕ`,
  `supp m ⊆ Irr(G)`, `χ = ∑_{ψ∈supp m} (m ψ:ℂ)•ψ`, かつ `∀ψ∈Irr, (m ψ:ℂ)=⟨χ,ψ⟩`。証明:
  `mem_ZIrr_repr` で `χ` の ℤ-Finsupp 分解 `c` を取り, `inner_eq_coeff_of_repr` で各係数 `c ψ = ⟨χ,ψ⟩`,
  これが genuine character で `≥ 0` (`inner_irreducible_nonneg`), `Finsupp.mapRange Int.toNat` で ℕ 化
  (support 不変: support 上の係数は正なので `Int.toNat` で値も support も保存)。Peterfalvi の
  "χ = ∑ mᵢψᵢ with mᵢ = ⟨χ,ψᵢ⟩ ∈ ℕ".
- **honest 판정**: thin wrapper 아님 — `IsCharacter` 는 genuine vs virtual character 의 진짜 새 述語;
  비음성은 `restrictionMultiplicity_nonneg` (H-level) 가 안 주는 G-level Hom-dim 을 새로 끌어옴;
  ℕ-Finsupp 分解은 ℤ-repr + 비음성 + `Int.toNat` support-preservation 의 비자명한 합성.
- **배치 (import closure 判断)**: `Clifford.lean` 가 `character_mem_ZIrr` (CharacterCompleteness) +
  Fourier (`mem_ZIrr_repr`/`inner_eq_coeff_of_repr`, ZIrrFourier) + `character_inv` (CharacterConjugate)
  를 모두 import closure 에 가지는 유일 모듈이며, 概念的으로도 `restrictionMultiplicity_natCast`
  (Clifford 多重度 비음성) 와 同族. `IsCharacter` 述語만 `ZIrr.lean` (其 `.mem_ZIrr` 는 downstream
  `character_mem_ZIrr` 필요 ⟹ Clifford 에 둠).
- **(6.6) 残作業 (G2.2 後)**: この ℕ-分解 leaf 자체는 G2.2 의 character-side primitive 로 완결.
  (6.6) main 의 残 = pass-8/pass-2 의 `coherentPairChain` `hstep`/`h0` 입력 (degree sort →
  per-step (5.6) data: θᵢ(1)=p-power, [Is] Cor 2.30, `χᵢ(1)²∣∑_{j<i}`) + base prefix coherence
  ((1.1)/(1.4)) — character-theory/구조정수 작업으로 별도.

### (2026-05-31, G2.6 WIRING) (6.6) coherence-of-X 결론 `IsCoherent τ X A` 의 조립

(6.6) 증명의 결론 "Repeated use of Theorem (5.6) then shows that X is coherent" (mmd L84) 을, landed
leaves (G2.1 degree-sort `exists_monotoneDegreeEnum`, pass-8 `coherentPairChain` 엔진, pass-2 gap leaf
`two_mul_lt_sq_of_primePow_gap`, G2.5 degree-sum `sumInflatedDegreeSq`) 위에 honest 하게 조립하는
**wiring 정리** 를 `S07_Coherence.lean` ((6.6) section 의 `coherentPairChain` 직후) 에 landing
(sorry/axiom 無 — `#print axioms coherentOfPairChainCover` = {propext, Classical.choice, Quot.sound};
AxiomsCheck 등록 3건 각 3 axiom 全 allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑
3360/3343 jobs):

- **`mem_pairUnion`** (membership 특성화): `χ ∈ pairUnion S₀ pair N ↔ χ ∈ S₀ ∨ ∃ j<N, χ ∈ pairSet pair j`.
  `N` induction. engine accumulator 의 멤버십 결정.
- **`pairUnion_eq_of_cover`** (set-decomposition bridge): `S₀ ⊆ X` + 각 pair ⊆ X + `X` cover ⟹
  `pairUnion S₀ pair N = X`. = degree-monotone enum (`exists_monotoneDegreeEnum`) 이 `X = S − S(Z)`
  를 equal-min-degree prefix `S₀` 와 나머지 conjugate pair 들로 쪼갠 것을 engine accumulator
  `pairUnion S₀ pair N` 와 동일시하는 다리. **본 round 의 핵심 신규 content** (`coherentPairChain` 미제공).
- **`coherentOfPairChainCover`** (`noncomputable def`, = G2.6 GOAL): pair-chain decomposition data +
  base coherence `h0 : IsCoherent τ S₀ A` ((1.1)+(1.4) prefix) + per-step (5.6) adjoining `hstep` ⟹
  `IsCoherent τ X A`. 증명 = `pairUnion_eq_of_cover … ▸ coherentPairChain S₀ pair h0 N hstep`.
- **honest 판정**: thin wrapper 아님 — `coherentPairChain` 은 `IsCoherent (pairUnion S₀ pair N) A` 만
  주고, 본 정리는 set-decomposition bridge 를 추가해 **(6.6) 의 실제 결론 `IsCoherent τ X A`** 산출;
  `h0`/`hstep` 은 (6.6) 증명구조의 *공급* 입력, 결론은 chain 으로 derived (posit 無). instruction 이
  명시 허용한 wiring boundary 까지만 landing.
- **정밀 잔존 (G2.7)**: `hstep` 각 step 의 `retarget_isCoherent` 입력 중 **target characters
  `{Xᵢ, X̄ᵢ}` + image equation + lattice 직교** 의 *구성* = **Dade isometry ν basis extension** 미완
  (degree 부등식 부분은 이미 landed). + caller 의 decomposition data (`pair`/`N`/cover) 를 enum +
  conjugate-pairing 에서 구성하는 작업 (별도). 상세는 issue 0046 G2.6.

### (2026-05-31, G2.6 PASS 2) (6.6) named conclusion `peterfalvi_66_coherence_of_X` + enum-cover bridge

PASS 1 의 `coherentOfPairChainCover` (set-level cover `hcover` 를 opaque 가설로 받는 abstract assembler)
를 (6.6) 의 실제 증명구조 — degree-monotone enumeration (mmd L76 "Set X = {χ₁,…,χₙ}, χ₁(1) ≤ ⋯ ≤
χₙ(1)") 를 `coherentPairChain` accumulator 에 threading — 으로 끌어올려 **named (6.6) 결론**을 landing
(`S07_Coherence.lean`, `coherentOfPairChainCover` 직후; sorry/axiom 無 —
`#print axioms peterfalvi_66_coherence_of_X` = {propext, Classical.choice, Quot.sound}; AxiomsCheck
등록 2건 각 3 axiom 全 allowlist; full `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3360/3343 jobs):

- **`pairUnion_eq_of_enumCover`** (genuinely new bridge): enum `e : Fin n → ClassFunction L ℂ` 의
  *surjectivity* `hsurj : ∀ χ∈X, ∃ i, e i=χ` + **index-level** cover `hcoverIdx : ∀ i, e i ∈ S₀ ∨
  ∃ j<N, e i ∈ pairSet pair j` ⟹ `pairUnion S₀ pair N = X`. `pairUnion_eq_of_cover` 의 set-level
  cover 를 χ=e i 치환으로 index-level 에서 도출 — `exists_monotoneDegreeEnum` 가 `Fin n` 인덱스로
  주는 사실들과 engine 의 set-level cover 사이의 connective tissue (PASS 1 note 의 residual
  "threading the enum sort into the accumulator").
- **`peterfalvi_66_coherence_of_X`** (`noncomputable def`, = G2.6 GOAL): enum `e`/`hsurj` (mmd L76
  opening) + pair-chain decomposition (`S₀`/`pair`/`N`/`hS₀`/`hpairs` + index-cover `hcoverIdx`) +
  base prefix coherence `h0` ((1.1)+(1.4)) + per-step (5.6) adjoining `hstep` (`retarget_isCoherent`)
  ⟹ `IsCoherent τ X A` (mmd L84 "Repeated use of (5.6) shows X is coherent"). proof =
  `pairUnion_eq_of_enumCover hsurj … ▸ coherentPairChain S₀ pair h0 N hstep`. `hXfin` 는 (6.6) X
  유한성 (enum 존재 정당화).
- **honest 판정**: thin wrapper 아님 — `coherentOfPairChainCover` 보다 (a) (6.6) named 결론을 textbook
  altitude statement 로 제시, (b) `exists_monotoneDegreeEnum` 을 surjectivity 경유로 engine 에 연결
  (set-level cover → index-level `hcoverIdx`). `h0`/`hstep`/decomposition 은 *공급* 데이터, 결론은
  chain 으로 derived (posit 無).
- **정밀 잔존 (G2.7, 불변)**: `hstep` 각 step 의 `retarget_isCoherent` 입력 중 **`{Xᵢ, X̄ᵢ}` target +
  image equation + lattice 직교** 의 *구성* = **Dade isometry ν basis extension** (orthonormal set 의
  ℤ-linear independence ⟹ free-module basis extension, repo/mathlib 부재). + decomposition data 를
  enum + conjugate-pairing 에서 구성하는 작업 (conjugation-closed set 의 canonical pairing, 별도 leaf).
  degree-inequality 측은 이미 landed (`two_mul_lt_sq_of_primePow_gap`/`sumInflatedDegreeSq`).

## §8 全結果表

| # | mmd 行 | 種別 | Statement 概要 | 数学的意義 | 形式化難度 | §9-§16 被引用 |
|---|--------|------|----------------------|-----------|-----------|-----------|
| **(6.1)** | 3-5 | **Hypothesis** | K solvable, S = Ind_K^L(Irr K - 1), S(A) filtration | Coherence 応用の基盤セットアップ | low | 全結果の前提 |
| **(6.2)** | 7-22 | **Lemma** | Coherence 喪失判定: 2\|L:C\|\sqrt{\|C:D\|} ≥ \|K:A\|-1 | Coherence 不成立による矛盾導出の技法 | **high** (長計算) | (6.3), (6.5), 構造分析で頻出 |
| **(6.3)** | 24-48 | **Theorem** | nilpotent 商 H/M での coherence 伝播 | 下降補題: coherence が層状に保存 | **high** (5 段階矛盾導出) | (6.4), (6.5), (6.8) 依存 |
| **(6.4)** | 50-73 | **Hypothesis + (6.5)-(6.6)** | |L| odd, K/M nilpotent, Frobenius 構造 → K/M は p-群で特定 | **奇数位数下での特殊化** (Sibley 系) | mid | (6.6), (6.8) 直前提 |
| **(6.7)** | 87-135 | **Theorem** | P Sylow p, L=N_G(P), P^# TI → character class 関係式 | **Galois 作用下の character 整数性** (Reynolds 1965 関連) | **very high** (7 つの sub-lemmas) | (6.8) 依存, (6.7.1)-(6.7.3) sub-structure |
| **(6.8)** | 136-244 | **Main Theorem** | L = H ⋊ W_1, H^# TI, Frobenius or Dade cond. → S coherent | **Frobenius family の coherence 統合定理** | **very high** (6.8.1)-(6.8.3, 8 sub-parts) | §9, §10-§14 の最重要入口 |

## 各結果の詳細

### (6.1) Hypothesis — Coherence 応用の枠組み

**主張**:
- (a) Hypothesis (ref:eq:C) が成立 (= §7 Coherence の前提 (5.2))
- (b) K は L の可解正規部分群
- (c) S = {Ind_K^L θ | θ ∈ Irr K, θ ≠ 1_K} (K からの導入指標集合)
- (d) A ⊂ K が L の正規部分群なら S(A) = {Ind_K^L θ | A ⊂ Ker θ, θ ≠ 1_K}

**数学的意義**:
- K が可解正規部分群という点が重要 ⟹ K/A も可解 ⟹ K/A は線形指標を持つ
- 導入指標集 S の "filtration by kernel" S(A) を考える = 正規部分群の階層構造を character level で追跡

**Lean 表現**:
```lean
structure CoherenceHypothesis (G L K : Type*) [Group G] [Group L] [Group K] 
    (hyp_C : Hypothesis (5.2) L G) where
  K_solvable : IsSolvable K
  K_normal : K ◁ L
  S : Set (Representation ℂ L)  -- = Ind_K^L (Irr K - 1_K)
  S_A : (A : Subgroup K) → A ◁ L → Set (Representation ℂ L)  -- filtration
```

### (6.2) Lemma — Coherence 喪失の数値的判定

**主張**: Hypothesis (ref:eq:C) 下で、

- (a) A ⊂ K (A ≠ ∅), B ⊂ D ⊂ C ⊂ K, D/B ⊂ Z(C/B) (正規化群条件)
- (b) S(A) は coherent だが S(B) は NOT coherent

なら **2|L:C|√|C:D| ≥ |K:A|-1**

**証明概要** (mmd L14-22):
1. Hypothesis (ref:eq:C.b) より ∃ S_1, S_2 (S_1 closed under conj, S_1 coherent, S_1 ∪ S_2 NOT coherent)
2. K solvable ⟹ K/A は線形指標を持つ ⟹ S(A) の一員は degree |L:K|
3. **Theorem (5.6)** (§7 Coherence 拡張定理) 適用 ⟹ 2ψ(1)|L:K| ≥ Σ χ(1)²/‖χ‖²
4. (ref:eq:C.c), (ref:eq:C.d) より Σ χ∈S(A) χ(1)²/‖χ‖² = |L:K|(|K:A|-1)
5. θ(1) ≤ |K:C|√|C:D| (by (ref:eq:C)) ⟹ ψ(1) = Ind_K^L θ(1) ≤ |L:C|√|C:D| ⟹ 完成

**形式化の難所**:
- 多重的な sum/product 計算 (∑ χ∈S(A) χ(1)²/‖χ‖²)
- induced character の degree 推定 (最後の不等式)
- (ref:eq:C.b)-(ref:eq:C.d) の各条件の局所適用

**役割**: (6.3)-(6.5) での矛盾導出に直結

### (6.3) Theorem — Nilpotent 商での Coherence 伝播

**主張**: Hypothesis (ref:eq:C) 下で、M ⊂ H_1 ⊂ H ⊂ K (全て L の正規部分群) かつ

- (a) H/M が nilpotent
- (b) S(H_1) は coherent
- (c) |H:H_1| > 4|L:K|² + 1

なら **S(M) is coherent** (M での filtration も coherent)

**証明概要** (mmd L24-48):
1. Minimal counterexample: A ⊃ M, A ⊂ H_1, S(A) coherent, A minimal with these properties
2. A ≠ M と仮定 (矛盾を狙う)
3. B を M ⊂ B ⊂ A, B maximal で選ぶ
4. H/M nilpotent ⟹ (A/B) ∩ Z(H/B) ≠ 1 ⟹ A/B ⊂ Z(H/B)
5. **(6.2) を C=H, D=A で適用** ⟹ 2|L:H|√|H:A| ≥ |K:A|-1
6. x = |H:A| で変形: (√x - 1/√x)² = x - 2 + 1/x ≤ 4|L:K|²
7. |H:H_1| > 4|L:K|² + 1 に矛盾

**数学的意義**:
- **下降補題 (Descent Lemma)**: coherence が層状に保存される
- K の分層構造を利用して、上から下へ coherence を伝播させる
- (6.4)-(6.5)-(6.6) での Frobenius + odd-order 特殊化の前提

**Lean 表現**: 矛盾導出が複雑 — `decide` で不等式評価をサポート要

### (6.4) Hypothesis + (6.5)-(6.6) — 奇数位数下での特殊化

⚠️ audit 訂正: 旧 section 見出し「(Sibley 系)」は誤帰属. (6.3) と (6.5) は **[FT] §11** から (Peterfalvi Notes §SS6 明示). Sibley の寄与は **(6.8) のみ**.

#### (6.4) Setup

**主張**:
- (a) Hypothesis (6.1) + |L| odd
- (b) M ⊂ K, K/M nilpotent
- (c) H_1/M = [K/M, K/M] (commutator subgroup)
- (d) L/H_1 は kernel K/H_1 を持つ Frobenius 群

#### (6.5) Lemma — K/M の構造決定

Hypothesis (6.4) + S(M) NOT coherent なら:

- **(a)** K/H_1 は L の chief factor で |K:H_1| ≤ 4|L:K|² + 1
- **(b)** ∃ prime p s.t. K/M is non-abelian p-group
- **(c)** |L:K| ∤ (p-1) (p-1 を割らない)

**証明**:
1. (6.3) の仮説 H=K で K/H_1 abelian & non-trivial ⟹ (6.3.b) holds
2. (6.3) 適用 ⟹ |K:H_1| ≤ 4|L:K|² + 1
3. K solvable & commutator [K,K]=H_1 ⟹ K/M is p-group for some p
4. (c) proof by contrapositive: |L:K| | (p-1) ⟹ p ≥ 2|L:K|+1 ⟹ |K:H_1| ≥ p² > 4|L:K|²+1 矛盾

**数学的意義** ⚠️ audit 訂正 (旧記載「Sibley 1984 の翻訳」は **完全誤帰属**):
- (6.5) は **[FT] §11** (Feit-Thompson 1963 原論文) からの character-theoretic 引き取り
- Sibley とは無関係 ((6.8) のみが [Si1] Sibley 1976 *Illinois J. Math.* 20)
- K/M が p-group かつ non-abelian
- commutator K/H_1 が chief factor (Frobenius 構造の key)
- |L:K| coprime to (p-1) — [FT] §11 の signature condition

#### (6.6) Lemma — Center での Coherence

Hypothesis (6.4) + M=1 + Z ⊂ Z(K) non-trivial, X = S - S(Z) ⊂ Irr L なら:

**X = {χ ∈ Irr L | Z ⊄ Ker χ} and X is coherent**

**証明** (mmd L76-84): **複雑, 8 段階**
1. n = |X| ≥ 2
2. X の elements を degree で sort: χ_1(1) ≤ ⋯ ≤ χ_n(1)
3. χ_i = Ind_K^L θ_i, θ_i(1) = power of p (K/M は p-group)
4. θ_i(1)² | Σ_{j≥i} χ_j(1)²
5. Σ_{j≥i} χ_j(1)² = |L| - |L:Z| - Σ_{j<i} χ_j(1)²
6. **[Is] Corollary 2.30**: θ_i(1)² ≤ |K:Z|
7. Σ_j<i χ_j(1)² divisibility + **Theorem (5.6)** の繰り返し適用 ⟹ X is coherent

**役割**: (6.7)-(6.8) へ向けた coherence の final composition

### (6.7) Theorem — Character Class 関係式 (無名 internal lemma)

⚠️ audit 訂正: 旧見出し「(Reynolds 1965 関連)」は **完全捏造**. Reynolds は Peterfalvi 参考文献 (04.18) + Notes (04.17) **両方に存在せず**. (6.7) は無名の internal lemma で (6.8) Sibley の前段補題.

**主張**: G 有限, p prime, P Sylow p-subgroup of G, L = N_G(P),
- |L| odd, P^# TI-subset of G
- Z ⊂ Z(P) non-trivial, |C_L(z)| independent of z ∈ Z^#
- ψ ∈ Irr G, ψ constant on Z^#

**結論**: z ∈ Z^# ⟹ ψ(z) ∈ ℤ かつ **ψ(z) ≡ ψ(1) (mod |P|)**

**証明概要** (mmd L88-135, 6 つの sub-lemmas):

**(6.7.1) Lemma**: P^# が Z^# × Z^# に fixed-point-free に作用 ⟹ TI 性

**(6.7.2) Lemma**: Algebra homomorphism ω: Z[G] → ℂ (via ψ) の class operation 下での structure

**(6.7.3) Lemma** (Main): z ∈ Z^# ⟹ ψ(z) ≡ ψ(1) (mod |P|)
- Proof: ℤ[G] の conjugacy class algebra の construction
- z, z^{-1} が distinct conjugacy class (|L| odd ⟹ z^{-1} ≠ z^g)
- a_{11}, a_{12} calculation mod |P|
- integrality + congruence arithmetic

**数学的意義** ⚠️ audit 訂正 (旧「Reynolds 1965 定理」は捏造帰属):
- character class congruence: TI-subset + cyclic centralizer ⟹ character が "rigid" (mod |P|)
- (6.8) Sibley main thm の前準備
- proof 内で [Is] p.35 class-sum algebra hom `ω : ZC[G] → C` + algebraic integer congruence を使用 (両方 mathlib 不在; 新規 `OddOrder/RepresentationTheory/ClassSumAlgebraHom.lean` + `AlgInt.cong.lean` 要)

> **進捗 2026-05-30 (issue 1000 完了)**: class-sum algebra + central character `ω_ρ` の整数性を
> `OddOrder/GroupTheory/RepresentationTheory/ClassSumAlgebra.lean` に実装済 (unconditional, AxiomsCheck 登録).
> - `classSum_mul` : `C_i · C_j = ∑_s m_s · C_s` の **正しい** explicit 形 (係数 `m_s = (classSum Ci * classSum Cj) C_s.out`
>   = per-element 因子分解個数, 同一類上で定数; class-function 性は `classSum_mul_apply_conj`/`_out`).
>   read-only plan の `classSumCoeff/|C_s|` 形は誤りで採用せず (issue 注意書き通り).
> - `centralCharacterOfRep_classSum_mul` : `ω_ρ(C_i)·ω_ρ(C_j) = ∑_s m_s · ω_ρ(C_s)` (ℕ 係数; ω が ℂ-alg hom).
> - `centralCharacterOfRep_classSum_isIntegral` : **`IsIntegral ℤ (ω_ρ(C))`**. 行列固有値論法を回避し,
>   `{ω_ρ(C_s)}∪{1}` 生成の ℤ-部分加群 `N⊆ℂ` が乗法閉 (上記 product rule) かつ f.g. ⟹ `Submodule.toSubalgebra`
>   で部分代数化 ⟹ `IsIntegral.of_mem_of_fg`. これが (6.7.3) の `ψ(z)≡ψ(1) (mod |P|)` で使う integrality 部品.
> - 残: `AlgInt.cong` (合同 arithmetic in ℤ[ζ_n]) + a_{11}/a_{12} mod |P| の計算 = (6.7.3) 本体.

> **進捗 2026-05-30 (AlgInt.cong infra 完了)**: 合同関係 `α ≡ β (mod n)` を
> `OddOrder/Algebra/AlgInt.lean` に実装済 (unconditional, AxiomsCheck 登録).
> `Cong n α β := IsIntegral ℤ ((α - β)/n)` (Peterfalvi の三条件のうち load-bearing な商整数性;
> 端点整数性は別途 `character_isIntegral` 等で供給). API:
> - refl / symm / comm / trans / add / sub / neg = 加法的合同.
> - **`Cong.smul_left`/`smul_right`** : 片側を**任意の代数的整数で**スケール = (6.7.2)/(6.7.3) の
>   乗法ステップ (合同を ψ(1), 構造定数 a_{ij}, 別の整数 ω-値で掛ける). ⚠️ 2 つの合同の積
>   (`a≡b ∧ c≡d ⟹ ac≡bd`) は端点整数性を要し**無条件には成立しない**; 教科書も整数定数倍しかしないので一致.
> - `intMul_left`/`intMul_right`/`natMul_left` : 整数/ℕ スカラー特殊形.
> - `cong_of_exists_isIntegral`/`cong_of_sub_eq_intMul`/`Cong.of_int` : 導入形 (差を n×整数として提示).
> - notation `α ≡ β [ALGMOD n]` (scoped). commit dde7758.
> - **(6.7.3) 本体の残依存** (精密化): (1) **(6.7.1)** P が
>   `Ω = {(u,v) ∈ C_i × C_j | uv ∈ C_s}` (`C_s ∩ Z = ∅`) に fixed-point-free 作用 ⟹ `|P| ∣ a_{ijs}|C_s|`.
>   proof は **TI-subset ⟹ `C_G(x) ⊆ L` (x∈P^#)** + y∈{u,v} が L の p-元 ⟹ y∈P ⟹ (Z normal in L で) y∈Z ⟹ uv∈Z 矛盾.
>   これは `IsTISubset` + Sylow-in-L の group-theoretic 組み立て (~40-60 LOC, 未着手).
>   (2) **(6.7.2)** `ψ(1)α² ≡ ψ(1)(a_{ij0}+a_{ij}α) (mod |P|)`: `ω(C_i)ω(C_j)=∑ a_{ijs}ω(C_s)` (既存
>   `centralCharacterOfRep_classSum_mul`) に (6.7.1) を適用し `C_s∩Z=∅` 項を mod |P| で落とす.
>   (3) **(6.7.3)** assembly: |L| odd ⟹ z, z⁻¹ が異なる G-共役類 ⟹ a_{110}=0, a_{120}=|C_1|;
>   `ψ=1_G` で a_{11}≡1+a_{12} ⟹ (1+a_{12})ψ(z)≡ψ(1)+a_{12}ψ(z) ⟹ ψ(z)≡ψ(1). ⟸ ここで本 module の
>   `Cong.smul_left`/`add`/`trans` が直接効く. (1)(2)(3) は §6 group-theory 組み立てなので別 issue.

> **進捗 2026-05-30 ((6.7.1) orbit-counting half 完了)**: (6.7.1) の**数え上げ部分**を
> `OddOrder/GroupTheory/RepresentationTheory/ClassSumAlgebra.lean` に実装済 (unconditional, AxiomsCheck 登録).
> planner が CRITICAL と指摘した「集合上の作用の `|G| ∣ |Ω|`」欠落 primitive を埋めた:
> - `card_dvd_of_stabilizer_eq_bot` : 有限群 `Γ` の有限集合 `β` への**自由**作用 (全 stabilizer ⊥) ⟹ `|Γ| ∣ |β|`.
>   proof は free-action 分解 `β ≃ (β/Γ) × Γ` (mathlib `MulAction.selfEquivOrbitsQuotientProd`).
>   ⚠️ "fixed-point-free" は教科書文脈では **自由作用** (x≠1 が点を固定しない=全 stabilizer 自明) の意で,
>   mathlib の `IsPGroup.card_modEq_card_fixedPoints` (= `p ∣ |Ω|` しか出ない) では**不足**; 自由作用の
>   orbit-stabilizer 分解で初めて全 `|P| ∣ |Ω|` が出る (教科書の主張は `|P|` 整除であって `p` 整除ではない).
> - `card_dvd_of_no_nontrivial_fixed` : 等価な仮説形 (no `x≠1` fixes a point).
> - `classPairMulAction` : 部分群 `P` の `ClassPair = {q:G×G // IsClassPair Ci Cj Cs q}` (= Ω) 上共役作用.
> - `card_classPair` : `|Ω| = classSumCoeff Ci Cj Cs` (= a_{ijs}|C_s|).
> - **`card_dvd_classSumCoeff_of_fixedPointFree`** : fixed-point-free ⟹ `|P| ∣ a_{ijs}|C_s|` = (6.7.1) 結論.
> - **残**: fixed-point-free *仮説の検証* (TI ⟹ C_G(x)⊆L ⟹ y∈P ⟹ y∈Z ⟹ uv∈Z 矛盾) は Sylow/TI/Z setup
>   (`IsTISubset`+Sylow-in-L) を要し repo 未実装 = `needs-infra`. 揃えば (6.7.2)/(6.7.3) は本 module の
>   `centralCharacterOfRep_classSum_mul` + `card_dvd_classSumCoeff_of_fixedPointFree` + `AlgInt.Cong` で assembly.

> **進捗 2026-05-30 ((6.7.1) fixed-point-free 仮説検証 完了, commit 384e5b5)**: 上記「残」だった
> fixed-point-free *仮説の検証* を `ClassSumAlgebra.lean` に実装済 (unconditional, AxiomsCheck 登録).
> これで (6.7.1) の group-theory 部分が完全に閉じた:
> - **`mem_sylow_of_mem_normalizer_of_isPGroup`** : `N_G(P)` の p-元は Sylow p-部分群 `P` に属する
>   (P は N_G(P) で normal ⟹ unique Sylow p). proof は `P ⊔ ⟨u⟩` が p-群
>   (`IsPGroup.to_sup_of_normal_left'`; `⟨u⟩ ≤ N_G(P)`) + `Sylow.is_maximal'` で join が `P` に collapse.
>   ⚠️ `Z ≤ Z(P)` ではなく `Z ≤ P` のみ使用 (教科書の `Z ⊆ Z(P)` は強いが load-bearing なのは `Z ≤ P`).
> - **`fixedPointFree_classPair_of_isTISubset`** : (6.7) setup (P Sylow p in L=N_G(P), P^# TI-subset,
>   Z ≤ P normal in L; C_i,C_j が Z^# と交わり C_s∩Z=∅) で `P` が
>   `Ω = {(u,v)∈C_i×C_j | uv∈C_s}` に **fixed-point-free** 作用 (no `x∈P^#` が pair を固定).
>   - x∈P^# が (u,v) を固定 ⟹ x が u,v を中心化 ⟹ TI (`IsTISubset`, `y` が x を共役で動かさない
>     ⟹ y conjugates `x∈P^#` to `x∈P^#` ⟹ y∈L) で `C_G(x) ⊆ L`.
>   - u,v は p-元 (Z^#∩C_i 経由で `z∈Z≤P` (p-群) に G-共役; `SemiconjBy.orderOf_eq` で order 保存)
>     ⟹ 上記 `mem_sylow_…` で u,v∈P.
>   - 同じ共役が u (resp. v) を `c⁻¹` で `Z^#⊆P^#` に送る ⟹ TI で conjugator∈L ⟹ `Z⊴L` で u,v∈Z
>     ⟹ uv∈Z, `C_s∩Z=∅` に矛盾.
> - **assembly 可能**: `card_dvd_classSumCoeff_of_fixedPointFree` と合成して (6.7.1) 結論
>   `|P| ∣ a_{ijs}|C_s|` (C_s∩Z=∅) が完全形で出る. 残は (6.7.2) `ψ(1)α²≡ψ(1)(a_{ij0}+a_{ij}α)`
>   (本 module `centralCharacterOfRep_classSum_mul` + (6.7.1) で C_s∩Z=∅ 項を mod|P| 落とす) と
>   (6.7.3) assembly (|L| odd ⟹ z,z⁻¹ 異 G-共役類; `Cong.smul_left`/`add`/`trans`). これらは §6
>   class-algebra/合同算術の組み立てで group-theory 依存は解消済.

> **進捗 2026-05-30 ((6.7.2) product rule mod |P| 完了, commit 3735af4)**: (6.7.1) keystone
> (`card_dvd_classSumCoeff_of_fixedPointFree`) を product rule に流して (6.7.2) を `ClassSumAlgebra.lean`
> に実装済 (AxiomsCheck 登録). `import OddOrder.Algebra.AlgInt` 追加, `CharacterValuesIntegral` section を
> `ClassCongruence` section の前へ移動 (`character_isIntegral` を scope に入れるため).
> - `coeff_mul_card_eq_classSumCoeff` : per-element 因子数 `a_{ijs}=(classSum Ci*classSum Cj) Cs.out` ×
>   `|C_s|` = pair-count `classSumCoeff Ci Cj Cs` (Peterfalvi `a_{ijs}|C_s|`). `classSum_mul` の class-sum
>   係数 (per-element count) と (6.7.1) の pair-count を ℂ-cast で橋渡し. proof は pair 集合を `uv` の class
>   で fiber 分割 (`Finset.card_biUnion`) + per-element count の class-不変性 (`classSum_mul_apply_out`).
> - `character_one_mul_coeff_mul_centralChar` : 各項 `ψ(1)·a_{ijs}·ω(C_s) = (a_{ijs}|C_s|)·χ(C_s.out)`
>   (`ω(C_s)=(|C_s|χ(C_s.out))/χ(1)` + 上記 pair-count identity).
> - `character_one_mul_coeff_mul_centralChar_cong_zero` : `m ∣ a_{ijs}|C_s|` ((6.7.1) 入力) ⟹ 当該項
>   `≡ 0 [ALGMOD m]` (`cong_of_exists_isIntegral`; 代数的整数 `χ(C_s.out)` の `m` 倍).
> - **`centralCharacterOfRep_classSum_mul_cong`** = **(6.7.2)** :
>   `ψ(1)·ω(C_i)·ω(C_j) ≡ ∑_{inZ C_s} ψ(1)·a_{ijs}·ω(C_s) [ALGMOD m]` (`inZ` = `C_s∩Z≠∅` の decidable 述語;
>   `¬inZ` 項は `m∣a_{ijs}|C_s|` で脱落). proof は `centralCharacterOfRep_classSum_mul` ×ψ(1) で全 sum 展開 →
>   `Finset.sum_filter_add_sum_filter_not` で split → `¬inZ` 部分が `Finset.sum_induction` (`≡0` の加法閉) で `≡0`.
>   Peterfalvi `ψ(1)α² ≡ ψ(1)(a_{ij0}+a_{ij}α)` の `ω(C_s)=α` collapse 前形 (collapse は α 不変性の group-theory 要).

> **進捗 2026-05-30 ((6.7.3) 合同算術 assembly 完了, commits 27ed939/2be1cc3)**: (6.7.3) を
> group-theory atoms を仮説とする **conditional** assembly に還元して `ClassSumAlgebra.lean` に, cancellation
> infra を `AlgInt.lean` に実装済 (AxiomsCheck 登録). ⚠️ memory `scaffold-sorry-free-not-done` に照らし:
> これは sorry-free だが atoms (`a_{110}=0`,`a_{120}=|C₁|`,`z⁻¹∤z`,`ω(C_s)=α` const) を仮説に外出しした
> conditional 形 — 真の完了には atoms の group-theory 証明が要る (下記「残依存」). assembly 自体の算術は本物.
> - `AlgInt.Cong.intMul_cancel_left` : `(c:ℂ)·a≡(c:ℂ)·b (mod n)` + `IsCoprime c n` (ℤ) + a,b 代数的整数 ⟹
>   `a≡b (mod n)`. Bézout `uc+vn=1` で `(a-b)/n = u·(c(a-b)/n) + v·(a-b)` (両項整数係数×代数的整数で整). =
>   (6.7.3) の「`|C₁|` で割る」step. **端点整数性が本質** (2 合同の積が無条件でないのと同根; `character_isIntegral` 供給).
> - `peterfalvi_673_combine` : 2 つの (6.7.2) instance (1,1) `ψ(1)α²≡ψ(1)a_{11}α` (a_{110}=0) /
>   (1,2) `ψ(1)α²≡ψ(1)(|C₁|+a_{12}α)` (a_{120}=|C₁|) の `symm.trans`.
> - `peterfalvi_673_cancel` : `ψ(1)α=|C₁|ψ(z)` 代入で両辺を `|C₁|·(…)` 形にして `intMul_cancel_left` で
>   `|C₁|` cancel ⟹ `a_{11}ψ(z)≡ψ(1)+a_{12}ψ(z)`.
> - `peterfalvi_673_final` : `1_G` instance `a_{11}≡1+a_{12}` を `ψ(z)` (整) 倍 (`Cong.smul_left`) →
>   `a_{11}ψ(z)≡ψ(z)+a_{12}ψ(z)`, `hψ` と trans して `ψ(z)+a_{12}ψ(z)≡ψ(1)+a_{12}ψ(z)`, `a_{12}ψ(z)` を sub.
> - **`peterfalvi_673`** = **(6.7.3)** : combine→cancel→final の chain を atoms 仮説から組む 1 本.
> - **残依存** (= (6.7.3) 真完了に要る group-theory atoms; いずれも (6.7) full setup
>   `IsTISubset`+Sylow `P`+`Z⊴L`+`|C_L(z)|` const を要する `needs-infra`):
>   (i) 構造定数計算 `a_{110}=0` (`(u,u⁻¹)`, u∈C_1, u⁻¹∈C_2≠C_1 ⟹ 不可) / `a_{120}=|C_1|`;
>   (ii) `|L| odd ⟹ z⁻¹` が `z` に G-非共役 (z∈C_1, z⁻¹∈C_2 を distinct に取れる);
>   (iii) `ω(C_s)=α` が `C_s∩Z^#≠∅` 上不変 (`ψ(z),|C_L(z)|` の z∈Z^# 不変性から) + `ω(C_0)=1` で右辺 collapse;
>   (iv) `(|C_1|,p)=1` (= `IsCoprime |C_1| |P|`).

> **進捗 2026-05-30 ((6.7.2) geometric form — abstract `hdvd` を (6.7) setup から放電)**:
> `ClassSumAlgebra.lean` (`section ClassCongruence`) に
> **`centralCharacterOfRep_classSum_mul_cong_of_isTISubset`** を landing (AxiomsCheck 登録, 3 axioms 全
> allowlist 内). これは抽象版 `centralCharacterOfRep_classSum_mul_cong` (仮説 `hdvd : ∀ Cs, ¬inZ Cs →
> m ∣ classSumCoeff` を要求) を **実 (6.7) setup** へ特殊化したもの:
> - 仮説: Sylow `p`-subgroup `P`, `Z ≤ P` で `Z ⊴ L=N_G(P)` (`hZnormal`), `P^#=P∖{1}` TI-subset
>   (`hti : IsTISubset (P∖{1}) (N_G(P))`), source class `C_i,C_j` が `Z^#` と交わる (`hCi`/`hCj`).
> - 設定: `m := |P| = Nat.card P` (≠0: `Nat.card_pos`, P は群 nonempty + finite), 
>   `inZ Cs := ∃ w, ⟦w⟧=Cs ∧ w∈Z` (= Peterfalvi の `C_s∩Z≠∅`; `open Classical in` で statement の
>   `Finset.filter` の `DecidablePred` を供給, `omit [DecidableEq G]`).
> - `hdvd` の放電が新規部分: `¬inZ C_s` は `∀ w, ⟦w⟧=Cs → w∉Z` と同値 = (6.7.1)
>   `fixedPointFree_classPair_of_isTISubset` の `hCs` 仮説そのもの. それで fixed-point-free を得て (6.7.1)
>   counting `card_dvd_classSumCoeff_of_fixedPointFree` に流すと `|P| ∣ a_{ijs}|C_s|` (ℕ);
>   `exact_mod_cast` で ℤ. これで **(6.7.1) fixed-point-free + counting + (6.7.2) product rule を 1 定理に
>   合成**, (6.7.3) の geometric source `h11`/`h12` (`ψ(1)α²≡ψ(1)(a_{ij0}+a_{ij}α)`) が立つ.
>   残 atoms = 上記 (i)`a_{110}=0`/`a_{120}=|C₁|` 構造定数 + (iii)`ω(C_s)=α` const + (iv)`(|C₁|,p)=1` のみ
>   (= 純粋に構造定数・指標値の計算; fixed-point-free の group-theory は本定理で解消済).

> **進捗 2026-05-30 ((6.7.3) atom discharge — (i)/(iv)/`ω(C₀)=1` 完了, (ii)/(iii) 残)**:
> `ClassSumAlgebra.lean` に (6.7.3) の group-theory atoms を放電する standalone 補題群を landing
> (commits 5105064 / 4588590 / 399945c / ed4fae7, 全 AxiomsCheck 登録, unconditional). これで
> `peterfalvi_673` の conditional 仮説のうち **構造定数 (i) と coprimality (iv) と (iii) の `ω(C₀)=1`
> 部分が真の補題として独立に証明済**になった:
> - **構造定数 (i)** (`section StructureCoeffAtIdentity`): `classSumCoeff_one_eq_zero` (`a_{110}=0`,
>   抽象仮説 `∀u, mk u=Ci→mk u⁻¹≠Cj` で filter 空) / `classSumCoeff_one_eq_card` (`a_{120}=|C₁|`,
>   `Cj` = inverse class で bijection `u↦(u,u⁻¹)`). z-keyed instance:
>   `classSumCoeff_self_one_eq_zero` (`C₁=⟦z⟧`, **唯一の仮説 = `⟦z⁻¹⟧≠⟦z⟧`**) /
>   `classSumCoeff_self_inv_one_eq_card` (`C₂=⟦z⁻¹⟧`, **完全 unconditional** — `mk_inv_eq_of_mk_eq`).
> - **coprimality (iv)** (`section ClassSizeCoprime`, `[Finite G]`): `card_class_eq_index_centralizer`
>   (orbit-stabilizer `|⟦z⟧|=[G:C_G(z)]`; `ConjAct G` 作用, `orbit=carrier`, `stabilizer=centralizer`,
>   `toConjAct` 同型で card 移送 + `index_mul_card` cancel) / `coprime_card_class_card_sylow`
>   (`(|C₁|,p)=1`; `P≤C_G(z)` (z∈Z(P)) ⟹ `[G:C_G(z)]∣[G:P]` (`index_dvd_of_le`), `p∤[G:P]`
>   (`Sylow.not_dvd_index`), `|P|=p^k`).
> - **(iii) の `ω(C₀)=1`** (`section Evaluation`): `centralCharacterOfRep_one` (identity class =
>   singleton `{1}`, `ω=1·χ(1)/χ(1)=1`).
> - **残 atom (fully unconditional `peterfalvi_673` 化の前提)**:
>   (ii-wrap) real-class atom `⟦z⁻¹⟧≠⟦z⟧` の **TI-reduction** (`|L| odd`+`P^#` TI+`z∈P` ⟹
>     `¬IsConj_G z⁻¹ z`, Peterfalvi L122). core `ConjClasses.eq_one_of_isConj_inv_of_odd_card` は repo
>     既存 (`BrauerPermutation.lean`) だが TI-reduction wrapper は **import cycle
>     `ClassSumAlgebra←ZIrr←IrrIndexing←BrauerPermutation` で `ClassSumAlgebra` に置けない** ⟹
>     downstream module (例: `ZIrr` か新規 file) 行き.
>   (iii-collapse) `centralCharacterOfRep_classSum_mul_cong_of_isTISubset` の RHS sum を Peterfalvi
>     `ψ(1)(a_{ij0}+a_{ij}α)` 形へ collapse する補題. `{C_s∩Z≠∅}` を `{⟦1⟧}` (ω=1) と `{C_s∩Z^#≠∅}`
>     (ω=α, **atom iii = `ω` 不変性, `ψ`+`|C_L(z)|` の Z^# 不変性依存**) に分割し per-element count を
>     regroup. `|C_L(z)|` const の (6.7) setup 仕込みを要する最深 `needs-infra`.

> **進捗 2026-05-30 ((6.7.3) 残 atom (ii-wrap) real-class TI-reduction 完了, 新規 `RealClassTISubset.lean`)**:
> 上記 (ii-wrap) を解消. `BrauerPermutation` (= `eq_one_of_isConj_inv_of_odd_card` の在処) と
> `ClassSumAlgebra` の **両方の downstream** に新 leaf module
> `OddOrder/GroupTheory/RepresentationTheory/RealClassTISubset.lean` を作成 (unconditional, AxiomsCheck 登録).
> import cycle 回避: `ZIrr` は `BrauerPermutation` の *upstream* ゆえ不可 (`ZIrr←IrrIndexing←BrauerPermutation`);
> `BrauerPermutation` を import すれば `ClassSumAlgebra` も transitive に入る. 2 定理:
> - `not_isConj_inv_of_isTISubset` : `P∈Syl_p`, `Odd |N_G(P)|`, `P^#=P∖{1}` が `N_G(P)` 相対 TI-subset,
>   `z∈P`, `z≠1` ⟹ `¬IsConj z⁻¹ z`. 証明: `z,z⁻¹∈P^#`; `G`-conjugator `c` (`c z⁻¹ c⁻¹=z`) が `z⁻¹∈P^#`
>   を `z∈P^#` へ送るので TI で `c∈L=N_G(P)`; `z∈L` (`P≤L`) と合わせ `↥L` 内で `IsConj (⟨z,_⟩⁻¹) ⟨z,_⟩`;
>   `|L|` odd で `eq_one_of_isConj_inv_of_odd_card` が `z=1` を強制し矛盾. = Peterfalvi L122「`|L|` odd ⟹
>   `z⁻¹` は `G` 内で `z` に共役でない」.
> - `mk_inv_ne_self_of_isTISubset` : 上の class 形 `⟦z⁻¹⟧≠⟦z⟧` (`mk_eq_mk_iff_isConj`). これが
>   `classSumCoeff_self_one_eq_zero` の唯一仮説に直接プラグインし **(ii) 残を解消**.
> - mathlib quirk (rc2): `Subgroup.normalizer : Set G → Subgroup G` (Set 引数) のため, `Nat.card`/`Finite`/
>   subtype-ascription 等の型位置では `Subgroup→Set` 引数 coercion が自動挿入されずエラー. `∈`/`IsTISubset`
>   引数位置 (期待型 `Subgroup G`) は OK. `set L := Subgroup.normalizer ((P:Subgroup G):Set G)` で `hodd`/`hti`
>   を畳んで全箇所一貫化し回避.
> - **残**: fully unconditional `peterfalvi_673` の最後の依存は (iii-collapse) のみ
>   (`centralCharacterOfRep_classSum_mul_cong_of_isTISubset` の RHS sum collapse, `|C_L(z)|` const 依存).

> **進捗 2026-05-30 ((6.7.3) atom (i) `a_{110}=0` を (6.7) setup から hypothesis-free 化, `RealClassTISubset.lean`)**:
> 上記 (ii-wrap) real-class atom を構造定数計算に**配線**し, `a_{110}=0` を (6.7) setup から無条件化.
> `RealClassTISubset.lean` に `classSumCoeff_self_one_eq_zero_of_isTISubset` を追加 (unconditional,
> AxiomsCheck 登録, `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑, 3 axioms 全 allowlist 内):
> - `classSumCoeff_self_one_eq_zero_of_isTISubset` (`[Fintype G]`, `[DecidableEq (ConjClasses G)]`,
>   `P∈Syl_p`, `Odd |N_G(P)|`, `P^#=P∖{1}` が `N_G(P)` 相対 TI-subset, `z∈P`, `z≠1` ⟹
>   `classSumCoeff ⟦z⟧ ⟦z⟧ 1 = 0`): `mk_inv_ne_self_of_isTISubset` を `classSumCoeff_self_one_eq_zero`
>   (唯一仮説 = `⟦z⁻¹⟧≠⟦z⟧`) にプラグイン. これで **(6.7.3) の `a_{110}=0` 入力が group-theory 仮説ゼロ**で
>   (6.7) data から出る (`z∈P^#` のみ要求). placement は atom と同理由で本 leaf (`BrauerPermutation` downstream;
>   `ClassSumAlgebra` への `BrauerPermutation` import は cycle `ClassSumAlgebra←ZIrr←IrrIndexing←BrauerPermutation`).
> - **残 (fully unconditional `peterfalvi_673` の唯一の前提)**: (iii-collapse) のみ.
>   `centralCharacterOfRep_classSum_mul_cong_of_isTISubset` は (6.7.2) を **SUM 形**
>   (`ψ(1)ω(C_i)ω(C_j) ≡ ∑_{C_s∩Z≠∅} ψ(1)a_{ijs}ω(C_s)`) で無条件に出すが, `peterfalvi_673` の `h11`/`h12`
>   入力は **collapse 形** (`ψ(1)α² ≡ ψ(1)(a_{ij0}+a_{ij}α)`). 橋には `ω(C_s)=α` (`C_s∩Z^#≠∅` 上不変) が要り,
>   それは `|C_L(z)|` const = `[G:C_G(z)]·ψ(z)` が `z∈Z^#` で不変 = (6.7) hypothesis の deep character-theory
>   仕込み (`needs-infra`). これは memory `scaffold-sorry-free-not-done` の趣旨に照らし**仮説外出ししない**
>   (外出しは vacuous/too-strong になる). 真の完了には `|C_L(z)|`-constancy 部品の実装が要る (別 issue).

> **進捗 2026-05-30 (characterDegree ↔ finrank bridge 完了)**: Round 3 の `finrank_dvd_card`
> (`χ_ρ(1) ∣ |G|`, `ClassSumAlgebra.lean`) は `Representation.character` レベルだったため S03 の
> `characterDegree`/`ClassFunction` 層へ流れず Peterfalvi の degree 文に乗らなかった。この橋を
> `OddOrder/GroupTheory/RepresentationTheory/ZIrr.lean` に実装 (unconditional, AxiomsCheck 登録):
> - `IsIrreducibleCharacter.exists_finrank_charValue_one` : 既約指標 `φ` の値 `φ 1` は任意の witness 表現
>   `ρ` on `V` の次元 `finrank ℂ V` に等しい (`IsIrreducibleCharacter` の存在 witness を unpack →
>   仮説 `Representation.IsIrreducible ρ` を `haveI` で instance 化 → `ρ.char_one`)。`[Finite G]` 不要。
> - `IsIrreducibleCharacter.exists_natDegree_charValue_one_dvd_card` `[Finite G]` : ∃ `n:ℕ`, `0<n ∧ φ 1 = n ∧ n ∣ |G|`
>   (= Isaacs Thm 3.11 の `ClassFunction` 層への載せ替え; `finrank_dvd_card ρ` を直接適用)。
> - **消費経路**: Peterfalvi の `characterDegree φ` は定義上 `φ 1` (`characterDegree_def`, `rfl`/`@[simp]`)
>   なので S03 側で `rw [characterDegree_def]` 後に上記を当てれば `characterDegree φ ∣ |G|` (ℕ 鋳直し) が出る。
>   `ZIrr` は `ClassSumAlgebra` を新規 import (両者 sibling, `ClassFunction` 経由で acyclic; `characterDegree`
>   自体は S03 = downstream なので `ZIrr` からは参照せず `φ 1` 形で橋渡しした)。

**Lean 表現**: 
```lean
theorem S08_6_7 (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (L : Subgroup G) (Z : Subgroup L) 
    (h_odd : Odd (Nat.card L))
    (h_ti : TI_Subset G P.val)
    (h_Z_center : Z ≤ Subgroup.center P.val)
    (h_Z_nontrivial : Z ≠ ⊥)
    (h_C_independent : ∀ z₁ z₂ ∈ Z.val, z₁ ≠ 1 → z₂ ≠ 1 → 
                       (Subgroup.centralizer G z₁).card = (Subgroup.centralizer G z₂).card)
    (ψ : Character G)
    (h_ψ_const : ∀ z₁ z₂ ∈ Z.val, z₁ ≠ 1 → z₂ ≠ 1 → ψ z₁ = ψ z₂) :
    ∀ z ∈ Z.val, z ≠ 1 → ψ z ∈ ℤ ∧ ψ z ≡ ψ 1 [ZMOD P.val.card] := by
  sorry
```

複雑: 7 つの sub-lemma が必要, class algebra の detailed calculation

### (6.8) Main Theorem — Frobenius Family の Coherence 統合定理

**主張**: G 有限, L ⊂ G,
- (a) L = H ⋊ W_1, |L| odd, H non-identity nilpotent, H^# TI with normalizer L
- (b) S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}, τ = restriction of Ind_L^G to Z[S, L^#]
- (c) Two cases:
  - (c1) L は kernel H を持つ Frobenius 群
  - (c2) Hypothesis (4.6) (Dade condition) + w_2 prime + W_2 ⊂ [H,H]

**結論**: **S is coherent** (τ が全 Z[S] に拡張できる)

**証明** (mmd L136-244, 3 つの main sub-proofs + 8 sub-lemmas):

**(6.8.1) X ∪ Y coherent in case (A)**: 
- Setup: Z = Z(H) ∩ [H,H] in (A), or Z = W_2 in (B)
- X = S - S(Z), Y = S([H,H])
- (6.6) + Dade 応用 ⟹ X coherent
- Y は orthonormal base ⟹ X ∪ Y coherent

**(6.8.2) X ∪ Y coherent in case (B)** (W_2 ⊂ Z(H)):
- Sub-lemmas:
  - **(6.8.2.1)**: η ∈ Y ⟹ η^{τ_1} constant on Z^#
  - **(6.8.2.2)**: (Ind_Z φ - |H:Z|η_1)^τ = X - |H:Z|Y (with explicit formula)
  - **(6.8.2.3)**: χ ∈ X ⟹ (χ - a η_1)^τ = X_1 - aY
- Isometry preservation

**(6.8.3) S is coherent** (Final):
- Contrapositive: S NOT coherent ⟹ S ≠ X ∪ Y ∃ S_1, S_2 with S_1 coherent, S_1 ∪ S_2 NOT coherent
- (5.6) apply ⟹ 2ψ(1)η_1(1) > Σ_χ χ(1)²/‖χ‖²
- (6.8.1)-(6.8.2) + calculation mod 4|W_1|² ⟹ contradiction

**数学的意義**:
- **§8 の最高峰** — Coherence framework の最終統合
- Frobenius group (case c1) + Dade isometry (case c2) の両立
- §9-§16 構造分析での character 計算基盤

**Lean 形式化難度**: ★★★★★
- 8 つの sub-lemma の逐次的構築
- case split (A) vs (B)
- isometry 延長の explicit construction
- norm/orthogonality 計算の chain

## Sibley 系の同定 (Reynolds 削除)

⚠️ audit 訂正 (2026-05-23): 旧 section の「Sibley 1984 Contemp. Math. 47」と「Reynolds 1965 Duke Math. J.」は **両方とも完全捏造** (Peterfalvi 参考文献 04.18 + Notes 04.17 で検証):

- **正しい Sibley 引用**: **[Si1] Sibley, M. J. (1976), "Coherence in finite groups containing a Frobenius section", *Illinois J. Math.* 20:434-442** + **[Si2] unpublished lectures**
- **Reynolds は本書全体に存在しない**. (6.7) は無名 internal lemma; (6.8) Sibley の前段補題.

### Sibley 1976 [Si1] との関連

**Notes §SS6 (mmd 04.17 L11) 明示**:
- (6.3), (6.5) は **[FT] §11** (Feit-Thompson 1963 原論文) から
- **(6.8) のみ** が Sibley [Si1] の寄与

(6.8) Main Theorem: L が Frobenius or Dade condition 満たす時 S が coherent — これが Sibley 1976 *Illinois J. Math.* 20 の主結果の Peterfalvi 版.

### (6.7) は無名 lemma

Reynolds 帰属は完全捏造のため削除. (6.7) は character class congruence の internal lemma で、proof で:
- [Is] p.35 class-sum algebra hom `ω : ZC[G] → C` (mathlib 不在)
- algebraic integer congruence `α ≡ β mod n` in Z[ζ_n] (mathlib 不在)
- TI-subset (§4-§5)
- [Is] Lem 7.7 (§8 で 2 回利用)

を使用. (6.8) の Frobenius case の前準備.

## §10-§16 구조분석에서의 사용

### §9 Non-existence of Certain Type (BG App.C)

- (6.1)-(6.4): Frobenius family의 coherence를 통해 non-existence 증명의 "character-theoretic obstruction" 제공
- (6.8): 최종 non-existence의 핵심 — Type I-V 분류 이전에 Frobenius structure 자체가 불가능함을 보임

### §10-§14 Type I-V 분석

- **(6.8)**: Type I (Elementary abelian Sylow 2-subgroup, BG Type A) 분석의 기초
- (6.1)-(6.3): Commutator subgroup chain을 따라 coherence를 추적하며 maximal subgroup의 structure constraint 도출
- (6.5): p-group structure bound가 Type classification을 진행하는 동안 dimension reduction 제공

### §15 S and T 부분군 분석

- (6.8.1)-(6.8.3)의 explicit isometry construction이 S, T의 character extension을 계산할 때 reuse됨
- Coherence predicate이 "S ⊂ Irr L" 판정에 사용됨 (irreducibility vs reducibility 구분)

### §16 Non-existence of G

- (6.2)의 inequality chaining: |K:A|-1 bound가 size argument (counting irreducibles)로 변환
- (6.7) mod |P| congruence: G의 존재 → character class 계산에서 모순 (final punch)
- (6.8) coherence chain: 최종 FT 증명에서 "모든 가능한 G의 maximal subgroup이 coherent character set을 가질 수 없다" 를 보이는 핵심

## mathlib 카버리지

### 기존 API
- `Subgroup.normal`: normal subgroup predicate ✓
- `Representation ℂ L` / `Character L`: representation, character type ✓
- `inner_product` (character 내적): ✓
- `Induced`: induced character/representation (부분) ✓

### 新規 (Phase 2b에서 정의 필요)

1. **Coherence 관련**:
   - `def Coherence (τ : E →ₗᵢ[ℤ] Z[Irr G]) (S : Set (Irr L)) (A : Set L) : Prop`
   - `structure CoherenceTriple`
   - Lemma/Theorem collections 전 (5.2)-(5.9) [§7에서 정의]

2. **§8 고유**:
   - `def CoherenceHypothesis (6.1)` — mmd notation과 정확히 동일
   - `structure FilteredCharacterSet` — S(A) filtration
   - `theorem S08_6_2` — 부등식 기반 lemma
   - `theorem S08_6_3` — nilpotent descent
   - `theorem S08_6_7` — Reynolds congruence (복잡)
   - `theorem S08_6_8` — Main theorem

3. **보조 타입**:
   - `IsTI_Subset`: TI-subset predicate (if not in mathlib)
   - `IsCoherent.extends` — isometry extension existence
   - `CharacterClass.CongruenceMod` — modular arithmetic wrapper

## Phase 2b 형식化 着手順

### 선행 조건
- ✓ Phase 1 Isaacs Ch.1-8 완성
- ✓ Phase 2b §3 (Preliminary) 완성
- ✓ Phase 2b §4 (Dade Isometry) 완성
- ✓ Phase 2b §5 (TI-cyclic norm) 완성
- ✓ Phase 2b §6 (Dade for certain type) 완성
- ✓ Phase 2b §7 (Coherence) 완성

### §8 형식화 계획 (예상 2-3주)

#### Wave 1: (6.1) Setup (1-2일)
```lean
structure CoherenceHypothesis ... where
  K : Subgroup L
  K_solvable : IsSolvable K
  K_normal : K ◁ L
  S : Set (Irr L)
  S_def : S = {Ind_K^L θ | θ ∈ Irr K ∧ θ ≠ 1_K}
  S_A : (A : Subgroup K) → A ◁ L → Set (Irr L)
```

#### Wave 2: (6.2) + (6.3) (3-4일)
- (6.2) 부등식의 algebraic 재배열
- (6.3) inductive 모순 구조 — `decide` vs `omega` vs manual `ring` calculation
- (5.6) Coherence extension theorem의 직접 활용

#### Wave 3: (6.4)-(6.5)-(6.6) (4-5일)
- Case split: |L| odd 가정의 전역화
- (6.3) + Frobenius structure 조합 → p-group determination (6.5.b)
- (6.7) 전 단계 — Reynolds congruence 예비

#### Wave 4: (6.7) Lemma (5-7일) ⭐ **hardest**
- Class algebra construction: Z[G]의 conjugacy class의 formal algebra
- `algebra_homomorphism ω` 타입: fintype conjugacy class의 enumeration
- 6 sub-lemma들의 sequential dependent proof
- `decide` / `omega` / `ring` / `decide` chain으로 modular arithmetic

#### Wave 5: (6.8) Main Theorem (7-10일) ⭐⭐ **very hardest**
- (6.8.1) X ∪ Y coherent (case A): (6.6) 활용 + explicit isometry extension
- (6.8.2) X ∪ Y coherent (case B): 3 sub-lemmas + norm 계산
- (6.8.3) S coherent: final contradiction 유도
- **Coherence framework와의 상호작용 극대화** — §7 (5.1)-(5.9)와의 타이트한 integration

#### Wave 6: Integration + Testing (3-4일)
- § 7과의 cross-reference 검증
- §9 형식화 시작 (§8 완료 후 바로)
- LEAN 타입체킹 및 doc string 완성

## 未解決 / TODO

1. **§7 (5.2)-(5.9)와의 정확한 interface**: Hypothesis (5.2) vs (6.4)의 관계 — formal Lean type에서 sub-hypothesison 활용 방법 결정 필요

2. **(6.7)의 "conjugacy class algebra" 형식화 전략**: 
   - Option A: Explicit fintype enumeration (|G| finite이므로 computable)
   - Option B: Abstract algebra homomorphism (더 이론적이지만 계산 어려움)
   - 권장: Hybrid — enumeration + omega tactic

3. **(6.8.2.1)-(6.8.2.3)의 sub-lemma ordering**: 증명 의존도가 복잡하므로 formal dependency graph 먼저 그리기 필요

4. ~~**Sibley 1984 paper access**~~ ⚠️ audit 訂正 (2026-05-23): "Sibley 1984 Contemp. Math. 47" は **完全捏造で存在しない**. 正しくは [Si1] Sibley 1976 *Illinois J. Math.* 20:434-442 のみ. (6.8) Main Theorem が Sibley 1976 の寄与.

5. ~~**Reynolds 1965의 정확한 statement 확인**~~ ⚠️ audit 訂正: "Reynolds 1965 Duke Math. J." は **完全捏造**. Peterfalvi 参考文献 + Notes 両方に Reynolds 不在. (6.7) は無名 internal lemma.

6. **mathlib Character/Induced API의 최신 상태 (May 2026)**: 
   - `Subgroup.induced : Representation ℂ H → Representation ℂ G` (computable?)
   - `Character.inner : Character H → Character H → ℤ` vs `Z[Irr H]` module structure
   - Recent PRs 확인 필요

---

## Summary Table

| Section | Theorems | Type | Mathlib Coverage | FT Role | Est. Implementation |
|---------|----------|------|------------------|---------|-------------------|
| (6.1) | 1 | Setup Hypothesis | low | Foundation | 1-2 days |
| (6.2) | 1 | Inequality Lemma | low | Obstruction | 2 days |
| (6.3) | 1 | Descent Theorem | low | Key tool | 2-3 days |
| (6.4)-(6.6) | 3 | Special case + Lemmas | mid | Sibley system | 4-5 days |
| (6.7) | 1 | Reynolds-type | low | Character class calc | 5-7 days |
| (6.8) | 1 (+ 3 sub-proofs) | Main Theorem | low | Structure analysis | 7-10 days |
| **TOTAL** | **8 主結果** | - | **~5%** (statement-level; (6.7)/(6.8) 0%) | **☆☆** | **~35-45 days realistic** (audit 訂正; 旧 30 days は (6.7) class-sum module + (6.8) Sibley apparatus を過小評価) |

---

*作成: 2026-05-22. 出典: `references/peterfalvi/04.8_pp_30_37_Some_Coherence_Theorems.mmd` (243 行) + `04.7_pp_25_29_Coherence.mmd` (136 行). クロス参照確認済: §7 (5.1)-(5.9), (6.1)-(6.8) self-contained, §9 (7.1)-(7.6) 依存. Phase 2b 第 3 波着手予定は §7 完成後.*

---

## 追記 (2026-05-31): G2.7 gate 調査結論 + (5.2.d) `R(χ)` producer landing

(6.6) `peterfalvi_66_coherence_of_X` / `coherentPairChain` の `hstep` (= G2.7 gate) について調査:

**型レベルの honest verdict (Round-20 roadmap の「Dade wiring」判定を訂正)**: `hstep` 構成は Dade
isometry の wiring **ではなく** genuine 新 infra。理由 — `IsCoherent`/`retarget_isCoherent`/
`CharacterPsiDecomposition` は `IntegralCharacterMap L G = ClassFunction L ℂ →ₗ[ℤ] ClassFunction G ℂ`
(全 class function 上の ℤ-線形, `L G` 独立群) で動くのに対し, `FullDadeIsometryData`/`DadeMap`
(`OddOrder/Peterfalvi/S04_DadeIsometry.lean`) は `SupportedClassFunctions ℂ A L → ClassFunction G ℂ`
(supported 部分加群上のみの bare 関数, `L : Subgroup G`) で**別型**。各 step が要求する running
`τ₁ = hS₁.extension` (χᵢ 含む `Z[S₁]` 全体への isometry) は固定 Dade τ から得られず, mmd 04.8
L156/L166 通りこの lattice isometry の存在こそ (5.6)/(6.6) の結論 (FT では `dim CF(L) > dim CF(G)`
で大域 isometry 不在)。`CharacterPsiDecomposition` は repo 内 constructor 皆無,
`isometry_difference_pair_structure` も適用例皆無で §7↔§3 が断絶していた。

**landed (G2.7 最基礎 brick, sorry-free, axioms 3 個 allowlist; `S07_Coherence.lean`)**: (5.2.d)
`R(χ)` の producer。§3 (1.4) keystone `isometry_difference_pair_structure` の初の実 consumer。

- `characterDifferenceImageOfIsometry` — `τ`, non-real irreducible `χ`, family `{χ,χ̄}` 上の (1.4)
  三仮定から `CharacterDifferenceImage τ χ` を**構成** (`Exists.choose` で signed irreducible
  difference を抽出, `image_eq : τ(χ−χ̄)=ε•(μ−ν)`)。従来 constructor 無しで全 §7 補題が仮定取りして
  いた欠落を埋める。`toOrthonormalImage` 経由で orthonormal `R(χ)` (`OrthonormalCharacterImageFamily`)
  へ持ち上がる。
- 補助: `conjIrreducibleCharacter`/`conjPairFamily`/`coe_conjIrreducibleCharacter`,
  `irreducibleCharacter_conj_apply_one` (`χ̄(1)=χ(1)`, 指標値 at 1 = 自然数 ⟹ 共役不変)。

詳細・残作業 (running `τ₁` 配線 + `CharacterPsiDecomposition` constructor) は issue 0046 の進捗節
(2026-05-31) 参照。

### G2.7 PASS 2 (2026-05-31): (5.6.3) target pair `{X, X̄}` を (5.5) から構成

PASS 1 で genuine 新 infra と判定した G2.7 のうち **source-independent な layer** =
`retarget_isCoherent` の `{X, X̄}` block を `CharacterPsiDecomposition τ χ 0` から **構成** (posit 無)。
sorry/axiom 無, AxiomsCheck 登録 2 件 (3 axioms 全 allowlist), commit c6df07e。

- **`CharacterPsiDecomposition.RetargetTargetPair` + `.retargetTargetPair`**: irreducible `χ`
  (`‖χ‖²=1`) の (5.5) 分解 + source-pair orthonormality から `X := D.X`, `X̄ := D.X − (χ−χ̄)^τ` の
  orthonormal pair (`‖X‖²=‖X̄‖²=1`, `⟨X,X̄⟩=0`, 両者 ∈ `ℤ[Irr G]`)。**`|R(χ)|=‖χ−χ̄‖²=2` を
  `tau1_agrees`+τ₁-isometry で導き, `|E|=‖χ‖²=1` (5.5) と合わせ `‖X̄‖²=|R(χ)|−|E|=1`**。
- **`retarget_isCoherent_of_decomposition`**: `{X,X̄}` を data でなく `D` から構成して
  `retarget_isCoherent` に投入 ⟹ `IsCoherent (S₁∪{χ,χ̄}) A`。残仮説は **running `τ₁` 結合の 2 つ**
  (`hX_ortho`/`hXbar_ortho` = (5.2.e) cross-orthogonality, `himg` = (5.6.2) image eq) のみに精密化。

**Round-20 roadmap の反証**: 「Gram–Schmidt / free-module basis-extension 欠落 primitive が必要」は
**誤り**。irreducible `χ` では `|E|=1` ゆえ `X` は単一 R(χ) 元, target pair は FORCED で rescaling
不要。真の残 gap は orthonormalization でなく **(a) `CharacterPsiDecomposition` instance の構成
(auxiliary `tau1` が running τ と `χ−χ̄` 上一致), (b) `hX_ortho`/`himg` の running-`τ₁` 放電**。
両者は `hS₁.extension` に本質依存し固定 Dade τ から出ない (PASS 1 型ミスマッチ判定通り)。

### G2.7 PASS 3 (2026-05-31): Dade isometry を (5.1) base map `τ` として実体化 (type-bridge)

PASS 1/2 で「§4 Dade map (`SupportedClassFunctions ℂ A L → ClassFunction G ℂ`, bare partial,
`L : Subgroup G`) と §7 `IntegralCharacterMap L G := ClassFunction L ℂ →ₗ[ℤ] ClassFunction G ℂ`
(total ℤ-linear, `L G : Type*`) は別型」と判定した残 gap のうち, **base map `τ` 側の type-bridge を
構成** (posit 無, sorry/axiom 無, AxiomsCheck 登録 3 件 全 allowlist)。

**mmd 04.7 L3 (5.1) Definition の決定的読解**: coherence の base map `τ` は「`Z[S,A] ⊂ E ⊂ Z[Irr L]`
上の `ℤ`-linear isometry」で, (5.6.3) (mmd L101) は `τ` を **supported sublattice `Z[S₁,L^#]` および
差 `χ−aχ₁`, `χ−χ̄` 上で直接**使う。すなわち §4–§16 では **`τ` = §4 Dade isometry** (が supported span
上で). Lean `IsCoherent τ S A` はこれを忠実に符号化: `τ` を制約するのは `extends_on_supported`
(`zSupportedSpan S A` 上で `extension = τ`) **のみ**で, supported span 外の `τ` 値は一切 inspect
されない。**roadmap の Q1「τ は別 running isometry」判定は `τ` と `extension` を混同したもので,
正しくは Q2 (= τ は Dade isometry, supported span 上で一致する bridge が必要)**。

- **`Hypothesis.dadeLinearMap` (S04)**: bare `DadeMap` (`hyp.dadeMap`) を `ℂ`-linear map
  `CF(L,A) →ₗ[ℂ] CF(G)` として package。`dadeValue α g = α(a)` (固定基点 `a` での **評価**, support 外 0)
  ゆえ `α` について `ℂ`-linear。`map_add'`/`map_smul'` は `dadeValue_eq`/`dadeValue_of_not_mem` の
  case 分け + 係数加群 coe の `rfl`。
- **`dadeIntegralCharacterMap` (S07)**: `LinearMap.exists_extend` (体 `ℂ` 上の部分空間の分裂) で
  `dadeLinearMap` を `CF(L) →ₗ[ℂ] CF(G)` に延長 → `restrictScalars ℤ` で `IntegralCharacterMap ↥L G`。
  **延長は非標準 (complement 任意) だが無害**: supported span 外は coherence が見ない。
- **`dadeIntegralCharacterMap_apply_of_support`**: 定義性質 = supported subspace (`φ.support ⊆
  supportInSubgroup A L`) 上で lift = Dade map (`hyp.dadeMap ⟨φ,_⟩`)。`LinearMap.exists_extend` の
  `g ∘ subtype = dadeLinearMap` を `congr_fun` で評価。**これが (5.6.3) の `τ` on `Z[S,L^#]` を
  実 §4 isometry から供給する**。

**型整合**: S07 の `L G : Type*`, `A : Set L` を `↥L_subgroup`, `supportInSubgroup A_G L` で具体化。
`zSupportedSpan S (supportInSubgroup A_G L)` の元は `support ⊆ supportInSubgroup A_G L` を満たし
`dadeIntegralCharacterMap_apply_of_support` の仮説に直結。

**PASS 3 後の残 (hstep の (5.6.2) image eq 本体)**: `peterfalvi_66_coherence_of_X` の `hstep` を
`retarget_isCoherent_of_decomposition` で放電するには, `τ = dadeIntegralCharacterMap` に対し
`himg : τ(χ−aχ₁) = D.X − a•hS₁.extension χ₁` ((5.6.2) `Y = aχ₁^{τ₁}`) を組む必要。(5.6.2) capstone
`lambda_eq_zero_and_Z_eq_zero` (`λ=0 ∧ Z=0`) は landed なので, 残は **(5.6.1) の λ-係数分解 `hY`
(= `Y = ∑ᵢ(a[i=i₁]−λ·rᵢ)•χᵢ^{τ₁} + Z`) を実際の Dade τ・running `τ₁ = hS₁.extension` から導き,
`λ=0,Z=0` を代入して `Y = a•χ₁^{τ₁}` → `himg`** の assembly (wiring でなく (5.6.1) 本体, PASS 4+)。
これは `D.tau1`↔`hS₁.extension` 結合と (5.6.1) の cross-difference 計算を要し本質的に hard。

### G2.7 PASS 4 (2026-05-31): (5.6.2) image-equation supplier `himg` を *構成* + end-to-end 組立器

PASS 3 後の残 (`himg` を **posit せず構成**) を解消。`peterfalvi_66_coherence_of_X` の `hstep` が
Dade-isometry targets から放電可能になった (posit 無, sorry/axiom 無, AxiomsCheck 登録 2 件 全
allowlist; `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑)。

**verdict 再確認 (mmd 04.7 (5.6.2)/(5.6.3) 精読)**: `retarget_isCoherent` の `himg : τ(χ−aχ₁) =
X − a·τ₁χ₁` は **(5.6.1)+(5.6.2) そのもの** — `(χ−aχ₁)^τ = X−Y` の `R(χ)`-射影 + 整数強制 `λ=0` で
`Y = a·χ₁^{τ₁}`。これは free wiring でなく (5.6) の核。`τ₁ = hS₁.extension` は (5.6.3) の "τ₂ が `τ` と
`Z[S₁,L^#]`, `χ−aχ₁`, `χ−χ̄` 上で一致" の running isometry。`τ` (LHS) は Dade isometry (supported span 上)。

- **`image_eq_of_decomposition`** (= (5.6.2) image-eq supplier): `himg` を (5.4)/(5.6.1) decomposition
  `D : CharacterPsiDecomposition τ χ (a·χ₁)` と 3 honest 入力から *構成*:
  - `htau1_diff : D.tau1 (χ−a·χ₁) = τ (χ−a·χ₁)` — (5.4) auxiliary isometry `D.tau1` が supported
    difference 上で `τ` (Dade map) と一致 (mmd (5.4) "τ₁ coincides with τ on `Z[χ−ψ, χ−χ̄]`");
  - `hY : D.Y = a • D.tau1 χ₁` — (5.6.2) 結論 `Y = a·χ₁^{τ₁}` (λ=0/Z=0 後);
  - `htau1_chi1 : D.tau1 χ₁ = hS₁.extension χ₁` — `D.tau1` が running coherence 拡張と `χ₁∈S₁` で一致。
  proof は 1 行: `rw [← htau1_diff, D.tau1_image, hY, htau1_chi1]` (連鎖
  `τ(χ−aχ₁) = D.tau1(χ−aχ₁) = D.X − D.Y = D.X − a·D.tau1 χ₁ = D.X − a·hS₁.extension χ₁`)。
  **これが §4↔§7 結合点の正準形**: Dade-isometry 側は `htau1_diff` の RHS `τ(χ−aχ₁)` で入る
  (= supported difference の §4 Dade 像, `dadeIntegralCharacterMap_apply_of_support` で具体化可能)。
- **`retarget_isCoherent_of_decompositions`** (= 完全 per-step adjoining, `himg` 内部放電):
  (6.6)/(6.8) `coherentPairChain` の 1 step `IsCoherent τ S₁ A → IsCoherent τ (S₁∪{χ,χ̄}) A` の
  **単一入口**。(5.5) decomposition `D₀ : CharacterPsiDecomposition τ χ 0` (orthonormal pair
  `{D₀.X, X̄}` 用) と (5.6.1) decomposition `Da : CharacterPsiDecomposition τ χ (a·χ₁)` (himg 用),
  共通射影 `hX_eq : Da.X = D₀.X` ((5.6.2) 同定) を取り, `retargetTargetPair` で pair 構成 +
  `image_eq_of_decomposition` で `himg` 内部放電 → `retarget_isCoherent_of_decomposition` に委譲。
  `pairSet pair i = {(pair i).1, (pair i).2}`, `pairUnion S₀ pair (i+1) = pairUnion S₀ pair i ∪
  pairSet pair i` ゆえ `hstep` target に直結。

**PASS 4 後の残 (この round 範囲外, (5.4)/(5.6.1) 本体 content; wiring 部分は完了)**:
1. 各 step の **decomposition `D₀`/`Da` の生産** — (5.4) auxiliary isometry `D.tau1` (Dade `τ` と
   supported diff 上一致, running `τ₁` と `S₁` 上一致) の構成。
2. **(5.6.2) `hY` の導出** — (5.6.1) λ-係数分解を `lambda_eq_zero_and_Z_eq_zero` に流す cross-difference
   計算 (`crossDifference_inner` 系で source 側は landed, image 側 `χᵢ^{τ₁} ⊥ R(χ)` の (5.5)+(5.2.e)
   結合が残)。capstone 自体は landed。
3. **`Da.X = D₀.X` の (5.6.2) 同定** — 2 射影が同一 `∑_{α∈E}α` になること (`a·χ₁^{τ₁} ⊥ R(χ)` ゆえ)。

### G2.7 Round 23 PASS 1 (2026-05-31): (5.6.3) 射影同定 `Da.X=D₀.X` + (5.5)+(5.2.e) image-side orthogonality を *構成*

PASS 4 末尾の残 3 (`Da.X=D₀.X` 同定) と残 2 の image 側 (`χᵢ^{τ₁} ⊥ R(χ)` 結合の reduction) を解消。
`retarget_isCoherent_of_decompositions` から **3 つの opaque 仮説** (`hX_eq`, `hX_ortho`, `hXbar_ortho`)
が消え, genuine な (5.5)/(5.6.2)/(5.2.e) data から *構成*されるようになった (posit 無, sorry/axiom 無,
AxiomsCheck 4 件 新規 全 allowlist; `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3360 jobs;
commits 32a8c37 / e340467)。

- **(a)+(c) 射影同定 `Da.X = D₀.X`** (`CharacterPsiDecomposition` namespace):
  - `X_eq_tau1_chi_of_Y_eq` : (5.6.2) collapse `hY : Da.Y = a·χ₁^{τ₁}` から `Da.X = Da.tau1 χ`
    (= χ^{τ₁})。proof は `Da.tau1 (χ−a·χ₁) = Da.X − Da.Y = Da.X − a·χ₁^{τ₁}` (tau1_image, hY) と
    線形性 `= χ^{τ₁} − a·χ₁^{τ₁}` (map_sub, map_nsmul) を `sub_left_inj` で相殺。`a : ℕ` 必須
    (map_nsmul)。これが (5.6.3) の「X が ψ に依らない」核。
  - `X_eq_of_tau1_eq_on_chi` : `Da.X = Da.tau1 χ` (上) + `Da.tau1 χ = D₀.tau1 χ` (τ₁-agreement,
    honest 入力) + `D₀.tau1 χ = D₀.X` (eq_sum_of_psi_eq_zero, (5.5)) を連鎖し `Da.X = D₀.X`。
  - **`retarget_isCoherent_of_decompositions`**: posit していた `hX_eq : Da.X = D₀.X` を, より原始的な
    honest 入力 `htau1_chi : Da.tau1 χ = D₀.tau1 χ` (両 decomposition が running τ₁ を χ で同一評価) に
    置換し, `hX_eq` を `X_eq_of_tau1_eq_on_chi` で内部導出。
- **(b) image-side orthogonality `X, X̄ ⊥ τ₁ξ`** (`CharacterPsiDecomposition` namespace):
  - `inner_X_eq_zero_of_orthogonal_imageSet` : per-element `∀α∈R(χ), ⟨η,α⟩=0` ⟹ `⟨η, X⟩=0`,
    via `X_eq : X = ∑ coeff•α` + `inner_sum_right`/`inner_smul_right`。
  - `inner_conjImage_eq_zero_of_orthogonal_imageSet` : 同様に `⟨η, X̄⟩=0` (X̄ = X−(χ−χ̄)^τ;
    `(χ−χ̄)^τ = ∑_{α∈R(χ)}α` ゆえ X̄ も ℤ[R(χ)])。
  - **`retarget_isCoherent_of_decompositions`**: posit していた sum-level `hX_ortho`/`hXbar_ortho` を
    単一 per-element 入力 `hperElem : ∀ξ∈ℤ[S₁], ∀α∈R(χ), ⟨τ₁ξ, α⟩=0` (genuine (5.5)+(5.2.e) fact;
    残るは family `{R(χᵢ)}` への結合のみ) に置換し, 両者を内部導出。

**Round 23 PASS 1 後の残 (この round 範囲外)**: `retarget_isCoherent_of_decompositions` に残る
posited-conclusion 系仮説は **`hY : Da.Y = a·Da.tau1 χ₁` ((5.6.2) collapse 出力) ただ 1 つ**。これは
(5.6.1) の `Y` を基底 `{χᵢ^{τ₁}} ∪ {直交補}` に展開した form (= (5.6.1) 存在主張, projection 存在を要する)
を `lambda_eq_zero_and_Z_eq_zero` (landed) に流して得る。残は: ① 各 step の `D₀`/`Da` 生産 ((5.4)
auxiliary isometry `D.tau1` を Dade τ + running τ₁ から構成), ② (5.6.1) form の存在 (Y の R(χ)/{χᵢ^τ₁}
分解), ③ `hperElem` の family `{R(χᵢ)}` 結合 ((5.2.e) を extension 像へ)。①②③ が揃えば hstep 完全放電。

### G2.7 Round 23 PASS 2 (2026-05-31): residual (b) `hperElem` を per-member (5.5)+(5.2.e) data から完全構成

PASS 1 末尾の残 ③ (`hperElem` の family `{R(χᵢ)}` 結合) を解消。`hperElem` は
`retarget_isCoherent_of_decompositions` の **最後の image-side opaque 仮説**だったが, honest per-member
(5.5)+(5.2.e) data から *構成* (posit せず) できるようになった。これは mmd L77 一行
「χᵢ^{τ₁} is orthogonal to R(χ) by (5.5) and (5.2.e)」を members → ℤ[S₁] へ lift したもの (sorry/axiom 無,
AxiomsCheck 4 件 新規 全 allowlist; `lake build OddOrder`/`OddOrder.AxiomsCheck` 緑 3343 jobs; commit 8c48fe7)。

- `CharacterPsiDecomposition.inner_X_orthogonal_imageSet_of_orthogonal` : (5.2.e) feed。
  `X = D.X ∈ ℤ[R(χ')]` が `R(χ')⊥R(χ)` (`D.imageFamily.Orthogonal R₀`) なら 各 `α∈R(χ)` と直交。
  `⟨X,α⟩ = ∑ coeff·⟨β,α⟩ = 0` (`X_eq` + `inner_sum_left` + `Orthogonal.inner_eq_zero`)。
  PASS 1 の `inner_X_eq_zero_of_orthogonal_imageSet` の双対 (左因子が X, 右が外部 family R₀ の元)。
- `inner_extension_member_orthogonal_imageSet` : per family member `χ'∈S₁`。その ψ=0 decomposition
  `D'` (⟹ `χ'^{τ₁'}=D'.X` by (5.5), `eq_sum_of_psi_eq_zero`) + `R(χ')⊥R(χ)` (5.2.e) + running
  agreement `D'.tau1 χ'=hS₁.extension χ'` から `⟨hS₁.extension χ', α⟩ = ⟨D'.tau1 χ', α⟩ = ⟨D'.X, α⟩ = 0`。
- `inner_extension_orthogonal_imageSet_of_members` : span induction (`mem`/`zero`/`add`/`smul`) で
  per-member 直交性を全 `ξ∈ℤ[S₁]` へ lift。extension の ℤ-線形性 (`map_zsmul`) + `⟨·,α⟩` の
  ℤ-線形性 (`inner_add_left`/`inner_smul_left` via `Int.cast_smul_eq_zsmul`)。
- `retarget_isCoherent_of_decompositions_and_memberFamily` : **完全** (5.6.3) per-step adjoining で
  `hperElem` も内部放電。`hperElem` を per-member family `{Dmem, hmemOrtho, hmemTau1}` で置換し
  上 2 lemma で導出 → `retarget_isCoherent_of_decompositions` に委譲。**(5.6.3) の image-side 入力が
  全て genuine Dade-map / running-extension fact に帰着** — coupling は一切 posit されない。

**Round 23 PASS 2 後の残 (image-side (b)+(c) は完了)**: 残るは **source-side のみ** — ① `hY : Da.Y =
a·Da.tau1 χ₁` ((5.6.2) collapse 出力; (5.6.1) λ-form の cross-difference 計算を landed
`lambda_eq_zero_and_Z_eq_zero` に流す本体), ② 各 step の `D₀`/`Da`/`Dmem` 生産 ((5.4) auxiliary isometry
`D.tau1` を Dade `τ` と supported-diff 上で一致させる構成)。①② は wiring でなく (5.4)/(5.6.1) 本体 content。
これらが揃えば (6.6) `peterfalvi_66_coherence_of_X` の `hstep` が Dade isometry から完全放電。

### G2.8 Round 24 PASS 1 (2026-05-31): source-side ① `hY` producer を (5.6.1) λ-form から完全構成

Round 23 PASS 2 末尾の source-side 残 ① (`hY : Da.Y = a·Da.tau1 χ₁` の生産) を解消。これまで `hY` は
`X_eq_tau1_chi_of_Y_eq` / `image_eq_of_decomposition` / `retarget_isCoherent_of_decompositions[_and_memberFamily]`
の 4 箇所で **消費** されるが, どこからも **生産** されていなかった (= source-side の唯一の posited-conclusion)。
これを (5.6.1) λ-form + landed `lambda_eq_zero_and_Z_eq_zero` から *構成* (posit せず)。sorry/axiom 無
(`#print axioms` = propext/Classical.choice/Quot.sound のみ), AxiomsCheck 1 件 新規 全 allowlist;
`lake build OddOrder` 緑 3360 jobs / `OddOrder.AxiomsCheck` 緑 3343 jobs。

- `CharacterPsiDecomposition.Y_eq_nsmul_tau1_of_lambdaForm` : (5.6.1)→(5.6.2) の `Y`-collapse 本体。
  入力 = (5.6.1) λ-form `hYform : D.Y = (a:ℂ)•χ₁^{τ₁} − (lam:ℂ)•∑ᵢ(rcᵢ:ℂ)•vcᵢ + Z`
  (`vc i = χᵢ^{τ₁}`, `vc i₁ = D.tau1 χ₁`, `rc i = aᵢ/‖χᵢ‖²`, `mc i = ‖χᵢ‖²`), 直交 gram `horth`,
  `Z` の family 直交性 `hZ`, 教科書仮説 `hψ` (‖ψ‖²=a²‖χ₁‖²) / `hr₁` (a₁=1 ⟹ rc·mc=1) / `hD`
  (degree (c) `2a < ∑(aᵢ/‖χᵢ‖²)²‖χᵢ‖²`)。本体: ① λ-form を capstone の pointwise-coeff form
  `∑ᵢ(a[i=i₁]−λrcᵢ)•vcᵢ + Z` に bridge (`sub_smul`/`Finset.sum_sub_distrib`/`Finset.sum_ite_eq'`/
  `Finset.smul_sum` + `module`), ② `lambda_eq_zero_and_Z_eq_zero` で λ=0 ∧ Z=0, ③ λ-form に戻し
  `(a:ℂ)•χ₁^{τ₁} = a•χ₁^{τ₁}` (`Nat.cast_smul_eq_nsmul`) → `D.Y = a • D.tau1 χ₁` (= `hY`)。

**Round 24 PASS 1 後の残 (source-side ① 完了)**: 残るは source-side ② のみ — 各 step の `D₀`/`Da`/`Dmem`
**instance 生産** ((5.4) auxiliary isometry `D.tau1` を Dade `τ` + running `τ₁ = hS₁.extension` から構成し,
τ₁-image を `OrthonormalCharacterImageFamily R(χ)` に projection して X−Y split を作る; (5.6.1) λ-form
`hYform` 自体の供給も含む)。これは projection infra ((5.6.1) の Y 分解存在 = 有限正規直交族への直交射影) を
要し, PASS 2 の対象。② が揃えば (6.6) `peterfalvi_66_coherence_of_X` の `hstep` が Dade isometry から
完全放電し, coherence-of-X が実 Dade isometry で instantiable。

### G2.9 Round 24 PASS 2 (2026-05-31): integral 直交射影 primitive + ofProjection 構成子

PASS 1 末尾の source-side ② のうち **projection infra (有限 ZIrr-正規直交族への整数係数直交射影)** を解消し,
D₀/Da 生産を「Dade R(χ) 抽出 + τ₁ isometry 拡張」の 2 primitive に縮約する seam を landed。sorry/axiom 無
(`#print axioms` = propext/Classical.choice/Quot.sound のみ), AxiomsCheck 2 件 新規 全 allowlist;
`lake build OddOrder` 緑 3360 jobs / `OddOrder.AxiomsCheck` 緑 3343 jobs。

- `ClassFunction.exists_intProjection_of_orthonormal_ZIrr` (InducedCharacter.lean) : **整数係数直交射影**
  本体。`φ ∈ ZIrr G` + 有限 ZIrr-正規直交族 `R` (`∀α∈R, α∈ZIrr G` + orthonormal) から *整数* 係数
  `c α = ⟨φ,α⟩` (整数性は `inner_mem_ZIrr_int` ← R⊆ZIrr) + 直交残差 `Y = φ − ∑c•α ⊥ R` を生産。
  `φ = (∑c•α) + Y`, `⟨Y,α⟩ = ⟨φ,α⟩ − ⟨X,α⟩ = c α − c α = 0` (orthonormal coeff recovery)。
  これが (5.4)/(5.5)/(5.6.1) の **X-side (整数 ℤ[R(χ)]) / Y-side / coeff** を供給する genuine primitive。
  係数整数性 (signed-irreducible family R(χ) ⊆ ZIrr 上) が load-bearing, Y 直交性は純線型代数。
- `CharacterPsiDecomposition.ofProjection` (S07) : **smart constructor**。`CharacterPsiDecomposition`
  の hard 6 fields (`X`/`Y`/`tau1_image`/`coeff`/`X_eq`/`Y_orthogonal`) を 単一 number-theoretic input
  `htau1_mem : (χ−ψ)^{τ₁} ∈ ZIrr G` から上 projection で *計算* 供給。`X := ∑c•α`,
  `Y := −((χ−ψ)^{τ₁} − X)` で `tau1_image : (χ−ψ)^{τ₁} = X − Y` は純 algebra (`sub_neg_eq_add; abel`)。
  残 input = structural data のみ: `imageFamily` (R(χ); Dade data / §3 keystone),
  `tau1`+`htau1_isom`+`htau1_agrees` ((5.4) auxiliary isometry), 3 直交スカラー
  `⟨χ,ψ⟩=⟨χ̄,ψ⟩=⟨χ,χ̄⟩=0`。`htau1_mem` は IntegralCharacterMap の ℤ-線型性からは導けない genuine input
  (nominal "integral"; 実 Dade map / 拡張のみが ZIrr→ZIrr; carried property)。

**Round 24 PASS 2 後の残 (projection infra 完了)**: D₀/Da/Dmem 完全生産に残る 2 primitive は純構成 (本 round
範囲外, projection は seam として landed):
1. **Dade R(χ) 抽出**: `dadeIntegralCharacterMap` から各 χ∈S₁∪{χ} の `OrthonormalCharacterImageFamily`
   を読み出す (irreducible は `characterDifferenceImageOfIsometry` + `toOrthonormalImage`;
   reducible は Thm 4.9 経由)。
2. **τ₁ isometry 拡張**: 非実 χ で `χ−χ̄` の像を 2 次元格子 `ℤ[χ,χ̄]` 上の full isometry に拡張し
   τ (Dade) と差で, running τ₁ = hS₁.extension と S₁ で一致させる構成 (2D Gram–Schmidt; ZIrr→ZIrr 保存
   = `ofProjection` の `htau1_mem` 供給)。これは from-scratch isometry-extension primitive で未実装。

1+2 が揃えば `ofProjection` で D₀/Da/Dmem 完成 → `Y_eq_nsmul_tau1_of_lambdaForm` (PASS 1) で `hY`,
`retarget_isCoherent_of_decompositions_and_memberFamily` で (6.6) `hstep` 完全放電。

**Round 24 PASS 2 (final) (2026-05-31) — per-step D₀/Da 生産パッケージ + 残の精密化**:
- `CharacterPsiDecomposition.decompositionPair` (S07) : *同一* shared `(R(χ), τ₁, isom, agrees)` +
  2 つの `ZIrr`-membership `(χ−0)^{τ₁}, (χ−a·χ₁)^{τ₁} ∈ ℤ[Irr G]` から `ofProjection` を 2 回呼び
  D₀ (ψ=0) と Da (ψ=a·χ₁) を **同時生産** (`Prod`)。両者 `.tau1` が同一 `tau1` ゆえ
  `Da.tau1 χ = D₀.tau1 χ` は構造的 `rfl` (`decompositionPair_tau1_agree`)。`a·χ₁` 直交性
  `⟨χ, a·χ₁⟩ = a·⟨χ,χ₁⟩ = 0` は nsmul→ℂ-smul 変換 (`Nat.cast_smul_eq_nsmul` + `inner_smul_right`)。
- `retarget_isCoherent_of_sharedDecomposition` (S07) : (5.6.3) per-step coherence entry point。
  shared isometry data を取り pair を内部生産し `htau1_chi` を構造的放電 →
  `retarget_isCoherent_of_decompositions_and_memberFamily` に委譲。`hmemOrtho` は
  `D₀.imageFamily = imageFamily` (definitional; `ofProjection` が `imageFamily := imageFamily`) ゆえ
  `Orthogonal imageFamily` で型整合。残 input は genuine Dade/running-extension facts
  (per-member family Dmem/hmemOrtho/hmemTau1, (5.6.2) collapse hY, 各 agreement)。
  これで per-step「ad-hoc 2 decomposition 供給 + τ₁ 共有 *主張*」義務を除去。

**精密化した唯一の真の残 — global-vs-lattice isometry mismatch (本 round で確定)**: (6.6) hstep の
*完全放電* の唯一の blocker は roadmap が「② τ₁ 2D Gram–Schmidt 拡張」と呼んだもの **だが、その global
版は FT で構成不能 (statement が false)**:
- `CharacterPsiDecomposition.tau1_isometry` は **global** `IsIntegralIsometry tau1`
  (`∀ φ ψ : CF(L), ⟨τ₁φ,τ₁ψ⟩ = ⟨φ,ψ⟩`, CF(L) 全体) を要求。
- だが Dade 等距 (`IsDadeIsometry`/`FullDadeIsometryData`) は **supported subspace `CF(L,A)` 上のみ**
  isometric (`inner_eq : ∀ α β : SupportedClassFunctions A L, …`)。`dadeIntegralCharacterMap` の
  `LinearMap.exists_extend` 拡張は off-support で非等距。
- かつ FT では `dim CF(L) > dim CF(G)` ゆえ **global isometry CF(L)→CF(G) は一般に存在しない**
  (`IsCoherent` docstring S07 L1023 が明言; だから `IsCoherent` は lattice-relative
  `extension_inner_eq` を採用)。`retarget_isIntegralIsometry` (S07 L2023) も *global* τ₁ を要求し
  global を産出する — retarget chain 全体が global 前提。
- 健全な修正: `tau1_isometry` を `ℤ[χ−ψ, χ−χ̄]` 上の **lattice-relative isometry** に弱める。使用は
  `inner_self_chi_eq_sum_coeff` (L904)/`inner_self_chi_add_psi_eq` (L971)/`RetargetTargetPair`
  builder (L1838) の 3 箇所のみ、いずれも差分対 `{χ−ψ,χ−χ̄}` でしか `inner_eq` を使わない (weakening 健全)。
  ただし `CharacterPsiDecomposition` 構造体 + 3 内部証明 + `ofProjection` + `decompositionPair` +
  `retarget_isIntegralIsometry` (+ retarget chain 全体) に cascade する大規模・高リスク refactor で
  別 round 推奨。①Dade R(χ) 抽出は②の lattice-relative 化が前提。

### G2.10 Round 25 (2026-05-31): `tau1_isometry` lattice-relative 化 (Round-13 原理の適用) 完了

上記 Round-24 PASS 2 (final) の「精密化した唯一の真の残 — global-vs-lattice isometry mismatch」を解消。
Round-13 (pass 5, commit b14a987) で `IsCoherent.extension_isometry` を lattice-relative に弱めたのと
**同一の原理** (USER 永続承認) を `CharacterPsiDecomposition.tau1_isometry` に適用。sorry/axiom 無
(`#print axioms` 不変 = propext/Classical.choice/Quot.sound), AxiomsCheck 件数不変 (S07 既存 5 件
全 3 axiom allowlist 内); `lake build OddOrder` 緑 3360 jobs / `OddOrder.AxiomsCheck` 緑 3343 jobs。

- **field 弱化** (S07 構造体 `CharacterPsiDecomposition`):
  `tau1_isometry : IsIntegralIsometry tau1` (global, CF(L) 全体) →
  `tau1_inner_eq_on_support : ∀ φ ζ : CF(L), φ ∈ zSpan {χ, χ.conj, ψ} → ζ ∈ zSpan {χ, χ.conj, ψ} →
  ⟨τ₁ φ, τ₁ ζ⟩ = ⟨φ, ζ⟩`。Round-13 の `extension_inner_eq` と完全並行 (sponsoring lattice が
  S→{χ, χ̄, ψ} に変わるだけ)。FT で `dim CF(L) > dim CF(G)` ゆえ global 等距は一般不在; Dade 等距/
  running extension は supported sublattice `ℤ[χ, χ̄, ψ]` 上でのみ inner 保存 — それが全使用に充分。
- **新規 helper 2 件** (membership cert): `chi_sub_conj_mem_zSpan_support` (`χ−χ̄ ∈ zSpan {χ,χ̄,ψ}`) /
  `chi_sub_psi_mem_zSpan_support` (`χ−ψ ∈ zSpan {χ,χ̄,ψ}`), 各 `Submodule.sub_mem` +
  `Submodule.subset_span (by simp)` の 4 行。
- **blast radius 実測 (前 note の見積りを訂正)**: field アクセスは `.inner_eq` 経由 **3 箇所のみ** —
  `inner_self_chi_eq_sum_coeff` (L904, 引数 `(χ−ψ, χ−χ̄)`)/`inner_self_chi_add_psi_eq` (L971, 引数
  `(χ−ψ, χ−ψ)`)/`retargetTargetPair` 内 `hχχbar_equiv_card_R` (L1838, 引数 `(χ−χ̄, χ−χ̄)`)。各 rewrite に
  上 helper を cert として渡すのみ。構造分解・pattern-match 無。
- **`retarget_isIntegralIsometry` は blast radius 外 (前 note の「retarget chain 全体に cascade」は誤り)**:
  S07 L2023 の `retarget_isIntegralIsometry` は struct field を経由せず **standalone global `τ₁` 仮説**
  (`hτ₁ : IsIntegralIsometry τ₁`) を取り global retarget を産む *別系統* で、本 refactor と完全独立・不変。
  global `τ₁` を扱う retarget chain は `CharacterPsiDecomposition.tau1` の lattice-relative 化と直交。
- **constructor 供給**: `ofProjection` は入力 `htau1_isom : IsIntegralIsometry tau1` (global) を保持し
  field を `fun φ ζ _ _ => htau1_isom.inner_eq φ ζ` で供給 (global→lattice は健全な特殊化)。
  `decompositionPair`/`retarget_isCoherent_of_sharedDecomposition` の global 入力も変更不要。
- **supply-ability (= Round-24 (ii) per-step D production の構造的 unblock)**: 弱化は field レベルのみ
  ⟹ 構造体に *global isometry を要求する field が皆無* (唯一だった `tau1_isometry` を除去)。よって将来の
  per-step D₀/Da 生産者が `tau1` を **Dade 等距 + running `IsCoherent.extension`** から組む際 (extension は
  lattice-relative `extension_inner_eq` しか証明し得ず global 等距は不在)、`tau1_inner_eq_on_support` を
  直接供給して `CharacterPsiDecomposition` を *手構成* 可能に。`IsCoherent` 自身の構成と完全に並行する形で、
  ②「τ₁ 2D Gram–Schmidt 拡張」を *global ではなく lattice-relative* な達成可能形へ確定した。残 = ①Dade
  R(χ) 抽出 (`dadeIntegralCharacterMap` → `OrthonormalCharacterImageFamily`) のみ。

### G2.10 Round 25 PASS 2 (2026-05-31): constructor 弱化 + supply-ability 橋 + per-step D 生産者

PASS 1 (commit 8577211) は *field* `tau1_inner_eq_on_support` のみ弱化し、constructor の入力は global
`htau1_isom : IsIntegralIsometry tau1` のままだった (上 PASS-1 note の「constructor 供給」参照、`fun φ ζ _ _
=> htau1_isom.inner_eq φ ζ` で global を捨てて field を供給)。**だが「Dade 等距から per-step D を組む」には
constructor 自身が lattice-relative 入力を受理せねばならない** — Dade 等距は global isometry を *供給し得ない*
(supported `CF(L,A)` 上のみ isometric, FT で `dim CF(L) > dim CF(G)`)。PASS 2 でこの最後のギャップを解消し、
Round-24 (ii) per-step `(D₀, Da)` production を **実 Lean で**閉じた。sorry/axiom 無; full
`lake build OddOrder` / `OddOrder.AxiomsCheck` 緑; 新規 3 定義全 3 axiom allowlist 内。

- **constructor cascade** (S07): `ofProjection` / `decompositionPair` / `decompositionPair_tau1_agree` /
  `retarget_isCoherent_of_sharedDecomposition` の `htau1_isom : IsIntegralIsometry tau1` 入力を
  lattice-relative `htau1_inner_eq : ∀ φ ζ ∈ zSpan {χ, χ̄, ψ}, ⟨τ₁ φ, τ₁ ζ⟩ = ⟨φ, ζ⟩` に置換。
  `decompositionPair` は 2 つの `ofProjection` 呼出 (`ψ=0`/`ψ=a·χ₁`) を **共有格子 `{χ, χ̄, 0, a·χ₁}`**
  上の 1 つの inner-eq から `Submodule.span_mono` で各 `{χ, χ̄, ψ}` へ特殊化 (これが Dade 等距の供給形:
  supported span 上の 1 つの保存則が全差分生成子を覆う)。`decompositionPair_tau1_agree` の `rfl` 不変。
  外部 caller 0 (`AxiomsCheck` の登録は名前参照ゆえ不変)。
- **supply-ability 橋 (prose でなく実 Lean 証明)** — Dade 基底写像が weakened form を *実際に供給* する証拠:
  - `support_subset_of_mem_zSpan_of_supported` — supported 生成系 `S` の `ℤ[S]` 全体が supported。
    `supportedSubmodule (supportInSubgroup A L)` の `restrictScalars ℤ` が全生成子を含む ⟹
    `Submodule.span_le` で `zSpan S = span ℤ S` を含む。純 `ℤ`-submodule closure。
  - `dadeIntegralCharacterMap_inner_eq_on_supported_span` — (5.1) 基底写像
    `τ = dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData hconj)` が **任意の supported span 上で
    inner 保存**。証明: 元が supported ⟹ `dadeIntegralCharacterMap_apply_of_support` で
    `τ φ = hyp.dadeMap ⟨φ,_⟩`、`IsDadeIsometry.inner_eq` (2.6.a) を `hyp.dadeIsometryData hconj` 経由で
    適用 (`dadeIsometryData_toDadeMap : (hyp.dadeIsometryData hconj).toDadeMap = hyp.dadeMap`, rfl)。
- **per-step D 生産者** `decompositionPairFromDade` (Round-24 (ii) を閉じる): orthonormal `R(χ)` +
  supported `χ, χ̄, a·χ₁` (`0` は `support_zero` で自動) + 2 つの `ZIrr`-membership
  `(χ−0)^τ, (χ−a·χ₁)^τ ∈ ℤ[Irr G]` から `(D₀, Da)` を **基底写像 `τ` から直接構成**。欠けていた
  `htau1_inner_eq` を上記橋で *内部放電* (global 等距仮説なし)。(5.4) 基底ケース `τ₁ = τ` の実体化で、
  `retarget_isCoherent_of_sharedDecomposition` に直接供給可。
- **残 (本パス後)**: 一般 (5.4) `τ₁ ⊋ τ` (running coherence extension への τ₁ 拡張) と ①Dade `R(χ)` 抽出
  (`dadeIntegralCharacterMap` → `OrthonormalCharacterImageFamily`) は別パス。ただし両者とも
  lattice-relative 化が前提で、その前提は本パスで完全除去 — per-step `hstep` を `decompositionPairFromDade`
  + `retarget_isCoherent_of_sharedDecomposition` で組む経路が **型レベルで開通**した。

## Round B (2026-05-31): Dade `R(χ)` extractor + ZIrr-membership (上記残① を閉じる)

`decompositionPairFromDade` が **入力**として要求していた `imageFamily : OrthonormalCharacterImageFamily τ χ`
と 2 つの `ZIrr`-membership を **Dade 等距から構成**。これで per-step `(5.6)` 入力が opaque 仮説ゼロで
実 Dade τ から得られる (基底ケース `τ₁=τ`)。

- **`Hypothesis.one_notMem_dadeSupport`** (S04, support-side keystone): `1 ∉ dadeSupport`。
  `1 ∈ dadeSupport ⟹ IsConj (a·h) 1 ⟹ a·h=1` (`isConj_one_left`) `⟹ a=h⁻¹∈H(a)`; 一方 `a∈C_L(a)`
  (a∈L, 自己可換)、`centralizer_disjoint` ((2.2)) で `a∈H(a)⊓C_L(a)=⊥ ⟹ a=1`、`ne_one` (A⊆G^#) と矛盾。
  vanish-at-1 の土台。
- **`dadeIntegralCharacterMap_apply_one_eq_zero`** (S07): supported φ の Dade 像は `dadeSupport` 外で 0
  (`IsDadeMap.map_eq_zero_of_not_mem_dadeSupport` via `isDadeMap_dadeMap`)、`1 ∉ dadeSupport` ゆえ
  `(φ^τ)(1)=0`。(1.4) `IsometryDifferenceImagesVanishAtOne` を放電。
- **`dadeIntegralCharacterMap_mem_ZIrr_of_supported`** (S07): supported かつ `φ∈ℤ[Irr L]` なら
  `φ^τ∈ℤ[Irr G]` ((2.6.b) `PreservesVirtualCharacters`/`maps_virtualCharacter`、`apply_of_support` で
  `hyp.dadeMap` に移送)。(1.4) `IsometryDifferenceImagesAreVirtual` + `htau1_mem0`/`htau1_mema` 双方を放電。
- **`dadeOrthonormalCharacterImageFamily hyp hconj χ hreal hχsupp hχbarsupp`** (S07, R(χ) extractor):
  χ irreducible 非実 + χ,χ̄ supported から、`conjPairFamily χ=![χ,χ̄]` 上で (1.4) keystone
  `characterDifferenceImageOfIsometry` の 3 仮説を上記で放電 (inner-eq は差が `ℤ[χ,χ̄]` 内ゆえ
  `dadeIntegralCharacterMap_inner_eq_on_supported_span` で供給)、`toOrthonormalImage` で
  `OrthonormalCharacterImageFamily τ χ` を構成。**①Dade `R(χ)` 抽出を実装**。
- **`decompositionPairFromDadeOfIrreducible`** (S07, full assembly): χ irreducible 非実 supported +
  `χ₁∈ℤ[Irr L]` から `R(χ)`・`htau1_mem0`・`htau1_mema` を **すべて内部構成**し `(D₀,Da)` を生産。
  per-step `(5.6)` 入力が opaque 仮説ゼロで実 Dade τ から得られる。
- **残 (Round C)**: `decompositionPairFromDadeOfIrreducible` は基底ケース `τ₁=τ` を構成。running chain では
  τ₁ = `hS₁.extension` (前段 coherence の extension) で、Dade-derived τ と新差分 χ−χ̄ 上で agree することを
  示す (`htau1_agrees`/`himg` を running extension に対し成立させる) のが Round C。それが済めば
  `coherentPairChain` の各 `hstep` が Dade 等距 + 前段 coherence から DISCHARGE され、
  `peterfalvi_66_coherence_of_X` が実 Dade τ で INSTANTIABLE になる。

## Round C (2026-05-31): running-`τ₁` instantiation `retarget_isCoherent_fromDade`

`coherentPairChain` の 1 step `IsCoherent τ S₁ A → IsCoherent τ (S₁∪{χ,χ̄}) A` を **基底写像
`τ = dadeIntegralCharacterMap` を running 補助等距 `τ₁ = τ` *そのもの* として** DISCHARGE する producer。
Round B 残「running τ₁ = hS₁.extension への一般化」を閉じる。要点 = `τ₁ := τ` で
`retarget_isCoherent_of_sharedDecomposition` の 4 agreement を **内部放電**:

- `htau1_agrees`/`htau1_diff` — 共に `rfl` (decomposition の `tau1` field が `τ` そのもの)。
- `htau1_chi1 : τ χ₁ = hS₁.extension χ₁` / per-member `hmemTau1 : (Dmem x).tau1 x = hS₁.extension x` —
  **`IsCoherent.extends_on_supported`** から。running extension は supported sublattice `Z[S₁,A]` 上で
  基底 `τ` と一致し、χ₁ も全 member `x∈S₁` も supported (`hchi1supp`/`hmemSupp`) ゆえ
  `(Dmem x).tau1 x = τ x = hS₁.extension x`。これが「base case `τ₁=τ` を running extension へ一般化」の核心:
  *running extension が新規 τ₁ を必要とせず、`τ` 自身が supported lattice 上の agreement を提供する*。
- `R(χ)` + 2 `ZIrr` facts = Round B; `htau1_inner_eq` = `dadeIntegralCharacterMap_inner_eq_on_supported_span`。
- per-member `Dmem x` も Dade 等距から生産 (`.tau1=τ` を `hmemTau1Base` で保証)。

**残 input** = 真正 (6.6) 文字次数内容 (Dade 等距の責務外): (5.6.2) collapse `hY`、per-member (5.2.e)
image-orthogonality `hmemOrtho`、source orthogonalities、generation `hgen`。これらは (6.6) enumeration が
供給する degree 算術で、本 round の対象外 (roadmap "Residual (post-instantiation)" と一致)。

**`peterfalvi_66_coherence_of_X` 完全 instantiate の到達性**: `hstep` から opaque 補助等距 agreement は
除去済 (B+C)。だが各 step の `hY`/`hmemOrtho`/次数比/`hgen` がなお必要で、これは (6.6) per-step degree
データの threading (別 round)。本 round は `retarget_isCoherent_fromDade` までを landing。

## Round C assembly (2026-05-31): instantiated `peterfalvi_66_coherence_of_X_from_dade`

上記「(6.6) per-step degree データの threading (別 round)」を消化。Round C の per-step engine
`retarget_isCoherent_fromDade` を `coherentPairChain` accumulator 形に組み上げ、(6.6) coherence-of-X を
**実 Dade 等距 `τ = dadeIntegralCharacterMap` で instantiate** する。`hstep` はもはや posit されず、
各 step が Dade 等距 + 前段 coherence からの 1 つの (5.6) adjoining として **構成** される。

3 piece (すべて `S07_Coherence.lean` `DadeBaseMap` section 末尾):

- **`pairUnion_succ_eq_union_pair`** (汎用 set 橋, `pairUnion` 一般 section): `(pair i)=(c₁,c₂)` のとき
  `pairUnion S₀ pair (i+1) = pairUnion S₀ pair i ∪ {c₁,c₂}`。`pairUnion_succ` + `pairSet` の rewrite。
  per-step adjoining engine の `S₁∪{χ,χ̄}` 結論を engine accumulator 形へ接続する connective tissue。

- **`DadeChainStep hyp hconj S₁ A χ`** (構造体): Dade 等距が供給しきった後に残る**真正 (6.6) per-step
  文字次数内容**を field として束ねる *残余 interface*。field = `χ₁`/`a`/`χ` 非実性/`χ,χ̄,a·χ₁` の
  supports/`χ₁∈ℤ[Irr L]`/orthonormality (`hχχ`/`hχbarχbar`/`hχbarχ`/`hχχbar'`)/per-member (5.5)+(5.2.e)
  family (`Dmem`/`hmemTau1Base`/`hmemSupp`/`hmemOrtho`)/source orthogonalities (`hχ_S1`/`hχbar_S1`)/
  `χ₁∈S₁` & supported/(5.6.2) collapse `hY`/(5.1) generation `hgen`。どれも Dade 等距の *image-side*
  構造に触れない (= source-side degree/orthogonality = (6.6) enumeration の責務)。
  - `DadeChainStep.advance`: prior coherence + step から `IsCoherent τ (S₁∪{χ,χ̄}) A` を
    `retarget_isCoherent_fromDade` 1 回で放電 (R(χ) [Round B] / ZIrr [2.6.b] / inner-preservation /
    `τ₁=τ` agreement は内部供給)。
  - `DadeChainStep.chainStepAdvance`: 橋で accumulator 形 `pairUnion S₀ pair (i+1)` へ書き換え。

- **`peterfalvi_66_coherence_of_X_from_dade`** (主定理 = milestone): 上記を `peterfalvi_66_coherence_of_X`
  の `hstep` 引数として chain 上で fold。`τ` を実 Dade map に固定し、各 `i<N` に対し
  `IrreducibleCharacter χᵢ` (`pair i = (↑χᵢ,(↑χᵢ).conj)`) + `DadeChainStep` over `pairUnion S₀ pair i`
  を取る。残 input = enumeration `e`/cover `hcoverIdx`/base coherence `h0`/per-step `hstepData`+`hpairχ`
  のみ。これで **§5/§6 coherence engine が実 Dade τ に対し完全 constructive**。

sorry/axiom 無; `#assert_only_allowed_axioms` 4 新規全 3 axiom allowlist 内; full `lake build OddOrder`
緑 3360 jobs、`OddOrder.AxiomsCheck` 緑。**残 (post-instantiation)**: per-step `DadeChainStep` の構成
(degree 比 `a` の整数性、`hY`/`hgen` の (6.6) 列挙からの供給) は依然 (6.6) degree 算術であり、Dade 等距の
責務外 — これは設計上の正しい境界 (Dade 等距 ↔ (6.6) enumeration の責務分離)。

### `DadeChainStep` source-side fields 放電試行 + (5.6.1) existence-half primitive (2026-05-31)

`DadeChainStep` の source-side fields (`hY`/`hmemOrtho`/`hgen`) を landed pieces で WIRE し
(6.6) coherence-of-X を 真正 (6.6) setup 仮説のみへ帰着する試み。精査で **3 fields いずれも
wiring-size では放電不能**と確定 (各々 真正に新規数学 + interface 拡張を要す)。本 round は
最も基礎的かつ完全 closable な (5.6.1) **existence-half primitive** のみ landing。

- **`exists_orthogonalProjection_of_orthogonal_family`** (`ZIrrFourier.lean`, commit 741e769,
  AxiomsCheck 登録): orthogonal family `vᵢ` (実 gram `δᵢⱼmᵢ`, `mᵢ≠0`) への任意 `w` の射影
  `w = ∑ᵢ(⟨w,vᵢ⟩/mᵢ)•vᵢ + Z`, `Z⊥vⱼ`。純 diagonal Gram 射影 (completeness 不要)。
  (5.6.1) λ-form `Y = a·χ₁^{τ₁} − λ·∑ᵢ(aᵢ/‖χᵢ‖²)·χᵢ^{τ₁} + Z` の **存在半** (step 1)。
  Pythagoras `inner_self_orthogonalSum_add_re` の sibling。
- **各 field の正直な放電障害**:
  - `hY` = `Da.Y = a•Da.tau1 chi1`。tautology ではない。`Y_eq_nsmul_tau1_of_lambdaForm` は `hYform`
    (λ-form) を消費するが producer 不在。core 障害 = **joint-lattice isometry**: 係数計算 (mmd L79)
    `aaᵢ‖χ₁‖² = ((χ−aχ₁)^τ,(χᵢ−aᵢχ₁)^τ)` は `χ−aχ₁` と `χᵢ−aᵢχ₁` を *同時に* 含む格子
    `Z[S₁∪{χ−χ̄,χ−aχ₁}]` 上の等距を要すが `Da.tau1_inner_eq_on_support` は `{χ,χ̄,ψ}` のみ。
    existence-half は landing 済、残 = coefficient-value (`λᵢ=λaᵢ/‖χᵢ‖²`) + integrality (`λ∈ℤ`) +
    joint-等距 transport。
  - `hmemOrtho` = `(Dmem x).imageFamily.Orthogonal R(χ)`。`Dmem` は field (任意データ) ゆえ構成法
    不明では証明不能。放電には `Dmem` も Dade 構成化 (`decompositionPairFromDade…`) + Dade
    `R(x)⊥R(χ)` を `x⊥{χ,χ̄}` から (4.1)型で導く必要。
  - `hgen` = pure module theory ではなく (4.7) `Z[S,L^#]=Z[S,A]` を要す (χ 単体は A 上 supported とは
    限らず `mχ+nχ̄` の support 制約が差 generator 経由の関係を強制)。(4.7) 未形式化・データ外。
- 結論: milestone (真正 (6.6) setup のみへの帰着) は本 round 未到達 (3 fields とも interface 拡張 +
  新規数学)。純益 = existence-half primitive (汎用・再利用可・λ-form の step 1)。
  次 step = (a) `DadeChainStep` に joint-isometry field 追加で coefficient-value + integrality を載せ
  `hY` 放電、(b) (4.7) 形式化で `hgen`、(c) `Dmem` 構成化で `hmemOrtho`。

### (2026-06-04, pass 12) `Y = S(H')` finite representative family and direct coherence bridge

`S08_CoherenceTheorems.lean` に T6/Y-family の representative construction を landing
(sorry/axiom 無; AxiomsCheck 登録):

- `finite_linearCharacters_of_finite`: finite group の linear characters は有限。
- `SibleyDadeHypothesis.Yset_finite`: `Y=S(H')` は非自明 linear source characters の induced image
  に含まれるので有限。
- `SibleyDadeHypothesis.isIrreducibleCharacter_of_mem_Yset`: `Y` member は degree-one source による
  induced irreducible character。
- `SibleyDadeHypothesis.exists_Yset_linearRepresentativeFamily`: `Yset` 自体を finite enumerate し、
  各 `Y` member から `exists_linear_source_of_mem_Yset` で source を選ぶ。これにより exact range、
  all-nontrivial-linear cover、pairwise non-`L`-conjugacy を同時に得る。重要な設計点: 全 nontrivial
  linear characters を先に quotient せず、既に有限な `Yset` を enumerate するので orbit representative
  machinery を追加しない。
- `SibleyDadeHypothesis.coherentYset_of_two_le_ncard`: 上の family を
  `coherentYset_of_pairwiseNonconj` に渡し、T6/Y-family coherence の残入力を
  `2 ≤ hyp.Yset.ncard` へ圧縮。

### 2026-06-04 pass 13: `Y = S(H')` の cardinal lower bound を discharge

`S08_CoherenceTheorems.lean` に `2 ≤ hyp.Yset.ncard` の入力を closed:

- `ClassFunction.induceTerm_conjStar` / `induceSum_conj` / `induce_conj`: 誘導和が複素共役と
  可換する一般 helper。
- `SibleyDadeHypothesis.Yset_nonempty`: `H ≠ 1` かつ nilpotent/solvable から `H/H'` の非自明
  linear character を取り、誘導して `Yset` の元を得る。
- `SibleyDadeHypothesis.Yset_hasNoRealCharacters`: `Yset` member は degree `|W₁| > 1` の既約誘導
  文字なので trivial ではなく、odd order の (1.1) から real でない。
- `SibleyDadeHypothesis.Yset_closedUnderConjugate`: source `θ` を `θ.conj` に替え、
  `characterKernel_conj` と `induce_conj` で `Yset` membership を保つ。
- `SibleyDadeHypothesis.two_le_Yset_ncard`: S07 の
  `two_le_ncard_of_conjugate_closed_of_noReal` に finite/nonempty/closed/no-real を渡す。
- `SibleyDadeHypothesis.coherentYset`: `coherentYset_of_two_le_ncard` の cardinality 仮定を
  内部で `two_le_Yset_ncard` により discharge した T6/Y-family coherence。

### 2026-06-04 pass 14: `X ∪ Y = S` glue adapter

`S08_CoherenceTheorems.lean` に (6.8) capstone 用の純集合 bridge と union adapter を追加:

- `SsubFiltration_subset_S`, `Xset_subset_S`, `Yset_subset_S`
- `disjoint_Xset_SsubFiltration`, `Xset_union_SsubFiltration_eq_S`
- `disjoint_Xset_Yset`, `Xset_union_Yset_eq_S` (`X = S - S(H')`, `Y = S(H')`)
- `SibleyDadeHypothesis.coherentS_of_Xset_commutator_Yset_glued`: caller が case-dependent
  `Xset H'` coherence, agreement, source/image orthogonality, supported-span generation を供給すれば、
  internally constructed `coherentYset` と `S07.coherentUnion_of_glued` で `hyp.CoherenceTarget`
  に retarget する。

残る T6/Y-family 側の実装境界は、case c1/c2 からこの adapter の `X` coherence と
orthogonality/generation 入力を構成すること。

### 2026-06-04 pass 15: Frobenius case `X=S-S(H')` coherence wrapper

`S08_CoherenceTheorems.lean` に (6.8.1) Frobenius alternative 用の `Z=H'` 特殊化を追加:

- `SibleyDadeHypothesis.Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius`
- `SibleyDadeHypothesis.Xset_commutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius`

どちらも既存の generic `Xset_isCoherent_from_*_of_irreducible_X` に対して、`H'≤H`,
`H'⊴L`, `X⊆Irr L` を内部 discharge する adapter。残る入力は `Xset H'` nonempty と各 step の
common-index p-power data のみ。これで c1 側は `coherentS_of_Xset_commutator_Yset_glued` の
`hX` 引数に直接入る形まで圧縮された。

同じ pass で c2/case-A route 用の純集合 bridge も追加:

- `SibleyDadeHypothesis.SsubFiltration_antitone`
- `SibleyDadeHypothesis.Xset_mono`
- `SibleyDadeHypothesis.Xset_commutator_eq_Xset_union_filtrationDiff`

`Z≤H'` なら `X(H') = X(Z) ∪ (S(Z) \\ S(H'))` と分解できる。explorer 偵察でも確認された通り、
case-A irreducibility bridge は central/fpf な小さい `Z` 用であり、`H'` へ直接適用する primitive は
ない。したがって c2 側はこの差分層を coherent に扱う bridge、または教科書どおり (6.8.3) の
最終 upgrade を別途実装する必要がある。

### 2026-06-04 pass 16: `X/Y` source-side orthogonality bridge

`S08_CoherenceTheorems.lean` に `coherentS_of_Xset_commutator_Yset_glued` の source-side
orthogonality input を discharge する bridge を追加:

- `SibleyDadeHypothesis.inner_eq_zero_of_mem_span_of_disjoint_irreducible`: disjoint な
  irreducible character 集合 `X`,`Y` について、`irreducibleCharacter_inner_eq_ite` と
  span induction により `ℤ[X] ⟂ ℤ[Y]` を証明する一般 helper。
- `SibleyDadeHypothesis.inner_span_Xset_Yset_eq_zero_of_irreducible_X`: (6.8) の
  `X=S-S(H')`, `Y=S(H')` に特殊化。`Y` 側 irreducibility は
  `isIrreducibleCharacter_of_mem_Yset`、disjointness は `disjoint_Xset_Yset` から内部供給し、
  caller は `Xset H' ⊆ Irr L` だけ渡せばよい。
- `SibleyDadeHypothesis.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X`: 上の
  source orthogonality bridge を組み込んだ glue variant。

これにより c1/Frobenius route では既存の `isIrreducibleCharacter_of_mem_Xset_of_frobenius` で
source-side orthogonality が自動化される。残 input は `X` coherence, `τ₃` agreement,
image-side orthogonality, supported-span generation。

### 2026-06-04 pass 17: Frobenius c1 glue adapter

pass 16 の source orthogonality bridge を (6.8.1) Frobenius alternative に直接接続:

- `SibleyDadeHypothesis.inner_span_Xset_Yset_eq_zero_of_frobenius`: `hF : IsFrobeniusGroup L H W₁`
  から `Xset H' ⊆ Irr L` を内部生成し、`ℤ[Xset H'] ⟂ ℤ[Yset]` を返す。
- `SibleyDadeHypothesis.coherentS_of_Xset_commutator_Yset_glued_of_frobenius`: caller が
  Frobenius case の `Xset H'` coherence と `τ₃` agreement/image orthogonality/generation を
  与えれば、source orthogonality は `hF` から放電して `hyp.CoherenceTarget` を返す。

これで c1 route の adapter chain は
`Xset_commutator_isCoherent_from_pairUnion..._of_frobenius` →
`coherentS_of_Xset_commutator_Yset_glued_of_frobenius`
の形に整理された。残りは `τ₃` の実構成・agreement、image-side orthogonality、supported-span
generation の case-specific 入力。

### 2026-06-04 pass 18: mixed-inner glue interface

S07/S08 に `himg_ortho` を直接要求しない glue variant を追加。`τ₃` 候補 `ν` が
`ℤ[X] × ℤ[Y]` の mixed inner を保存し、各 side の extension と agree するなら、source-side
orthogonality から image-side orthogonality が従う:

- `S07.image_orthogonal_of_mixed_inner_eq`: `ν = νX` on `ℤ[X]`, `ν = νY` on `ℤ[Y]`,
  `⟨νu,νv⟩=⟨u,v⟩` for `u∈ℤ[X]`, `v∈ℤ[Y]`, and `ℤ[X]⊥ℤ[Y]` から
  `νX(ℤ[X]) ⟂ νY(ℤ[Y])` を導く。
- `S07.coherentUnion_of_glued_of_mixed_inner_eq`: `coherentUnion_of_glued` の variant。
  caller は `himg_ortho` の代わりに mixed inner preservation を渡す。
- `SibleyDadeHypothesis.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_mixed_inner`
  and `_of_frobenius_mixed_inner`: §8 final adapter の corresponding variants。

これで c1 route の残 input は `X` coherence, `τ₃` agreement, mixed inner preservation,
supported-span generation へ整理された。`τ₃` 実構成側は image orthogonality を別途証明する代わりに、
mixed block の inner preservation を示せばよい。


### 2026-06-04 pass 19: generator-level mixed-inner glue interface

S07/S08 に `τ₃` 候補を generator-level data で渡す bridge を追加。pass 18 では
agreement/mixed-inner が `ℤ[X]`/`ℤ[Y]` 上の span-level input だったが、実際の `τ₃` 構成では
まず各 character generator 上で値を定めるため、この pass で span induction を内部化した:

- `S07.mixed_inner_eq_on_zSpan_of_eq_on`: `X × Y` の generator 上で
  `⟨νx,νy⟩=⟨x,y⟩` を確認すれば、`ℤ[X] × ℤ[Y]` 全体の mixed-inner preservation が従う。
- `S07.coherentUnion_of_glued_of_generator_mixed_inner_eq`: generator-level の
  `ν = hX.extension` on `X`, `ν = hY.extension` on `Y`, mixed-inner を受け取り、既存の
  mixed-inner glue に接続する。
- `SibleyDadeHypothesis.coherentS_of_Xset_commutator_Yset_glued_of_irreducible_X_generator_mixed_inner`
  and `_of_frobenius_generator_mixed_inner`: §8 final adapter の generator-level variants。

これで Frobenius/c1 route の `τ₃` 側残 input は、`X` coherence, generator 上の `τ₃` agreement,
generator 上の mixed-inner preservation, supported-span generation に縮約された。span への持ち上げは
caller 側で繰り返さない。


### 2026-06-04 pass 20: Frobenius c1 capstone from X-chain data

S08 に Frobenius/c1 route の capstone adapter を追加。pass 19 では final glue が generator-level
`τ₃` data を受けられるようになったが、caller はまだ `hX : IsCoherent τ (Xset H') A` を別途渡す
形だった。この pass で既存の (6.6) X-chain constructors と final glue を合成した:

- `SibleyDadeHypothesis.coherentS_of_frobenius_pairUnionCommonIndexPrimePowerData_generator_mixed_inner`:
  `Xset_commutator_isCoherent_from_pairUnionCommonIndexPrimePowerData_of_frobenius` で `X` coherence を
  内部構成し、その extension に対する generator-level `τ₃` agreement/mixed-inner/generation から
  `hyp.CoherenceTarget` を返す。
- `SibleyDadeHypothesis.coherentS_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner`:
  base-anchor step package 版。同じ capstone だが sorted-degree facts は step package からではなく
  既存 base-anchor adapter が内部導出する。

これで Frobenius/c1 route の caller-facing input は、`Xset H'` nonempty、各 X-chain step の
common-index p-power data、generator 上の `τ₃` agreement、generator 上の mixed-inner preservation、
supported-span generation に縮約された。`hX` witness 自体は caller が構成しない。


### 2026-06-04 pass 21: Frobenius c1 capstone to S09 Ind-chain data

S08 に S09-facing adapter
`SibleyDadeHypothesis.indChainDecomposition_of_frobenius_pairUnionBaseAnchorCommonIndexPrimePowerData_generator_mixed_inner`
を追加。base-anchor common-index p-power X-chain data と generator-level `τ₃` glue から
`hyp.CoherenceTarget` を内部構成し、`IndChainDecomposition.ofIsCoherent` で §9 の weighted-sum
consumer package へ直接変換する。

これは `hyp.CoherenceTarget` の単なるリネームではなく、§8 の coherence output を §9 の
`ζ_t`/`d_t` chain interface に変換する caller-facing bridge。既存 capstone と同じく `H.Normal`
instance は明示引数で受ける。`card_G0_lower_bound` 側はまだ
`CharacterEstimateData` 構成待ちだが、(6.8) Frobenius/c1 route から (7.10) の Ind-chain consumer への
接続点が明示化された。

### 2026-06-04 pass 22: AxiomsCheck coverage for T7/T8 X-layer wrappers

Explorer pass の指摘に従い、既に landed 済みの S08 T7/T8 X-layer を AxiomsCheck に登録した。
追加した coverage は、`isCharacter_restrict`, kernel-containment support lemmas,
`Xset_eq_irreducible_not_subset_characterKernel` と、Frobenius-specialized direct wrappers
`xMember_characterFacts`, `xMember_diffSupport`, `Xset_closedUnderConjugate`,
`Xset_hasNoRealCharacters`, `xSet_finite`, `xBaseBlock_closedUnderConjugate`,
`two_le_xBaseBlock_ncard`, `xBaseBlock_isCoherent`。

これで downstream S09/c1 callers は `_of_irreducible_X` 版を毎回手で合成するのではなく、
Frobenius hypothesis から出る direct API を axiom-clean 登録済みの入口として参照できる。


### 2026-06-04 pass 23: weighted Ind-chain image normal form

Gibbs explorer pass の候補に従い、`IndChainDecomposition` の §9-facing weighted consumer
algebraを正規化した。既存 `image_weightedDifferenceInput` は
`∑ d_t (χ_t - d_t χ_0)` の展開形だけを返していたが、この pass で
`weightedOutput - (∑ d_t^2) • χ_0` 形と Parseval 版
`weightedOutput - ⟪weightedOutput, weightedOutput⟫ • χ_0` を追加した。

同じ正規化式から `χ_0` 係数も抽出し、
`inner_chi_zero_image_weightedDifferenceInput` と norm 版を登録した。これは S09 の
`BetaDecomp` / `weightedNuSum` 側で、(7.10) の Ind-chain package から scalar coefficient
identity を直接消費するための小さな bridge。全 4 件を `AxiomsCheck` に登録済み。

### 2026-06-04 pass 24: weighted Ind-chain real norm bounds

`IndChainDecomposition` の Parseval identity から、§9 側がそのまま消費できる実数部の不等式を
2 件追加した。`one_le_weightedOutput_inner_self_re` は `d 0 = 1` により
`⟪weightedOutput, weightedOutput⟫.re ≥ 1` を返し、
`inner_chi_zero_image_weightedDifferenceInput_re_nonpos` は norm-normalized な `χ₀` 係数
identity からその実部が非正であることを返す。

これで (7.10) の weighted Ind-chain package から、S09 の scalar coefficient / norm estimate
consumer が等式を再展開せずに符号情報を参照できる。

### 2026-06-04 pass 25: weighted Ind-chain real Parseval forms

`IndChainDecomposition` の complex-valued Parseval identities を、下流の実数不等式で
直接使える real-sum 形にした。`weightedOutput_inner_self_re_eq_sum_sq` は
`⟪weightedOutput, weightedOutput⟫.re = Σ d_t^2` を返し、
`inner_chi_zero_image_weightedDifferenceInput_re_eq_one_sub_sum_sq` は `χ₀` 係数の実部を
`1 - Σ d_t^2` として返す。

前 pass の符号補題はこの精密形を経由するように整理した。これで §9 側の real scalar
coefficient / norm bound consumer が complex cast の展開を持たずに済む。
