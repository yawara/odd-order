/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroupsCoprime

/-!
# Isaacs Chapter 4 — Problem 4D.5 (半直積の導来長)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4D.5 (書籍 p. 146)。

`A` を導来長 `n` の可解群とし, `A` が可換群 `B` に忠実に自己同型で作用して
`(|B|, |A^{(n-1)}|) = 1` とすると, `G = B ⋊ A` の導来長は `n + 1`。

## 主結果

`derivedSeries_semidirectProduct_eq_bot_and_ne_bot`: `A` の導来長がちょうど `m + 1`
(`A^{(m+1)} = 1`, `A^{(m)} ≠ 1`) で `A` が可換群 `B` に忠実に作用し `(|B|, |A^{(m)}|) = 1`
なら, `B ⋊ A` の導来長はちょうど `m + 2` (書籍の `n = m + 1` で「導来長 `n + 1`」)。

* **上界** `derivedSeries_semidirectProduct_eq_bot` — `A^{(n)} = 1` かつ `B` 可換なら
  `(B ⋊ A)^{(n+1)} = 1`。`rightHom : B ⋊ A ↠ A` の核が `inl(B)` であることと,
  可換群 `B` の交換子が自明であることから。**coprime も faithful も不要**。
* **下界** `derivedSeries_semidirectProduct_ne_bot` — `W := ⁅inl(B), inr(V)⁆`
  (`V := A^{(m)}`) が `W = ⁅W, inr(V)⁆` を満たす (Lemma 4.29 の部分群版
  `commutator_commutator_inl_inr_map_eq`) ことから `W ≤ (B ⋊ A)^{(k)}` が `k ≤ m + 1` まで
  押し上がり, 忠実性が `W ≠ 1` を与える。

⚠ 書籍の後半「任意に大きい導来長の可解群が存在する」(正則 wreath 積 `C ≀ A` を使う) は
後続 iteration。
-/

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

section /- Problem 4D.5 (p. 146) -/

variable {A B : Type*} [Group A] [CommGroup B] (φ : A →* MulAut B)

/-- 半直積の導来列は `inl(B)` の中に落ちる: `A^{(n)} = 1` なら `(B ⋊ A)^{(n)} ≤ inl(B)`。

`rightHom : B ⋊ A ↠ A` は `(B ⋊ A)^{(n)}` を `A^{(n)} = 1` へ写すので, 核
`= inl(B)` (`SemidirectProduct.range_inl_eq_ker_rightHom`) に含まれる。 -/
theorem derivedSeries_le_range_inl {n : ℕ} (hA : derivedSeries A n = ⊥) :
    derivedSeries (B ⋊[φ] A) n ≤ (SemidirectProduct.inl : B →* B ⋊[φ] A).range := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  intro x hx
  rw [MonoidHom.mem_ker]
  have hmap : (derivedSeries (B ⋊[φ] A) n).map (SemidirectProduct.rightHom) ≤ derivedSeries A n :=
    map_derivedSeries_le_derivedSeries _ n
  rw [hA, le_bot_iff] at hmap
  have : SemidirectProduct.rightHom x ∈
      (derivedSeries (B ⋊[φ] A) n).map (SemidirectProduct.rightHom) :=
    Subgroup.mem_map_of_mem _ hx
  rw [hmap, Subgroup.mem_bot] at this
  exact this

/-- **Isaacs Problem 4D.5** (上界): `B` が可換で `A` の導来長が `n` 以下なら,
`B ⋊ A` の導来長は `n + 1` 以下。

`(B ⋊ A)^{(n)} ≤ inl(B)` (`derivedSeries_le_range_inl`) と `inl(B)` の可換性から
`(B ⋊ A)^{(n+1)} = ⁅(B ⋊ A)^{(n)}, (B ⋊ A)^{(n)}⁆ ≤ ⁅inl(B), inl(B)⁆ = 1`。
coprime 性も忠実性も使わない。 -/
theorem derivedSeries_semidirectProduct_eq_bot {n : ℕ} (hA : derivedSeries A n = ⊥) :
    derivedSeries (B ⋊[φ] A) (n + 1) = ⊥ := by
  have hle := derivedSeries_le_range_inl φ hA
  have hab : ⁅(SemidirectProduct.inl : B →* B ⋊[φ] A).range,
      (SemidirectProduct.inl : B →* B ⋊[φ] A).range⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨c, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  rw [derivedSeries_succ, ← le_bot_iff, ← hab]
  exact Subgroup.commutator_mono hle hle

/-! ### 下界: `(B ⋊ A)^{(n)} ≠ 1` -/

/-- **Lemma 4.29 の部分群版** (`V ≤ A` に制限した形): `Γ = B ⋊ A` の中で
`⁅⁅inl(B), inr(V)⁆, inr(V)⁆ = ⁅inl(B), inr(V)⁆`。

制限作用 `ψ = φ ∘ V.subtype` の半直積 `Δ = B ⋊[ψ] V` で Γ 形の Lemma 4.29
(`iterCommutator_inl_inr_two_eq_one_of_coprime`) を使い, 埋め込み
`F = SemidirectProduct.map (id B) V.subtype : Δ →* Γ` で押し出す
(`Subgroup.map_commutator` が交換子と可換)。 -/
theorem commutator_commutator_inl_inr_map_eq [Finite A] [Finite B] (V : Subgroup A)
    (hcop : Nat.Coprime (Nat.card ↥V) (Nat.card B)) :
    ⁅⁅(SemidirectProduct.inl : B →* B ⋊[φ] A).range,
        V.map (SemidirectProduct.inr : A →* B ⋊[φ] A)⁆,
      V.map (SemidirectProduct.inr : A →* B ⋊[φ] A)⁆ =
      ⁅(SemidirectProduct.inl : B →* B ⋊[φ] A).range,
        V.map (SemidirectProduct.inr : A →* B ⋊[φ] A)⁆ := by
  set ψ : ↥V →* MulAut B := φ.comp V.subtype with hψ
  set F : B ⋊[ψ] ↥V →* B ⋊[φ] A :=
    SemidirectProduct.map (MonoidHom.id B) V.subtype (fun _ => by ext _; rfl) with hF
  have h29 : ⁅⁅(SemidirectProduct.inl : B →* B ⋊[ψ] ↥V).range,
      (SemidirectProduct.inr : ↥V →* B ⋊[ψ] ↥V).range⁆,
      (SemidirectProduct.inr : ↥V →* B ⋊[ψ] ↥V).range⁆ =
      ⁅(SemidirectProduct.inl : B →* B ⋊[ψ] ↥V).range,
        (SemidirectProduct.inr : ↥V →* B ⋊[ψ] ↥V).range⁆ :=
    iterCommutator_inl_inr_two_eq_one_of_coprime (φ := ψ) hcop
  have hXmap : ((SemidirectProduct.inl : B →* B ⋊[ψ] ↥V).range).map F =
      (SemidirectProduct.inl : B →* B ⋊[φ] A).range := by
    ext x
    constructor
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, by rw [hF, SemidirectProduct.map_inl]; rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨SemidirectProduct.inl b, ⟨b, rfl⟩, by rw [hF, SemidirectProduct.map_inl]; rfl⟩
  have hYmap : ((SemidirectProduct.inr : ↥V →* B ⋊[ψ] ↥V).range).map F =
      V.map (SemidirectProduct.inr : A →* B ⋊[φ] A) := by
    ext x
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨(v : A), v.2, by rw [hF, SemidirectProduct.map_inr]; rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨SemidirectProduct.inr ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩,
        by rw [hF, SemidirectProduct.map_inr]; rfl⟩
  have hmap := congrArg (Subgroup.map F) h29
  simp only [Subgroup.map_commutator, hXmap, hYmap] at hmap
  exact hmap

/-- `V` が `B` に忠実に作用するなら `⁅inl(B), inr(V)⁆ ≠ 1`. -/
theorem commutator_inl_inr_map_ne_bot (hφ : Function.Injective φ) {V : Subgroup A}
    (hV : V ≠ ⊥) :
    ⁅(SemidirectProduct.inl : B →* B ⋊[φ] A).range,
      V.map (SemidirectProduct.inr : A →* B ⋊[φ] A)⁆ ≠ ⊥ := by
  intro hbot
  refine hV (le_bot_iff.mp fun v hv => ?_)
  have hgen : ∀ b : B, ⁅(SemidirectProduct.inl b : B ⋊[φ] A),
      (SemidirectProduct.inr v : B ⋊[φ] A)⁆ = 1 := by
    intro b
    have hmem := Subgroup.commutator_mem_commutator (H₁ :=
      (SemidirectProduct.inl : B →* B ⋊[φ] A).range)
      (H₂ := V.map (SemidirectProduct.inr : A →* B ⋊[φ] A))
      ⟨b, rfl⟩ ⟨v, hv, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hfix : ∀ b : B, (φ v) b = b := by
    intro b
    have h := hgen b
    rw [SemidirectProduct.commutator_inl_inr] at h
    have h' : b * (φ v) b⁻¹ = 1 :=
      SemidirectProduct.inl_injective (h.trans (map_one _).symm)
    have h'' : (φ v) b⁻¹ = b⁻¹ := eq_inv_of_mul_eq_one_right h'
    have h3 : ((φ v) b)⁻¹ = b⁻¹ := by rw [← map_inv]; exact h''
    exact inv_injective h3
  rw [Subgroup.mem_bot]
  have : φ v = 1 := by
    ext b
    exact hfix b
  exact hφ (by rw [this, map_one])

/-- **Isaacs Problem 4D.5** (下界): `V := A^{(m)} ≠ 1` が可換群 `B` に忠実かつ coprime に
作用するなら `(B ⋊ A)^{(m+1)} ≠ 1`。

`W := ⁅inl(B), inr(V)⁆` とおくと `W = ⁅W, inr(V)⁆` (Lemma 4.29 の部分群版) で,
`inr(V) ≤ Γ^{(k)}` (`k ≤ m`; `V = A^{(m)} ≤ A^{(k)}` と `inr` が導来列を保つこと) だから
`W ≤ Γ^{(k)}` が `k ≤ m+1` まで押し上がる。忠実性から `W ≠ 1`。 -/
theorem derivedSeries_semidirectProduct_ne_bot [Finite A] [Finite B]
    (hφ : Function.Injective φ) {m : ℕ}
    (hV : derivedSeries A m ≠ ⊥)
    (hcop : Nat.Coprime (Nat.card ↥(derivedSeries A m)) (Nat.card B)) :
    derivedSeries (B ⋊[φ] A) (m + 1) ≠ ⊥ := by
  set W : Subgroup (B ⋊[φ] A) := ⁅(SemidirectProduct.inl : B →* B ⋊[φ] A).range,
    (derivedSeries A m).map (SemidirectProduct.inr : A →* B ⋊[φ] A)⁆ with hW
  have hWfix : ⁅W, (derivedSeries A m).map (SemidirectProduct.inr : A →* B ⋊[φ] A)⁆ = W :=
    commutator_commutator_inl_inr_map_eq φ (derivedSeries A m) hcop
  have hVk : ∀ k ≤ m, (derivedSeries A m).map (SemidirectProduct.inr : A →* B ⋊[φ] A) ≤
      derivedSeries (B ⋊[φ] A) k := fun k hk =>
    (Subgroup.map_mono (derivedSeries_antitone A hk)).trans
      (map_derivedSeries_le_derivedSeries _ k)
  have hWk : ∀ k ≤ m + 1, W ≤ derivedSeries (B ⋊[φ] A) k := by
    intro k
    induction k with
    | zero => intro _; rw [derivedSeries_zero]; exact le_top
    | succ k ih =>
      intro hk
      rw [derivedSeries_succ, ← hWfix]
      exact Subgroup.commutator_mono (ih (by omega)) (hVk k (by omega))
  intro hbot
  have hle := hWk (m + 1) le_rfl
  rw [hbot, le_bot_iff] at hle
  exact commutator_inl_inr_map_ne_bot φ hφ hV hle

/-- **Isaacs Problem 4D.5**: 導来長ちょうど `m + 1` の可解群 `A` が可換群 `B` に忠実に
自己同型で作用し `(|B|, |A^{(m)}|) = 1` なら, `B ⋊ A` の導来長はちょうど `m + 2`。

書籍の記法では `A` の導来長が `n` (= `m + 1`) のとき `B ⋊ A` の導来長は `n + 1`。 -/
theorem derivedSeries_semidirectProduct_eq_bot_and_ne_bot [Finite A] [Finite B]
    (hφ : Function.Injective φ) {m : ℕ}
    (hAtop : derivedSeries A (m + 1) = ⊥) (hV : derivedSeries A m ≠ ⊥)
    (hcop : Nat.Coprime (Nat.card ↥(derivedSeries A m)) (Nat.card B)) :
    derivedSeries (B ⋊[φ] A) (m + 2) = ⊥ ∧ derivedSeries (B ⋊[φ] A) (m + 1) ≠ ⊥ :=
  ⟨derivedSeries_semidirectProduct_eq_bot φ hAtop,
    derivedSeries_semidirectProduct_ne_bot φ hφ hV hcop⟩

end

end OddOrder.Isaacs.Ch04
