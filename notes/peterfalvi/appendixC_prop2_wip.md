# Peterfalvi App.C Prop 2 (`cyclic_index_two_nearField_classification`) — WIP

**Status (2026-07-21, lane a, carve-out 9204).** The Zassenhaus/Dickson near-field
classification is **committed with 1 remaining sorry** — the center-cardinality clause.
`OddOrder/Peterfalvi/Appendices/NearFields.lean` builds green
(`lake build OddOrder.Peterfalvi.Appendices.NearFields`, exit 0). Prop 2 went from a single
opaque tail-`sorry` to ~350 lines of real proof + 1 focused center `sorry` (no file sorry-count
regression: still 2 total = Prop 1 deferred + center). Everything except the center is sorry-free:
setup, Θ, σ, σ²=1, unit-mult formulas, **field case (DONE)**, B, χ, hBA, `hχσ` (σ preserves
B via `σ(μ a)=μ(y₀⁻¹ a y₀)` — avoids cyclic-uniqueness), TwistData d, mult-transport `hmulΘ`,
near-field iso `hiso`.

Already committed: `card_eq_sq_of_orderTwo_ringAut` (153512c35) + the classification body.

## Proof architecture (all in the one theorem body)

Normalized form (Peterfalvi p.137-138, reconstructed from scrambled OCR
`references/peterfalvi/pdftotext/07.0_pp_137_138_On_Near-Fields.txt`):
near-field mult `x∘y = σ_y(x)·y` (field mult `·`), `y↦σ_y` a hom `F*→Aut(K)` with
**kernel = A** (index 2) in the twisted case; `Θ⁻¹(A) = μ(A) = range μ = B` = the unique
index-2 subgroup of cyclic `Kˣ` (= squares), so `χ` = quadratic character **is** a field-mult hom.

Built (sorry-free) in order:
- `exists_field_semilinear_with_scalar` → `K`, `μ : A →* Kˣ` (scalar realization), σ-family.
- `hμ' : (μ a)•x = x*(a:F)` (scalar clause, near-field form).
- `Θ : K ≃ₗ[K] F` (`a↦a•1`), `hμcoord : Θ(μ a)=(a:F)`, `hμinj`.
- `σ` from semilinearity for a chosen `y₀∉A` (conjugation `c₀=conjNormalMulAut A y₀⁻¹`);
  `hσNF : (a•x)*y₀ = σ a•(x*y₀)`.
- `σ²=1` (via `y₀²∈A` acting as a scalar + `hsmul_inj`).
- `hUmulA`/`hUmulNA` (unit-mult: `id`-semilinear for y∈A, σ-semilinear for y∉A).
- **Field case** (σ=1): F commutative — DONE.
- Twisted case: `B=range μ` index 2, `χ:Kˣ→*Mult(ZMod 2)` via `mulEquivOfPrimeCardEq`
  (order-2 quotient), `hχone : χ u=1 ↔ u∈B`, `hBA : mk0 c∈B ↔ ∃a:A,(a:F)=Θ c`.
- `d : TwistData K := ⟨σ, hσ2, χ, hχσ⟩`, `hmulΘ : Θ a*Θ c = Θ(d.twMul a c)`, `hiso` — DONE.

## The 1 remaining sorry — center (line ~1129): `Nat.card ↥(Subgroup.center Fˣ) = r - 1`

`hχσ` is **DONE** (committed): σ preserves `B=range μ` via `σ(μ a)=μ(y₀⁻¹ a y₀)` (a clean
consequence of the semilinear structure + normality), and σ²=1 gives the reverse — **no
cyclic-uniqueness needed**.

**Center math (worked out, ready to formalize).** Peterfalvi: `x∈Z(F*) ⟺ σ(x)=x ⟺ x∈Fix(σ)`,
so `Z(F*) ≅ (Fix σ)ˣ = 𝔽_r*`, card `r-1`.
- Transport `Fˣ ≃* (Twisted d)ˣ` via the near-field iso `e=Θ.symm` (multiplicative on units),
  so `Z(Fˣ) ≅ Z((Twisted d)ˣ)` (`MulEquiv` maps center to center).
- `(Twisted d)ˣ` = `Kˣ` as a set with group op `twMul`; for units a,c: `twMul a c = σ^{χ(c)}(a)·c`.
- `a ∈ Z ⟺ ∀ c≠0, σ^{χ(c)}(a)·c = σ^{χ(a)}(c)·a`.
  - **a∈Fix σ, a≠0 ⟹ central**: need `χ(a)=0` i.e. `a∈B`. `Fix σ*=𝔽_r*` (order r-1) ⊆ B
    (squares): for `x∈𝔽_r*`, `x^{(r²-1)/2}=(x^{r-1})^{(r+1)/2}=1` (r odd ⟹ (r+1)/2∈ℕ) ⟹ x square.
    Then `twMul a c = a·c` (σ fixes a) and `twMul c a = σ^{χ(a)}(c)·a = c·a = a·c` (χ(a)=0, · comm).
  - **central ⟹ a∈Fix σ**: from c∈B (χ(c)=0): `a·c=σ^{χ(a)}(c)·a` ⟹ (· comm, cancel a)
    `σ^{χ(a)}(c)=c ∀c∈B`. If χ(a)=1 then σ|_B=id ⟹ Fix σ⊇B (|B|=(r²-1)/2 > r=|Fix σ|),
    contradiction ⟹ χ(a)=0. Then from c∉B: `σ(a)·c=c·a=a·c` ⟹ σ(a)=a.
- `|Fix σ| = r`: `Fix σ = FixedPoints.subfield (zpowers σ) K`, `finrank_(Fixσ) K = |⟨σ⟩| = 2`
  (`FixedPoints.finrank_eq_card`), and this is exactly the `r` from `card_eq_sq_of_orderTwo_ringAut`
  (r = |Fix σ|). May need to re-extract r as `|Fix σ|` rather than the opaque obtain, OR relate.
  ⚠ Current `r` comes from `card_eq_sq` obtain (r,p,n with |K|=r²); tie `r=|Fixσ|` via that lemma's
  construction (r there IS `Fintype.card (FixedPoints.subfield (zpowers σ) K)`).

**Route note**: cleanest may be to strengthen `card_eq_sq_of_orderTwo_ringAut` to also return
`r = Nat.card (FixedPoints.subfield (zpowers σ) K)`, so the center clause can use `Z(Fˣ)≅Fixσˣ`
and `|Fixσ|=r` directly. Then `Nat.card (Fixσ)ˣ = |Fixσ|-1 = r-1` (`Nat.card_units`).

## Next session
Finish (1) then (2) in `NearFields.lean`, rebuild leaf, then the theorem is sorry-free (file
2→1 sorry, only Prop 1 `rankOne_affine_nearField` remains — deferred, Brauer-Suzuki gated).
Commit as the Prop 2 completion. Wire nothing new into `OddOrder.lean` (leaf already there).
