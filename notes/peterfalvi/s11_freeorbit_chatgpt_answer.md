> ⚠️ **SUPERSEDED (2026-07-01)**: This free-orbit/exponent route is NOT the path to conjunct c.
> Reading the Coq proof (`PFsection9.v` `typeP_nonGalois_characters` part (c)) showed (9.8.c) is a
> **counting + parity** argument, not a per-`f` free-orbit construction. The clean existence: either
> `Xmu ⊊ Xtheta` (→ witness) or `Xmu = Xtheta` (→ `u = (p-1)^{q-1}` even, contradicting `u` odd).
> This **sidesteps the `ρ(U)=K` number-theory gap entirely**. New plan = issue 1012
> "★ 重大 redirect". The free-orbit machinery below stays green/committed but is off the main path.
> (The verified consult content below remains correct as an *alternative* route, kept for reference.)

# Free-orbit (9.8.c) — ChatGPT Pro consult answer (verified) 2026-07-01

Consult sent (model 最高/Pro) for `θ̄^{w₀}∉U-orbit` strategy. Answer **verified rigorous** (the
counterexample is concrete and correct; Lemma A's W-projection argument is correct; Lemma F's
q-cycle argument is correct). Full transcript: chat "Character Theory Proof Strategy".

## CRITICAL: my current construction is INSUFFICIENT

`θ̄^{w₀}≠θ̄` (fact 2, what `clifford_caseA_exists_char_inertia_hc_not_fixed` gives) **does NOT imply**
`θ̄^{w₀}∉U-orbit`. **Explicit counterexample**: U=C₇, W=C₃ (σxσ⁻¹=x²), p=29, H̄=S₀×S₁×S₂ (each C₂₉),
σ cyclically permutes factors, x acts by scalars (a, a⁴, a²) (a order 7 in F₂₉ˣ). Encode θ̄ by exponents
(1, a³, a): then θ̄^σ≠θ̄ BUT θ̄^σ=θ̄^x ∈ U-orbit. Even I_U(θ̄)=1 here. So the obstruction: `uw₀` may fix θ̄
though `w₀` doesn't. **I need a genuine orbit-separation construction.**

## The clean lemma chain (to formalize)

- **Lemma A (semidirect stabilizer criterion)**: G=U⋊W, U◁G, |W|=q PRIME, w₀≠1. Then
  `I_G(x) ≤ U ⟺ x^{w₀} ∉ x^U` (for the G-action on any G-set X; apply X=Irr(H̄), x=θ̄).
  Proof: x^{w₀}=x^u ⟹ w₀u⁻¹∈I_G(x) with W-image w₀≠1 ⟹ I_G(x)⊄U. Conversely I_G(x)⊄U ⟹ ∃ elt with
  W-component w₀ (q prime → image is all of W) ⟹ x^{w₀}∈x^U. **This IS my reduction's hfree ⟺ I_M(θ₀)≤HU.**
- **Lemma C (direct-product char extensionality)**: χ=ψ ⟺ ∀i, χ|_{S_i}=ψ|_{S_i} (internal direct product).
- **Lemma D/E (component formula + factor-orbit separation)**: (θ̄^u)|_{S_i}=θ_i^u (U preserves S_i),
  (θ̄^w)|_{S_i}=transport_w(θ_{w⁻¹i}) (W permutes). So θ̄^w∈θ̄^U ⟺ ∃u,∀i, transport_w(θ_{w⁻¹i})=θ_i^u.
  **⟹ if ∃i with transport_w(θ_{w⁻¹i}) ∉ U-orbit(θ_i), then θ̄^w∉θ̄^U.**
- **Lemma F (marked-factor construction)**: choose factor chars so the U-orbit-LABEL function
  i↦[θ_i]_U is NONCONSTANT. Since W acts as a q-cycle (q prime) on the q-element index set, a
  nonconstant function is not fixed by any nontrivial w ⟹ θ̄^{w₀}∉θ̄^U ∀w₀≠1 ⟹ I_{U⋊W}(θ̄)≤U.
  Simplest: one marked factor [θ_{i₀}]_U=A, others [θ_i]_U=B≠A.

## Caveat (§7): needs ≥2 U-orbits on Irr(factor)^#

The marked-factor needs **≥2 U-orbit classes** on Irr(S_i)^# ≅ F_pˣ, i.e. **im(U→Aut(S_i))=im(U→F_pˣ)
PROPER** (= u<p-1, where the U-orbits are cosets of im(U)). If U acts transitively (im=F_pˣ), use the
**exponent-vector criterion (Lemma G)**: encode θ̄ by a=(a_i)∈(F_pˣ)^Ω, U-action by ρ:U→(F_pˣ)^Ω,
Δ_w(a)_i:=a_i⁻¹a_{w⁻¹i}. Then θ̄^w∈θ̄^U ⟺ Δ_w(a)∈ρ(U). So need **Δ_{w₀}(a)∉ρ(U)**.
NB: if U acts TRIVIALLY on each factor (C=U, u=1 degenerate) then U-orbit(θ̄)={θ̄} and fact 2 DOES
suffice — but for u>1 (the interesting case) U acts nontrivially and fact 2 fails.

## Redirected plan

1. **Build Lemma A** (semidirect stabilizer ⟺ orbit, q prime) — pure group theory, reusable, clean.
   This connects my reduction's hfree to I_M(θ₀)≤HU directly.
2. **Build Lemma C/D/E** (direct-product char extensionality + factor-orbit separation) — abelian
   char theory on the noncommPiCoprod factor structure (reuse char_eq_on_factors_of_bijective).
3. **Strengthen the construction** to the marked-factor (nonconstant orbit-label) — needs the
   type-P fact that im(U→Aut(S₀)) is proper (≥2 U-orbits, u<p-1) OR the exponent criterion. **Verify
   whether u<p-1 holds in caseA** (if U acts transitively, need Lemma G exponent route).
4. Lemma F → θ̄^{w₀}∉U-orbit = hfree → hcZeta_inertia_ne_top_of_free → conjunct c.

The reduction (hcZeta_inertia_ne_top_of_free, taking hfree) is CORRECT and already built. The work is
discharging hfree via the strengthened construction + Lemma A-F chain.
