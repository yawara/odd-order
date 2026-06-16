# ChatGPT consult — BG Theorem 15.2 step 4 (F(M) = Q·C_M(Q)) reconstruction

Sent 2026-06-16 (lane-g). Math reconstruction gap: mmd L4196-4198 "Prop 1.5(d) yields
F(M)=QC_M(Q)=C_M(Q̄)=C_{M_σ}(Q̄)⊂M_σ". Need the elided derivation, esp. C_M(Q) ⊆ F(M).

## Prompt

I'm formalizing Bender–Glauberman, "Local Analysis for the Odd Order Theorem", Theorem 15.2, in
Lean 4 and need help reconstructing one elided step. Please give a rigorous, self-contained
derivation citing only standard finite solvable group theory.

Setup. G is a minimal simple group of odd order (every proper subgroup is solvable). M is a maximal
subgroup of G. Write sigma = sigma(M) for the relevant prime set and M_sigma = O_sigma(M), the
normal sigma-core of M. We are in the case where M_sigma is NOT nilpotent. Established facts at this
point:
- q is a prime, Q = O_q(M) (largest normal q-subgroup of M), and q is in sigma.
- M_sigma / Q is nilpotent.
- D is a nilpotent complement to Q in M_sigma: M_sigma = QD, Q ∩ D = 1, and gcd(|Q|,|D|) = 1
  (Q is the q-part, D the q'-part of M_sigma); D is isomorphic to M_sigma/Q, hence nilpotent.
- Q0 = C_Q(D) is a proper subgroup of Q (proper because M_sigma is non-nilpotent).
- Qbar := Q/Q0 is a chief factor (a minimal normal subgroup of N_M(Q0)/Q0), an elementary abelian
  q-group, and C_{Qbar}(D) = 1.

Available tool (Bender–Glauberman Proposition 1.5(d)). If A is a coprime operator group on a
solvable group X (so gcd(|A|,|X|)=1) and H is an A-invariant normal subgroup of X, then
C_{X/H}(A) is the image of C_X(A) in X/H.

Claim to reconstruct (verbatim from the text). "Since D is nilpotent, but M_sigma is not,
Proposition 1.5(d) yields F(M) = Q C_M(Q) = C_M(Qbar) = C_{M_sigma}(Qbar), properly contained in
M_sigma." (F(M) = Fitting subgroup of M.)

My questions (please prove each rigorously and explicitly):
1. Why is F(M) = Q · C_M(Q)? Equivalently, why is C_M(Q) ⊆ F(M)? (I can already show
   F(M) = Q × O_{q'}(F(M)) and O_{q'}(F(M)) ⊆ C_M(Q); the gap is the reverse inclusion
   C_M(Q) ⊆ F(M).)
2. Why C_M(Q) = C_M(Qbar)?
3. Why C_M(Qbar) = C_{M_sigma}(Qbar), i.e. why does centralizing Qbar force an element of M into
   M_sigma?
4. How exactly is Proposition 1.5(d) applied (which group X, operator group A, normal subgroup H)?

Please name the standard facts you use (coprime action, the P×Q lemma / Thompson's lemma, Fitting
subgroup properties, the self-centralizing property C_M(F(M)) ⊆ F(M) for solvable M, etc.), at the
level of detail needed to formalize the argument.

## Answer

(pending)
