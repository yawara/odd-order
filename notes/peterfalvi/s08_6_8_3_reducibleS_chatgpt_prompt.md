I am formalizing Peterfalvi's "Character Theory for the Odd Order Theorem" (LMS LNS 272) in Lean 4, and I am stuck on a structural question in the proof of Theorem (6.8), specifically step (6.8.3). I need you to clarify exactly what Theorem (5.6) requires and how the (6.8.3) argument works in case (B), so I can decide whether my formalization needs a major generalization. Please reason carefully from the actual structure of Peterfalvi's argument; if you are unsure of a detail, say so explicitly rather than guessing.

SETTING (Peterfalvi 6.8). L = H rtimes W1 with H a nilpotent normal Hall subgroup of the odd-order group L, and W1 a cyclic Hall complement, gcd(|H|,|W1|)=1. There are two cases by (6.8)(c):
 (c1) "Frobenius case": L is a Frobenius group with kernel H and complement W1 (so W1 acts fixed-point-freely on all of H).
 (c2) "certain-type case": Hypothesis (4.6) holds; there is a prime-order subgroup W2 with W2 subset of [H,H], and (in the subcase I care about) W2 is central in H, and C_H(x) = W2 for every nonidentity x in W1.
Let Z be the relevant central subgroup (Z = [H,H] in case A handling, Z = W2 in case B handling). Define:
 S = { Ind_H^L theta : theta in Irr(H), theta not= 1 }  (the base character set, 6.8.b).
 Y = S([H,H]) = the members of S induced from theta trivial on [H,H] (i.e. linear theta). Each such Ind_H^L theta is irreducible of degree |W1| (the eta_j). (6.8.1: Y is coherent.)
 X = S - S(Z). (6.8.2: X union Y is coherent.)
The Dade isometry tau is the coherence map; eta_1 in Y is the anchor of degree |W1|.

THE STEP I AM STUCK ON (6.8.3): "S is coherent." Peterfalvi's proof: suppose S is not coherent. By (6.8.1)+(6.8.2), S not= X union Y, so Z not= H'. There is a set S1, closed under complex conjugation, with X union Y subset S1 subset S, and a pair S2 = {psi, psi-bar} subset S, such that S1 is coherent but S1 union S2 is not. By Theorem (5.6),
   2 psi(1) eta_1(1)  >=  sum over chi in S1 of  chi(1)^2 / ||chi||^2   >   sum over chi in X of chi(1)^2 / ||chi||^2.
By (1.5.c,d), sum over chi in X of chi(1)^2/||chi||^2 = sum over { theta in Irr H : Z not subset Ker theta } |L:H| theta(1)^2 = |L:H|(|H| - |H:Z|) = |W1| |H:Z| (|Z|-1). With psi = Ind_H^L theta of degree |W1| d (theta in Irr H of degree d) and eta_1(1) = |W1|, this gives 2 d |W1|^2 > |W1| |H:Z| (|Z|-1), hence (using Cor 2.30: d^2 <= |H:Z|) 4|W1|^2 > |H:Z|(|Z|-1)^2, and then the fixed-point-free arithmetic gives a contradiction in each case.

MY PROBLEM. In case (B) (certain-type), the set S contains REDUCIBLE characters: for some theta in Irr(H), the induced character Ind_H^L theta is NOT irreducible (it decomposes; these are the "certain-type columns" mu_j, each a sum of several irreducible constituents, and they lie in X = S - S(W2) because W2 is not contained in Ker theta). So the break set S1, which contains X union Y, contains reducible members.

My formalization of Theorem (5.6) (Sibley's coherence bound) currently:
 (i) requires the Frobenius hypothesis "L Frobenius with complement W1" as an input, and
 (ii) in its conclusion enumerates S1 as a finite family of IRREDUCIBLE characters chi_j in Irr(L), and writes the bound as sum chi_j(1)^2 (with ||chi_j||^2 = 1 implicit), with no ||chi||^2 denominator.
So as formalized it does not apply to case (B): S1 has reducible members and there is no Frobenius hypothesis.

MY QUESTIONS (please answer each precisely):

Q1. What does Theorem (5.6) (the Sibley-type coherence bound) in Peterfalvi ACTUALLY require of the coherent set S1 and the pair {psi,psi-bar}? In particular: does (5.6) require the members of S1 to be irreducible, or is it genuinely stated/valid for an arbitrary coherent set of (possibly reducible) characters using the ||chi||^2-weighted sum sum chi(1)^2/||chi||^2? Please state (5.6) as precisely as you can (its hypotheses and conclusion) and identify whether irreducibility of S1's members is essential to its proof or merely a convenient special case.

Q2. Does (5.6) use any Frobenius hypothesis, or is that an artifact? In Peterfalvi the coherence machinery (Section 5, Hypothesis 5.2) is set up abstractly (a set S of characters, an isometry tau, etc.) without assuming L Frobenius. Is Theorem (5.6) Frobenius-free, so that the same (6.8.3) application works verbatim in case (B)?

Q3. The crucial decision question: To run (6.8.3) in case (B), must one apply (5.6) to a coherent set S1 that genuinely contains reducible characters (the columns), thereby requiring the ||chi||^2-weighted version of (5.6)? OR is there a reformulation that applies (5.6) only to an all-irreducible coherent set while still obtaining the lower bound sum over chi in X of chi(1)^2/||chi||^2 = |W1||H:Z|(|Z|-1)? For instance, could one replace each reducible column by its irreducible constituents inside S1, or work with the irreducible constituents of X directly, and still get the same numeric bound? Please be concrete about whether the reducible members can be avoided.

Q4. If the ||chi||^2-weighted (reducible) version of (5.6) is genuinely required, can you outline its statement and proof at the level of detail Peterfalvi uses (Section 5), so I can assess how large the generalization of my irreducible-only formalization would be? In particular, where exactly in the (5.6) proof does the ||chi||^2 weighting enter, and does the proof go through unchanged for reducible chi with ||chi||^2 > 1?

Context for your answer: I want to know whether my formalization can finish (6.8.3) case (B) by a light reformulation (avoiding reducible S1), or whether I must generalize the Section 5 coherence-break machinery to norm-weighted/reducible character sets (a large undertaking). A precise verdict on Q3 is the most important.
