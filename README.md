# Determinant recognition for overlapping weighted cycles

For an invertible matrix of dimension n, the determinant does not in general determine the characteristic polynomial among all monic degree-n annihilators. The relevant threshold is the degree of the minimal polynomial, not whether the matrix has simple spectrum. The determinant gives the signed constant coefficient. If a degree-n monic annihilator differs from the characteristic polynomial but has the right constant, the difference is divisible by X times the minimal polynomial, which leaves no room for disagreement when the minimal polynomial has degree at least n−1.

Two weighted cycles give sharp contrasting models. If the two lengths are 2 and 3, each block has nonzero weights but the block spectra can overlap. The entire operator still has minimal polynomial of degree at least 4, with equality when the two normalized products share a center. Its characteristic polynomial is therefore determined. If the lengths are 2 and 6 and the cycle products are u and u³ for nonzero u, a monic degree-eight annihilator and the characteristic polynomial share the same constant term but differ in the coefficient of degree seven. Thus even the trace is not determined there.

More generally, for same-center packets with cycle lengths a and b, the cyclic block polynomials are X^a−z^a and X^b−z^b for nonzero z. Their common-multiple problem is sharp: the signed constant and combined degree distinguish the product precisely when a and b are coprime. The matrix theorems check the boundary on actual cycle matrices, not only on abstract polynomials.

## Motivation and scope

The abstract division argument in [Alpöge's announcement](https://alpo.ge/remark.pdf) has a downstream [Hecke-polynomial matching step](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/ZetaCharacterDivisibility/PDivOne.lean#L51-L72). It uses dense simple spectrum to identify the prescribed annihilator with a characteristic polynomial. The matrix threshold here describes an alternative sufficient test once the determinant is independently known, and gives an explicit obstruction to weakening that test by another degree. This project does not alter the archived proof, check any actual arithmetic monodromy group, or formalize a general reductive-group classification.

Related spectral packet machinery appears in [Larsen, Rowell, and Wang, Lemma 2.1](https://arxiv.org/abs/math/0506025). No priority claim is made for the underlying polynomial facts.

## Verification

Run `lake build` with the pinned Lean and Mathlib revisions. The comparison entry points are `Challenge.lean`, `Solution.lean`, and `comparator.json`. Only the challenge statements are stated with `sorry` for Comparator; the solution proves each claim.
