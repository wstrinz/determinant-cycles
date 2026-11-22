module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Determinant recognition for overlapping weighted cycles

The challenge compares a sharp minimal-polynomial threshold, a two-cycle
coprimality criterion, and a positive and a negative matrix instance.
Only the usual signed constant coefficient is assumed known.
-/

open Polynomial

namespace DivisionFrontier

universe u

variable {K : Type u} [instField : Field K]

def matrix23 {K : Type u} [instZero : Zero K] (a b c d e : K) : Matrix (Fin 5) (Fin 5) K :=
  !![0, a, 0, 0, 0;
     b, 0, 0, 0, 0;
     0, 0, 0, c, 0;
     0, 0, 0, 0, d;
     0, 0, e, 0, 0]

def cycle26 : Equiv.Perm (Fin 8) :=
  { toFun := ![1, 0, 3, 4, 5, 6, 7, 2]
    invFun := ![1, 0, 7, 2, 3, 4, 5, 6]
    left_inv := by intro i; fin_cases i <;> decide
    right_inv := by intro i; fin_cases i <;> decide }

/-- The determinant recognises the characteristic polynomial exactly when the minimal polynomial loses at most one degree. -/
theorem matrix_charpoly_unique_iff {K : Type u} [instField : Field K] {n : ℕ}
    (A : (Matrix (Fin n) (Fin n) K)ˣ) :
    (∀ q : K[X], q.Monic → q.natDegree = n → aeval A.val q = 0 →
      q.coeff 0 = A.val.charpoly.coeff 0 → q = A.val.charpoly) ↔
    n ≤ (minpoly K A.val).natDegree + 1 := by
  sorry

/-- Two same-center cyclic blocks admit determinant recognition exactly for coprime lengths. -/
theorem two_cycle_charpoly_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (z : K) (hz : z ≠ 0) :
    let A : K[X] := X ^ a - C (z ^ a)
    let B : K[X] := X ^ b - C (z ^ b)
    (∀ q : K[X], q.Monic → q.natDegree = a+b → A ∣ q → B ∣ q →
      q.coeff 0 = (A*B).coeff 0 → q = A*B) ↔ Nat.Coprime a b := by
  sorry

/-- The weighted 2+3 matrix has minimal-polynomial degree at least four. -/
theorem matrix23_minpoly_degree {K : Type u} [instField : Field K] (a b c d e : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    4 ≤ (minpoly K (matrix23 a b c d e)).natDegree := by
  sorry

/-- A monic quintic annihilator with the signed determinant constant agrees with the 2+3 characteristic polynomial. -/
theorem matrix23_charpoly_eq_of_annihilator {K : Type u} [instField : Field K] (a b c d e : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (p : K[X]) (hp : p.Monic) (hpn : p.natDegree = 5)
    (haev : aeval (matrix23 a b c d e) p = 0)
    (hp0 : p.coeff 0 = - (matrix23 a b c d e).det) :
    p = (matrix23 a b c d e).charpoly := by
  sorry

/-- Under a shared spectral center the 2+3 minimal-polynomial degree is exactly four. -/
theorem matrix23_minpoly_degree_eq_four {K : Type u} [instField : Field K] (a b c d e z : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : a*b = z^2) (hcde : c*d*e = z^3) :
    (minpoly K (matrix23 a b c d e)).natDegree = 4 := by
  sorry

/-- The 2+6 matrix has a monic degree-eight annihilator with the right constant but the wrong trace coefficient. -/
theorem cycle26_weighted_determinant_does_not_pin_trace {K : Type u} [instField : Field K]
    (w : Fin 8 → K) (u : K) (hu : u ≠ 0) (hsmall : w 0 * w 1 = u)
    (hlarge : w 2 * w 3 * w 4 * w 5 * w 6 * w 7 = u ^ 3) :
    let A : Matrix (Fin 8) (Fin 8) K := Matrix.diagonal w * cycle26.permMatrix K
    A.det ≠ 0 ∧ Matrix.trace A = 0 ∧
      ∃ P : K[X], P.Monic ∧ P.natDegree = 8 ∧ aeval A P = 0 ∧
        P.coeff 0 = A.det ∧ P.coeff 7 = 1 := by
  sorry

end DivisionFrontier
