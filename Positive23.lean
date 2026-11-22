module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination
import NearRegularMatrix

@[expose] public section

open Polynomial

namespace DivisionFrontier

universe u

/-- A weighted permutation matrix with one 2-cycle and one 3-cycle. -/
def matrix23 {K : Type u} [instZero : Zero K] (a b c d e : K) : Matrix (Fin 5) (Fin 5) K :=
  !![0, a, 0, 0, 0;
     b, 0, 0, 0, 0;
     0, 0, 0, c, 0;
     0, 0, 0, 0, d;
     0, 0, e, 0, 0]

private def inv23 {K : Type u} [instField : Field K] (a b c d e : K) : Matrix (Fin 5) (Fin 5) K :=
  !![0, b⁻¹, 0, 0, 0;
     a⁻¹, 0, 0, 0, 0;
     0, 0, 0, 0, e⁻¹;
     0, 0, c⁻¹, 0, 0;
     0, 0, 0, d⁻¹, 0]

private def units23 {K : Type u} [instField : Field K] (a b c d e : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    (Matrix (Fin 5) (Fin 5) K)ˣ where
  val := matrix23 a b c d e
  inv := inv23 a b c d e
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix23, inv23, Matrix.mul_apply, Fin.sum_univ_succ,
        ha, hb, hc, hd, he]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix23, inv23, Matrix.mul_apply, Fin.sum_univ_succ,
        ha, hb, hc, hd, he]

private theorem powers23 {K : Type u} [instField : Field K] (a b c d e : K) :
    (matrix23 a b c d e)^2 =
      !![a*b, 0, 0, 0, 0;
         0, b*a, 0, 0, 0;
         0, 0, 0, 0, c*d;
         0, 0, d*e, 0, 0;
         0, 0, 0, e*c, 0] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix23, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem cubes23 {K : Type u} [instField : Field K] (a b c d e : K) :
    (matrix23 a b c d e)^3 =
      !![0, a*b*a, 0, 0, 0;
         b*a*b, 0, 0, 0, 0;
         0, 0, c*d*e, 0, 0;
         0, 0, 0, d*e*c, 0;
         0, 0, 0, 0, e*c*d] := by
  change (matrix23 a b c d e) ^ ((2 : ℕ) + 1) = _
  rw [pow_succ, powers23]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix23, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Any weighted 2+3 matrix has minimal-polynomial degree at least four. -/
theorem matrix23_minpoly_degree {K : Type u} [instField : Field K] (a b c d e : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    4 ≤ (minpoly K (matrix23 a b c d e)).natDegree := by
  let M := matrix23 a b c d e
  let p := minpoly K M
  by_contra! hn
  change p.natDegree < 4 at hn
  have haev : aeval M p = 0 := minpoly.aeval _ _
  rw [aeval_eq_sum_range' hn, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at haev
  change p.coeff 0 • M^0 + p.coeff 1 • M^1 + p.coeff 2 • M^2 + p.coeff 3 • M^3 = 0 at haev
  rw [pow_zero, pow_one, show M^2 = _ from powers23 a b c d e,
    show M^3 = _ from cubes23 a b c d e] at haev
  have h1 := congrArg (fun f : Matrix (Fin 5) (Fin 5) K => f 2 3) haev
  have h2 := congrArg (fun f : Matrix (Fin 5) (Fin 5) K => f 2 4) haev
  have h0 := congrArg (fun f : Matrix (Fin 5) (Fin 5) K => f 0 0) haev
  have h3 := congrArg (fun f : Matrix (Fin 5) (Fin 5) K => f 0 1) haev
  simp [M, matrix23] at h1 h2 h0 h3
  have hp1 : p.coeff 1 = 0 := h1.resolve_right hc
  have hp2 : p.coeff 2 = 0 := by simpa [hc, hd] using h2
  have hp0 : p.coeff 0 = 0 := by simpa [hp2] using h0
  have hp3 : p.coeff 3 = 0 := by
    simpa [hp1, ha, hb] using h3
  apply minpoly.ne_zero M.isIntegral
  ext i
  change p.coeff i = 0
  by_cases hi : i < 4
  · interval_cases i <;> assumption
  · exact coeff_eq_zero_of_natDegree_lt (show p.natDegree < i by omega)

/-- In the weighted 2+3 cycle, even one common eigenvalue does not leave enough
room for a second monic quintic annihilator with the correct constant term. -/
theorem matrix23_charpoly_eq_of_annihilator {K : Type u} [instField : Field K] (a b c d e : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (p : K[X]) (hp : p.Monic) (hpn : p.natDegree = 5)
    (haev : aeval (matrix23 a b c d e) p = 0)
    (hp0 : p.coeff 0 = - (matrix23 a b c d e).det) :
    p = (matrix23 a b c d e).charpoly := by
  let U := units23 a b c d e ha hb hc hd he
  have hdeg : 5 ≤ (minpoly K U.val).natDegree + 1 := by
    change 5 ≤ (minpoly K (matrix23 a b c d e)).natDegree + 1
    have h := matrix23_minpoly_degree a b c d e ha hb hc hd
    omega
  have hdet := Matrix.det_eq_sign_charpoly_coeff (matrix23 a b c d e)
  rw [Fintype.card_fin] at hdet
  norm_num at hdet
  rw [hdet, neg_neg] at hp0
  exact (matrix_charpoly_unique_iff U).2 hdeg p hp hpn haev hp0

/-- At a common normalized center, the degree bound is attained. -/
theorem matrix23_minpoly_degree_eq_four {K : Type u} [instField : Field K] (a b c d e z : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : a*b = z^2) (hcde : c*d*e = z^3) :
    (minpoly K (matrix23 a b c d e)).natDegree = 4 := by
  refine le_antisymm ?_ (matrix23_minpoly_degree a b c d e ha hb hc hd)
  let q : K[X] := (X + C z) * (X^3 - C (z^3))
  have hba : b*a = z^2 := by rw [mul_comm, hab]
  have hdec : d*e*c = z^3 := by calc
    _ = c*d*e := by ring
    _ = _ := hcde
  have hecd : e*c*d = z^3 := by calc
    _ = c*d*e := by ring
    _ = _ := hcde
  have hq : aeval (matrix23 a b c d e) q = 0 := by
    dsimp [q]
    rw [map_mul, map_add, map_sub, map_pow, aeval_X, aeval_C, aeval_C, cubes23]
    have hscalar (s : K) : algebraMap K (Matrix (Fin 5) (Fin 5) K) s =
      !![s, 0, 0, 0, 0;
         0, s, 0, 0, 0;
         0, 0, s, 0, 0;
         0, 0, 0, s, 0;
         0, 0, 0, 0, s] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.algebraMap_matrix_apply]
    rw [hscalar z, hscalar (z^3)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix23, Matrix.mul_apply, Fin.sum_univ_succ, hab, hba, hcde, hdec, hecd] <;>
      first | (solve | ring_nf) | linear_combination z^2 * hab
  have h1 : (X + C z : K[X]).Monic := monic_X_add_C _
  have h2 : (X^3 - C (z^3) : K[X]).Monic := monic_X_pow_sub_C _ (by decide)
  have hdeg := natDegree_le_of_dvd (minpoly.dvd K _ hq) (h1.mul h2).ne_zero
  have hqd : q.natDegree = 4 := by
    dsimp [q]
    rw [natDegree_mul h1.ne_zero h2.ne_zero, natDegree_X_add_C, natDegree_X_pow_sub_C]
  exact hdeg.trans_eq hqd

end DivisionFrontier
