module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

@[expose] public section

open Polynomial

namespace DivisionFrontier

/-- Given a divisor with nonzero constant coefficient and one monic degree-`n`
multiple, prescribing the constant coefficient pins that multiple exactly
when the degree deficit is at most one. -/
theorem monic_multiple_unique_iff {K : Type*} [Field K] {m p : K[X]} {n : ℕ}
    (hm : m.coeff 0 ≠ 0) (hp : p.Monic) (hd : p.natDegree = n) (hmp : m ∣ p) :
    (∀ q : K[X], q.Monic → q.natDegree = n → m ∣ q → q.coeff 0 = p.coeff 0 → q = p) ↔
      n ≤ m.natDegree + 1 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  constructor
  · intro hu
    by_contra hn
    have hpos : (m * X).natDegree < p.natDegree := by
      rw [natDegree_mul hm0 X_ne_zero, natDegree_X, hd]
      omega
    let q := p + m * X
    have hqm : q.Monic := by
      show (p + m * X).leadingCoeff = 1
      rw [leadingCoeff_add_of_degree_lt' (degree_lt_degree hpos), hp.leadingCoeff]
    have hqd : q.natDegree = n := (natDegree_add_eq_left_of_natDegree_lt hpos).trans hd
    have hmq : m ∣ q := dvd_add hmp (dvd_mul_right m X)
    have hq0 : q.coeff 0 = p.coeff 0 := by
      simp [q, coeff_mul]
    have heq := hu q hqm hqd hmq hq0
    have he : m * (X : K[X]) = 0 := by
      have he' : p + m * X = p + 0 := heq.trans (add_zero p).symm
      exact add_left_cancel he'
    exact (mul_ne_zero hm0 X_ne_zero) he
  · intro hn q hq hqd hmq hq0
    by_contra hqp
    have hd0 : q - p ≠ 0 := sub_ne_zero.mpr hqp
    obtain ⟨r, hr⟩ := dvd_sub hmq hmp
    have hr0 : r ≠ 0 := by
      rintro rfl
      simpa using hr.symm.trans_ne hd0
    have hr0c : r.coeff 0 = 0 := by
      have he := congrArg (fun t : K[X] => t.coeff 0) hr
      simp [coeff_mul, hq0] at he
      exact he.resolve_left hm
    have hrpos : 0 < r.natDegree := by
      by_contra h
      have he : r.natDegree = 0 := by omega
      exact hr0 (by rw [eq_C_of_natDegree_eq_zero he, hr0c, C_0])
    have hdeg : q.degree = p.degree := by
      rw [degree_eq_natDegree hq.ne_zero, degree_eq_natDegree hp.ne_zero, hqd, hd]
    have hdeglt := degree_sub_lt_left hdeg hq.ne_zero (hq.leadingCoeff.trans hp.leadingCoeff.symm)
    have hndeg := natDegree_lt_natDegree hd0 hdeglt
    rw [hr, natDegree_mul hm0 hr0, hqd] at hndeg
    omega

/-- For an invertible `n`-by-`n` matrix, the determinant and the condition of
being a monic degree-`n` annihilator determine the characteristic polynomial
if and only if the minimal polynomial has degree at least `n - 1`. -/
theorem matrix_charpoly_unique_iff {K : Type*} [Field K] {n : ℕ}
    (A : (Matrix (Fin n) (Fin n) K)ˣ) :
    (∀ q : K[X], q.Monic → q.natDegree = n → aeval A.val q = 0 →
      q.coeff 0 = A.val.charpoly.coeff 0 → q = A.val.charpoly) ↔
    n ≤ (minpoly K A.val).natDegree + 1 := by
  have hm : (minpoly K A.val).coeff 0 ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ := X_dvd_iff.mpr h
    have hev : aeval A.val (minpoly K A.val) = 0 := minpoly.aeval _ _
    rw [hr, map_mul, aeval_X] at hev
    have ha : aeval A.val r = 0 :=
      A.isUnit.mul_left_cancel (hev.trans (mul_zero A.val).symm)
    have hdvd := minpoly.dvd K A.val ha
    have hm0 := minpoly.ne_zero A.val.isIntegral
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hm0 (by simpa using hr)
    have hdeg := natDegree_le_of_dvd hdvd hr0
    rw [hr, natDegree_X_mul hr0] at hdeg
    omega
  have hd := monic_multiple_unique_iff hm A.val.charpoly_monic
    (by simp : A.val.charpoly.natDegree = n) A.val.minpoly_dvd_charpoly
  exact Iff.trans (forall_congr' fun q => by
    have ha : aeval A.val q = 0 ↔ minpoly K A.val ∣ q :=
      ⟨minpoly.dvd K A.val, fun hq => by
        obtain ⟨t, rfl⟩ := hq
        simp [minpoly.aeval]⟩
    rw [ha]) hd

end DivisionFrontier
