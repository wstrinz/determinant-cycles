module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

@[expose] public section

open Polynomial

namespace DivisionFrontier

universe u

/-- The permutation with a 2-cycle and a 6-cycle on disjoint coordinates. -/
def cycle26 : Equiv.Perm (Fin 8) :=
  { toFun := ![1, 0, 3, 4, 5, 6, 7, 2]
    invFun := ![1, 0, 7, 2, 3, 4, 5, 6]
    left_inv := by intro i; fin_cases i <;> decide
    right_inv := by intro i; fin_cases i <;> decide }

open scoped Matrix

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
/-- On a weighted 2+6 generator coset with equal normalized cycle products, the
monic degree-eight annihilator with prescribed determinant need not have the
correct trace coefficient. -/
theorem cycle26_weighted_determinant_does_not_pin_trace {K : Type u} [instField : Field K]
    (w : Fin 8 → K) (u : K) (hu : u ≠ 0) (hsmall : w 0 * w 1 = u)
    (hlarge : w 2 * w 3 * w 4 * w 5 * w 6 * w 7 = u ^ 3) :
    let A : Matrix (Fin 8) (Fin 8) K := Matrix.diagonal w * cycle26.permMatrix K
    A.det ≠ 0 ∧ Matrix.trace A = 0 ∧
      ∃ P : K[X], P.Monic ∧ P.natDegree = 8 ∧ aeval A P = 0 ∧
        P.coeff 0 = A.det ∧ P.coeff 7 = 1 := by
  dsimp only
  let A : Matrix (Fin 8) (Fin 8) K := Matrix.diagonal w * cycle26.permMatrix K
  change A.det ≠ 0 ∧ Matrix.trace A = 0 ∧
    ∃ P : K[X], P.Monic ∧ P.natDegree = 8 ∧ aeval A P = 0 ∧
      P.coeff 0 = A.det ∧ P.coeff 7 = 1
  have hstep (v : Fin 8 → K) (i : Fin 8) : (A *ᵥ v) i = w i * v (cycle26 i) := by
    change ((Matrix.diagonal w * cycle26.permMatrix K) *ᵥ v) i = _
    rw [← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec, Matrix.mulVec_diagonal]
    rfl
  have hrec (k : ℕ) (v : Fin 8 → K) (i : Fin 8) :
      (A ^ (k + 1) *ᵥ v) i = w i * (A ^ k *ᵥ v) (cycle26 i) := by
    rw [pow_succ', ← Matrix.mulVec_mulVec, hstep]
  have hpow : A ^ 6 = u ^ 3 • (1 : Matrix (Fin 8) (Fin 8) K) := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    funext i
    rw [hrec 5, hrec 4, hrec 3, hrec 2, hrec 1, hrec 0, pow_zero,
      Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hsmall3 := congrArg (fun x : K => x ^ 3) hsmall
    have h0 : cycle26 0 = 1 := by decide
    have h1 : cycle26 1 = 0 := by decide
    have h2 : cycle26 2 = 3 := by decide
    have h3 : cycle26 3 = 4 := by decide
    have h4 : cycle26 4 = 5 := by decide
    have h5 : cycle26 5 = 6 := by decide
    have h6 : cycle26 6 = 7 := by decide
    have h7 : cycle26 7 = 2 := by decide
    simp only [Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · change w (0 : Fin 8) * (w (cycle26 (0 : Fin 8)) * (w (cycle26 (cycle26 (0 : Fin 8))) * (w (cycle26 (cycle26 (cycle26 (0 : Fin 8)))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (0 : Fin 8))))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (0 : Fin 8)))))) * (v (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (0 : Fin 8))))))))))))) = u ^ 3 * v 0
      simp only [h0, h1]
      convert congrArg (fun x : K => x * v 0) hsmall3 using 1 <;> ring
    · change w (1 : Fin 8) * (w (cycle26 (1 : Fin 8)) * (w (cycle26 (cycle26 (1 : Fin 8))) * (w (cycle26 (cycle26 (cycle26 (1 : Fin 8)))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (1 : Fin 8))))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (1 : Fin 8)))))) * (v (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (1 : Fin 8))))))))))))) = u ^ 3 * v 1
      simp only [h0, h1]
      convert congrArg (fun x : K => x * v 1) hsmall3 using 1 <;> ring
    · change w (2 : Fin 8) * (w (cycle26 (2 : Fin 8)) * (w (cycle26 (cycle26 (2 : Fin 8))) * (w (cycle26 (cycle26 (cycle26 (2 : Fin 8)))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (2 : Fin 8))))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (2 : Fin 8)))))) * (v (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (2 : Fin 8))))))))))))) = u ^ 3 * v 2
      simp only [h2, h3, h4, h5, h6, h7]
      convert congrArg (fun x : K => x * v 2) hlarge using 1 <;> ring
    · change w (3 : Fin 8) * (w (cycle26 (3 : Fin 8)) * (w (cycle26 (cycle26 (3 : Fin 8))) * (w (cycle26 (cycle26 (cycle26 (3 : Fin 8)))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (3 : Fin 8))))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (3 : Fin 8)))))) * (v (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (3 : Fin 8))))))))))))) = u ^ 3 * v 3
      simp only [h2, h3, h4, h5, h6, h7]
      convert congrArg (fun x : K => x * v 3) hlarge using 1 <;> ring
    · change w (4 : Fin 8) * (w (cycle26 (4 : Fin 8)) * (w (cycle26 (cycle26 (4 : Fin 8))) * (w (cycle26 (cycle26 (cycle26 (4 : Fin 8)))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (4 : Fin 8))))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (4 : Fin 8)))))) * (v (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (4 : Fin 8))))))))))))) = u ^ 3 * v 4
      simp only [h2, h3, h4, h5, h6, h7]
      convert congrArg (fun x : K => x * v 4) hlarge using 1 <;> ring
    · change w (5 : Fin 8) * (w (cycle26 (5 : Fin 8)) * (w (cycle26 (cycle26 (5 : Fin 8))) * (w (cycle26 (cycle26 (cycle26 (5 : Fin 8)))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (5 : Fin 8))))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (5 : Fin 8)))))) * (v (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (5 : Fin 8))))))))))))) = u ^ 3 * v 5
      simp only [h2, h3, h4, h5, h6, h7]
      convert congrArg (fun x : K => x * v 5) hlarge using 1 <;> ring
    · change w (6 : Fin 8) * (w (cycle26 (6 : Fin 8)) * (w (cycle26 (cycle26 (6 : Fin 8))) * (w (cycle26 (cycle26 (cycle26 (6 : Fin 8)))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (6 : Fin 8))))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (6 : Fin 8)))))) * (v (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (6 : Fin 8))))))))))))) = u ^ 3 * v 6
      simp only [h2, h3, h4, h5, h6, h7]
      convert congrArg (fun x : K => x * v 6) hlarge using 1 <;> ring
    · change w (7 : Fin 8) * (w (cycle26 (7 : Fin 8)) * (w (cycle26 (cycle26 (7 : Fin 8))) * (w (cycle26 (cycle26 (cycle26 (7 : Fin 8)))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (7 : Fin 8))))) * (w (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (7 : Fin 8)))))) * (v (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (cycle26 (7 : Fin 8))))))))))))) = u ^ 3 * v 7
      simp only [h2, h3, h4, h5, h6, h7]
      convert congrArg (fun x : K => x * v 7) hlarge using 1 <;> ring
  have htr : Matrix.trace A = 0 := by
    have hfixed : ∀ i : Fin 8, cycle26 i ≠ i := by
      intro i
      fin_cases i <;> decide
    simp [Matrix.trace, Matrix.diag, A, Matrix.diagonal_mul, Equiv.Perm.permMatrix,
      PEquiv.toMatrix, hfixed]
  have hch7 : A.charpoly.coeff 7 = 0 := by
    have h := A.trace_eq_neg_charpoly_coeff
    rw [htr] at h
    simpa using h.symm
  have hdet : A.det ≠ 0 := by
    intro h0
    have hd := congrArg Matrix.det hpow
    simp [Matrix.det_pow, h0] at hd
    exact (pow_ne_zero 8 (pow_ne_zero 3 hu)) hd.symm
  refine ⟨hdet, htr, ?_⟩
  let Q : K[X] := (X ^ 6 - C (u ^ 3)) * X
  let P := A.charpoly + Q
  have hQdeg : Q.natDegree = 7 := by
    have hm : (X ^ 6 - C (u ^ 3) : K[X]).Monic := monic_X_pow_sub_C _ (by decide)
    change (((X ^ 6 - C (u ^ 3)) * X : K[X])).natDegree = 7
    rw [natDegree_mul hm.ne_zero X_ne_zero, natDegree_X_pow_sub_C, natDegree_X]
  have hlt : Q.natDegree < A.charpoly.natDegree := by
    simp [hQdeg]
  have hQann : aeval A Q = 0 := by
    have hAann : aeval A (X ^ 6 - C (u ^ 3)) = 0 := by
      rw [map_sub, map_pow, aeval_X, aeval_C, hpow, Algebra.algebraMap_eq_smul_one, sub_self]
    change aeval A ((X ^ 6 - C (u ^ 3)) * X) = 0
    rw [map_mul, hAann, zero_mul]
  have hMonic : P.Monic := by
    show (A.charpoly + Q).leadingCoeff = 1
    rw [leadingCoeff_add_of_degree_lt' (degree_lt_degree hlt), A.charpoly_monic.leadingCoeff]
  have hPdeg : P.natDegree = 8 := by
    change (A.charpoly + Q).natDegree = 8
    rw [natDegree_add_eq_left_of_natDegree_lt hlt]
    simp
  refine ⟨P, hMonic, hPdeg, ?_, ?_, ?_⟩
  · change aeval A (A.charpoly + Q) = 0
    rw [map_add, hQann, Matrix.aeval_self_charpoly, add_zero]
  · have hd := A.det_eq_sign_charpoly_coeff
    have hc : Q.coeff 0 = 0 := by simp [Q, coeff_mul]
    simp only [P, coeff_add, hc, add_zero]
    simpa only [Fintype.card_fin, Even.neg_pow (by decide : Even 8), one_pow, one_mul] using hd.symm
  · have hc : Q.coeff 7 = 1 := by
      change (((X ^ 6 - C (u ^ 3)) * X : K[X])).coeff (6 + 1) = 1
      rw [coeff_mul_X]
      simp only [coeff_sub, coeff_X_pow_self, coeff_C, ite_eq_right (by decide : (6 : ℕ) ≠ 0), sub_zero]
    simp [P, hch7, hc]

end DivisionFrontier
