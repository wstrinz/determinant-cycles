module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.EuclideanDomain
import NearRegularMatrix
import Mathlib.Tactic.Ring

@[expose] public section

open Polynomial

namespace DivisionFrontier

universe u

variable {K : Type u} [instField : Field K]

private theorem cycle_split (z : K) (a b : ℕ) :
    (X ^ (a + b) - C (z ^ (a + b)) : K[X]) =
      X ^ b * (X ^ a - C (z ^ a)) + C (z ^ a) * (X ^ b - C (z ^ b)) := by
  rw [pow_add, pow_add, map_mul]
  ring

private theorem dvd_cycle_split (z : K) (hz : z ≠ 0) (a b : ℕ) (q : K[X])
    (ha : q ∣ X ^ a - C (z ^ a)) :
    q ∣ X ^ (a + b) - C (z ^ (a + b)) ↔ q ∣ X ^ b - C (z ^ b) := by
  rw [cycle_split]
  have h₁ : q ∣ X ^ b * (X ^ a - C (z ^ a)) := dvd_mul_of_dvd_right ha _
  have hunit : IsUnit (C (z ^ a)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hz))
  constructor
  · intro h
    have hd := dvd_sub h h₁
    rw [add_sub_cancel_left] at hd
    exact hunit.dvd_mul_left.mp hd
  · intro h
    exact dvd_add h₁ (hunit.dvd_mul_left.mpr h)

private theorem cycle_common_dvd (z : K) (hz : z ≠ 0) (q : K[X]) (a b : ℕ) :
    (q ∣ X ^ a - C (z ^ a)) ∧ (q ∣ X ^ b - C (z ^ b)) ↔
      q ∣ X ^ (Nat.gcd a b) - C (z ^ (Nat.gcd a b)) := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hb : b = 0
  · subst b
    simp
  by_cases hab : a ≤ b
  · have hsum : a + (b-a) = b := by omega
    have hrec := cycle_common_dvd z hz q a (b-a)
    have hg : Nat.gcd a (b-a) = Nat.gcd a b := by
      conv_rhs => rw [← hsum]
      simp
    rw [hg] at hrec
    refine Iff.trans ?_ hrec
    constructor <;> rintro ⟨h₁,h₂⟩
    · exact ⟨h₁, (dvd_cycle_split z hz a (b-a) q h₁).mp (hsum.symm ▸ h₂)⟩
    · exact ⟨h₁, hsum ▸ (dvd_cycle_split z hz a (b-a) q h₁).mpr h₂⟩
  · have hsum : b + (a-b) = a := by omega
    have hrec := cycle_common_dvd z hz q b (a-b)
    have hg : Nat.gcd b (a-b) = Nat.gcd a b := by
      rw [Nat.gcd_comm a b]
      conv_rhs => rw [← hsum]
      simp
    rw [hg] at hrec
    refine Iff.trans ?_ hrec
    constructor <;> rintro ⟨h₁,h₂⟩
    · exact ⟨h₂, (dvd_cycle_split z hz b (a-b) q h₂).mp (hsum.symm ▸ h₁)⟩
    · exact ⟨hsum ▸ (dvd_cycle_split z hz b (a-b) q h₁).mpr h₂, h₁⟩
termination_by a + b
decreasing_by all_goals omega

/-- The determinant's signed constant recognises the product of two same-center
cycle polynomials, among their monic common multiples of the correct degree,
exactly when the cycle lengths are coprime. -/
theorem two_cycle_charpoly_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (z : K) (hz : z ≠ 0) :
    let A : K[X] := X ^ a - C (z ^ a)
    let B : K[X] := X ^ b - C (z ^ b)
    (∀ q : K[X], q.Monic → q.natDegree = a+b → A ∣ q → B ∣ q →
      q.coeff 0 = (A*B).coeff 0 → q = A*B) ↔ Nat.Coprime a b := by
  classical
  let _ : GCDMonoid K[X] := EuclideanDomain.gcdMonoid _
  dsimp only
  let A : K[X] := X ^ a - C (z ^ a)
  let B : K[X] := X ^ b - C (z ^ b)
  let D : K[X] := X ^ (Nat.gcd a b) - C (z ^ (Nat.gcd a b))
  let M : K[X] := lcm A B
  change (∀ q : K[X], q.Monic → q.natDegree = a+b → A ∣ q → B ∣ q →
    q.coeff 0 = (A*B).coeff 0 → q = A*B) ↔ Nat.Coprime a b
  have hA : A.Monic := monic_X_pow_sub_C _ ha.ne'
  have hB : B.Monic := monic_X_pow_sub_C _ hb.ne'
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
  have hD : D.Monic := monic_X_pow_sub_C _ hg.ne'
  have hM : M ≠ 0 := lcm_ne_zero_iff.mpr ⟨hA.ne_zero,hB.ne_zero⟩
  have hdD : gcd A B ∣ D := (cycle_common_dvd z hz _ a b).mp ⟨gcd_dvd_left _ _, gcd_dvd_right _ _⟩
  have hDg : D ∣ gcd A B := (cycle_common_dvd z hz D a b).mpr (dvd_refl D) |>.elim dvd_gcd
  have hG : gcd A B ≠ 0 := by
    intro h
    rw [h, zero_dvd_iff] at hdD
    exact hD.ne_zero hdD
  have hdegG : (gcd A B).natDegree = Nat.gcd a b := by
    have he := le_antisymm (natDegree_le_of_dvd hdD hD.ne_zero) (natDegree_le_of_dvd hDg hG)
    exact he.trans natDegree_X_pow_sub_C
  have hAB : (A * B).natDegree = a+b := by
    rw [natDegree_mul hA.ne_zero hB.ne_zero]
    congr 1 <;> exact natDegree_X_pow_sub_C
  have hdeg : Nat.gcd a b + M.natDegree = a+b := by
    have hm := GCDMonoid.gcd_mul_lcm A B
    change Associated (gcd A B * M) (A * B) at hm
    have he := le_antisymm (natDegree_le_of_dvd hm.dvd (mul_ne_zero hA.ne_zero hB.ne_zero))
      (natDegree_le_of_dvd hm.symm.dvd (mul_ne_zero hG hM))
    rwa [natDegree_mul hG hM, hdegG, hAB] at he
  have hMP : M ∣ A*B := lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
  have hM0 : M.coeff 0 ≠ 0 := by
    intro h
    obtain ⟨R, hR⟩ := hMP
    have he : (A*B).coeff 0 ≠ 0 := by
      rw [mul_coeff_zero, coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero]
      have h1 : A.eval 0 = -(z^a) := by simp [A, ha.ne']
      have h2 : B.eval 0 = -(z^b) := by simp [B, hb.ne']
      rw [h1,h2]
      exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ hz)) (neg_ne_zero.mpr (pow_ne_zero _ hz))
    rw [hR, mul_coeff_zero, h, zero_mul] at he
    exact he rfl
  have core := monic_multiple_unique_iff hM0 (hA.mul hB) hAB hMP
  refine Iff.trans ?_ (core.trans ?_)
  · constructor
    · intro h q hm hq hd hc
      rcases lcm_dvd_iff.mp hd with ⟨h₁,h₂⟩
      exact h q hm hq h₁ h₂ hc
    · intro h q hm hq h₁ h₂ hc
      exact h q hm hq (lcm_dvd h₁ h₂) hc
  · unfold Nat.Coprime
    omega

end DivisionFrontier
