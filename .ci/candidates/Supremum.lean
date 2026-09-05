import Sqrt6KissingBound.KissingNumber

/-! The equivalent supremum formulation of the optimal universal base. -/
namespace Sqrt6KissingBound
noncomputable section

/-- The set of nth roots of kissing numbers, with n ranging over positive integers. -/
def kissingNumberRoots : Set ℝ :=
  {x | ∃ n : ℕ, 1 ≤ n ∧ x = (kissingNumber n : ℝ) ^ ((n : ℝ)⁻¹)}

lemma kissingNumber_root_le_sqrt6 {n : ℕ} (hn : 1 ≤ n) :
    (kissingNumber n : ℝ) ^ ((n : ℝ)⁻¹) ≤ Real.sqrt 6 := by
  calc
    (kissingNumber n : ℝ) ^ ((n : ℝ)⁻¹) ≤
        ((Real.sqrt 6) ^ n) ^ ((n : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) (kissingNumber_le_sqrt6_pow hn) (by positivity)
    _ = Real.sqrt 6 := Real.pow_rpow_inv_natCast (Real.sqrt_nonneg 6) (by omega)

/-- The supremum is already attained in dimension two. -/
theorem sqrt6_isGreatest_kissingNumberRoots : IsGreatest kissingNumberRoots (Real.sqrt 6) := by
  constructor
  · refine ⟨2, by norm_num, ?_⟩
    have htwo : (kissingNumber 2 : ℝ) = (Real.sqrt 6) ^ 2 := by
      rw [kissingNumber_two_eq_six]
      norm_num
    rw [htwo]
    exact (Real.pow_rpow_inv_natCast (x := Real.sqrt 6) (n := 2)
      (Real.sqrt_nonneg 6) (by norm_num)).symm
  · rintro x ⟨n, hn, rfl⟩
    exact kissingNumber_root_le_sqrt6 hn

theorem supremum_kissingNumber_roots_eq_sqrt6 :
    sSup kissingNumberRoots = Real.sqrt 6 :=
  sqrt6_isGreatest_kissingNumberRoots.csSup_eq

end
end Sqrt6KissingBound
