import Sqrt6KissingBound.CapFraction

/-! The separately stated sine-integral recurrence in the manuscript. -/
namespace Sqrt6KissingBound
noncomputable section

/-- For the actual sine-integral fractions, the recurrence is strict. -/
theorem capFraction_step_strict (n : ℕ) (hn : 2 ≤ n) :
    capFraction n / 6 < capFraction (n + 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := capFraction_step_aux m
  simpa [capFraction, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end
end Sqrt6KissingBound
