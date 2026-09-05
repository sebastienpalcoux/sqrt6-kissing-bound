import Sqrt6KissingBound

-- The unconditional, manuscript-facing conclusions.
#print axioms Sqrt6KissingBound.kissingConfiguration_card_le_sqrt6_pow
#print axioms Sqrt6KissingBound.kissingNumber_isGreatest
#print axioms Sqrt6KissingBound.kissingNumber_le_sqrt6_pow
#print axioms Sqrt6KissingBound.kissingNumber_two_eq_six
#print axioms Sqrt6KissingBound.sqrt6_isLeast_universalKissingBase
#print axioms Sqrt6KissingBound.supremum_kissing_roots_eq_sqrt6
#print axioms Sqrt6KissingBound.supremum_kissingNumber_roots_eq_sqrt6
#print axioms Sqrt6KissingBound.kissingNumber_universal_base_iff

-- Pin the public conclusions with exactly the geometric hypotheses required.
example {n : ℕ} (hn : 1 ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ n :=
  Sqrt6KissingBound.kissingConfiguration_card_le_sqrt6_pow hn X ⟨hunit, hsep⟩

example {n : ℕ} (hn : 1 ≤ n) :
    (Sqrt6KissingBound.kissingNumber n : ℝ) ≤ (Real.sqrt 6) ^ n :=
  Sqrt6KissingBound.kissingNumber_le_sqrt6_pow hn

example : Sqrt6KissingBound.kissingNumber 2 = 6 :=
  Sqrt6KissingBound.kissingNumber_two_eq_six

example :
    sSup {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧
      r = (Sqrt6KissingBound.kissingNumber n : ℝ) ^ (1 / (n : ℝ))} =
      Real.sqrt 6 := by
  simpa only [one_div] using Sqrt6KissingBound.supremum_kissingNumber_roots_eq_sqrt6

example (α : ℝ) :
    (0 ≤ α ∧ ∀ n : ℕ, 1 ≤ n →
      (Sqrt6KissingBound.kissingNumber n : ℝ) ≤ α ^ n) ↔ Real.sqrt 6 ≤ α :=
  Sqrt6KissingBound.kissingNumber_universal_base_iff α

-- Fail the check if any project declaration depends on an additional axiom.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`Sqrt6KissingBound).isPrefixOf name ||
        name.toString.startsWith "_private.Sqrt6KissingBound." then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in project declaration {name}"
      checked := checked + 1
  if checked == 0 then
    throwError "No project declarations were audited"
  logInfo m!"Axiom audit passed for {checked} project declarations."
