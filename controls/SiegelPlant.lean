import OAI.RhSiegel.Statement
-- Control for RhSiegel: the lines marked FAIL must each fail; nothing else may.
-- Each failing example states a near miss of the node's statement and tries to close it with the proof.

-- 1. ε = 0 allowed (would make |log L(1,χ)| eventually 0)
example : ∀ ε : ℝ, 0 ≤ ε → ∃ Q : ℕ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → Q ≤ q → |Real.log (χ.LFunction 1).re| ≤ ε * Real.log q :=
  RhSiegel.siegel_log_L_one -- FAIL
-- 2. log log q in place of log q (a much stronger, Littlewood-type claim)
example : ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → Q ≤ q → |Real.log (χ.LFunction 1).re| ≤ ε * Real.log (Real.log q) :=
  RhSiegel.siegel_log_L_one -- FAIL
-- 3. the quadratic hypothesis χ ^ 2 = 1 dropped (complex characters)
example : ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → Q ≤ q → |Real.log (χ.LFunction 1).re| ≤ ε * Real.log q :=
  RhSiegel.siegel_log_L_one -- FAIL
-- 4. the nontrivial hypothesis χ ≠ 1 dropped
example : ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ^ 2 = 1 → Q ≤ q → |Real.log (χ.LFunction 1).re| ≤ ε * Real.log q :=
  RhSiegel.siegel_log_L_one -- FAIL
-- 5. lower bound with q^ε in place of q^(-ε)
example (ε : ℝ) (hε : 0 < ε) : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → c * (q : ℝ) ^ ε ≤ (χ.LFunction 1).re :=
  RhSiegel.siegel_lower ε hε -- FAIL
-- 6. a uniform lower bound (ε = 0), which is false (L(1, χ) can be as small as about 1/log log q)
example : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → c ≤ (χ.LFunction 1).re :=
  RhSiegel.siegel_lower 0 le_rfl -- FAIL

-- Positive controls: the true statements, retyped, are accepted.
example : ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → Q ≤ q → |Real.log (χ.LFunction 1).re| ≤ ε * Real.log q :=
  RhSiegel.siegel_log_L_one
example (ε : ℝ) (hε : 0 < ε) : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → c * (q : ℝ) ^ (-ε) ≤ (χ.LFunction 1).re :=
  RhSiegel.siegel_lower ε hε
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hχ2 : χ ^ 2 = 1) : χ.LFunction 1 = ((χ.LFunction 1).re : ℂ) ∧ 0 < (χ.LFunction 1).re :=
  RhSiegel.LFunction_one_real_pos hχ hχ2
example (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → c * ((q : ℝ) + 1) ^ (-ε) ≤ ‖χ.LFunction 1‖ :=
  OAI.LargePrimeGaps.quadratic_siegel hε hε1
