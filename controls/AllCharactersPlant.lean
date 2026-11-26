import OAI.RhSiegel.AllCharacters
-- Control for RhSiegel.AllCharacters (G2): the lines marked FAIL must each fail; nothing else may.
-- Each failing example states a near miss and tries to close it with the proof.

-- 1. χ ≠ 1 dropped (the principal character)
example {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), C * (q : ℝ) ^ (-ε) ≤ ‖χ.LFunction 1‖ :=
  RhSiegel.exists_siegel_constant hε -- FAIL
-- 2. q^ε in place of q^(-ε)
example {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → C * (q : ℝ) ^ ε ≤ ‖χ.LFunction 1‖ :=
  RhSiegel.exists_siegel_constant hε -- FAIL
-- 3. ε = 0 allowed (a uniform lower bound, false)
example {ε : ℝ} (hε : 0 ≤ ε) : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → C * (q : ℝ) ^ (-ε) ≤ ‖χ.LFunction 1‖ :=
  RhSiegel.exists_siegel_constant hε -- FAIL
-- 4. the constant made absolute (C = 1 for every ε)
example {ε : ℝ} (hε : 0 < ε) : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → (q : ℝ) ^ (-ε) ≤ ‖χ.LFunction 1‖ :=
  RhSiegel.exists_siegel_constant hε -- FAIL
-- 5. the reduction lemma without χ ≠ 1
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} : haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩; ‖χ.primitiveCharacter.LFunction 1‖ * ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) ≤ ‖χ.LFunction 1‖ :=
  RhSiegel.norm_LFunction_one_ge_primitive (χ := χ) -- FAIL
-- 6. the Euler product bound with δ = 0 (false: ∏_{p | q} (1 − 1/p) → 0 along primorials)
example : ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q → C ≤ ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) :=
  RhSiegel.prod_primeFactors_one_sub_inv_ge le_rfl -- FAIL

-- Positive controls: the true statements, retyped, are accepted.
example {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → C * (q : ℝ) ^ (-ε) ≤ ‖χ.LFunction 1‖ :=
  RhSiegel.exists_siegel_constant hε
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) : haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩; ‖χ.primitiveCharacter.LFunction 1‖ * ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) ≤ ‖χ.LFunction 1‖ :=
  RhSiegel.norm_LFunction_one_ge_primitive hχ
example {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q → C * (q : ℝ) ^ (-δ) ≤ ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) :=
  RhSiegel.prod_primeFactors_one_sub_inv_ge hδ
