import OAI.NumberTheory.PrimeGaps.ZeroFreeBounds

/-!
# Siegel's theorem for every nonprincipal Dirichlet character, unconditional

`RhSiegel.exists_siegel_constant`: for every `ε > 0` there is `C > 0` with `C q^(-ε) ≤ ‖L(1, χ)‖` for every modulus
`q` and every nonprincipal Dirichlet character `χ` mod `q` (real or complex, primitive or not).

Ingredients:
* the primitive case is openai/math's `OAI.LargePrimeGaps.nonprincipal_line_lower` (PrimeGaps/ZeroFreeBounds.lean,
  commit `fd4aeeb2`) at `t = 0`: `c ((q+2)(|t|+2))^(-ε) ≤ ‖L(1+it, χ)‖` for primitive `χ ≠ 1`. Its proof is
  Siegel's theorem for quadratic characters (`quadratic_siegel`, the classical ineffective case split) plus the
  3-4-1 inequality for the others. Its import closure is 43 files of `OAI/NumberTheory/PrimeGaps/` and Mathlib;
  it does not touch openai/math's Dirichlet 7/8 development (`OAI/NumberTheory/DirichletL/`) or grh-lean.
* the reduction to the primitive character is new here: Mathlib's `DirichletCharacter.LFunction_changeLevel`
  gives `L(1, χ) = L(1, χ*) ∏_{p | q} (1 − χ*(p)/p)`, and `prod_primeFactors_one_sub_inv_ge` bounds the product
  below by `C q^(-δ)`.

The constant is ineffective (that is a fact about the proof, not a Lean statement).
-/

namespace RhSiegel

open Complex

/-- `∏_{p | q} (1 − 1/p) ≥ C q^(−δ)`: primes below `P` (with `P^δ ≥ 2`) cost at most a factor `1/2` each, the
others satisfy `1 − 1/p ≥ 1/2 ≥ p^(−δ)`, and `∏_{p | q} p ≤ q`. -/
theorem prod_primeFactors_one_sub_inv_ge {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q →
      C * (q : ℝ) ^ (-δ) ≤ ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
  obtain ⟨P, hP⟩ : ∃ P : ℕ, (2 : ℝ) ≤ (P : ℝ) ^ δ := by
    obtain ⟨P, hP⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / δ))
    refine ⟨P, ?_⟩
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / δ)) ^ δ := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne', Real.rpow_one]
      _ ≤ (P : ℝ) ^ δ := Real.rpow_le_rpow (by positivity) hP hδ.le
  refine ⟨(1 / 2 : ℝ) ^ P, by positivity, ?_⟩
  intro q hq
  set S := q.primeFactors
  set h : ℕ → ℝ := fun p => if p < P then 1 / 2 else 1 with hh
  have hfac : ∀ p ∈ S, (p : ℝ) ^ (-δ) * h p ≤ 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) hp2
    have hle1 : (p : ℝ) ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hpos : 0 ≤ (p : ℝ) ^ (-δ) := by positivity
    simp only [hh]
    split_ifs with hlt
    · nlinarith
    · push Not at hlt
      have hpd : (2 : ℝ) ≤ (p : ℝ) ^ δ :=
        hP.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlt) hδ.le)
      have : (p : ℝ) ^ (-δ) ≤ 1 / 2 := by
        rw [Real.rpow_neg (by linarith), one_div]; exact inv_anti₀ (by norm_num) hpd
      linarith
  have hprod_le : ∏ p ∈ S, ((p : ℝ) ^ (-δ) * h p) ≤ ∏ p ∈ S, (1 - (p : ℝ)⁻¹) :=
    Finset.prod_le_prod₀ (fun p _ => mul_nonneg (by positivity) (by simp only [hh]; split_ifs <;> norm_num)) hfac
  rw [Finset.prod_mul_distrib] at hprod_le
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  -- ∏ p^(-δ) ≥ q^(-δ)
  have hA : (q : ℝ) ^ (-δ) ≤ ∏ p ∈ S, (p : ℝ) ^ (-δ) := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    have hS0 : (0 : ℝ) < ∏ p ∈ S, (p : ℝ) :=
      Finset.prod_pos (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    have hSq : ∏ p ∈ S, (p : ℝ) ≤ q := by
      have := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
      rw [← Nat.cast_prod]; exact_mod_cast this
    exact Real.rpow_le_rpow_of_nonpos hS0 hSq (by linarith)
  -- ∏ h ≥ (1/2)^P
  have hB : (1 / 2 : ℝ) ^ P ≤ ∏ p ∈ S, h p := by
    simp only [hh]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    calc (S.filter (fun p => p < P)).card ≤ (Finset.range P).card :=
          Finset.card_le_card (fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = P := Finset.card_range P
  have hBpos : 0 ≤ (1 / 2 : ℝ) ^ P := by positivity
  calc (1 / 2 : ℝ) ^ P * (q : ℝ) ^ (-δ) ≤ (∏ p ∈ S, h p) * ∏ p ∈ S, (p : ℝ) ^ (-δ) :=
        mul_le_mul hB hA (by positivity) (hBpos.trans hB)
    _ = (∏ p ∈ S, (p : ℝ) ^ (-δ)) * ∏ p ∈ S, h p := mul_comm _ _
    _ ≤ _ := hprod_le

/-- Each Euler factor removed when passing to the primitive character has norm at least `1 − 1/p`. -/
theorem norm_one_sub_euler_factor_ge {N : ℕ} (ψ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) :
    1 - (p : ℝ)⁻¹ ≤ ‖1 - ψ p * (p : ℂ) ^ (-(1 : ℂ))‖ := by
  have hnorm : ‖ψ p * (p : ℂ) ^ (-(1 : ℂ))‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, norm_natCast_cpow_of_pos hp.pos]
    simp only [neg_re, one_re, Real.rpow_neg_one]
    have h1 := ψ.norm_le_one (p : ZMod N)
    have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    nlinarith
  have := norm_sub_norm_le (1 : ℂ) (ψ p * (p : ℂ) ^ (-(1 : ℂ)))
  rw [norm_one] at this
  linarith

/-- The reduction to the primitive character: `‖L(1, χ)‖ ≥ ‖L(1, χ*)‖ ∏_{p | q} (1 − 1/p)` for `χ ≠ 1`, where
`χ* = χ.primitiveCharacter` (a character mod the conductor). -/
theorem norm_LFunction_one_ge_primitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    ‖χ.primitiveCharacter.LFunction 1‖ * ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) ≤ ‖χ.LFunction 1‖ := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h]
    exact (DirichletCharacter.changeLevel_eq_one_iff _).mpr rfl
  have hcl := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (s := 1) (Or.inl hprim)
  rw [χ.changeLevel_primitiveCharacter] at hcl
  rw [hcl, norm_mul, norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.prod_le_prod₀
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith
  · intro p hp
    exact norm_one_sub_euler_factor_ge _ (Nat.prime_of_mem_primeFactors hp)

/-- **Siegel's theorem for every nonprincipal Dirichlet character, unconditional.** For every `ε > 0` there is
`C > 0` with `C q^(−ε) ≤ ‖L(1, χ)‖` for every `q` and every nonprincipal `χ` mod `q`. Same statement as
`RestsOnGRH.exists_siegel_constant_onGRH` and `LeanClassics.SiegelUncond.exists_siegel_constant`, with no
hypothesis from grh-lean or openai/math's Dirichlet 7/8 theorem. -/
theorem exists_siegel_constant {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      C * (q : ℝ) ^ (-ε) ≤ ‖χ.LFunction 1‖ := by
  set δ : ℝ := min ε 1 / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by have := min_le_right ε 1; linarith
  have h2δ : 2 * δ ≤ ε := by have := min_le_left ε 1; linarith
  obtain ⟨c, hc, hline⟩ := OAI.LargePrimeGaps.nonprincipal_line_lower hδ hδ1
  obtain ⟨C₁, hC₁, hprod⟩ := prod_primeFactors_one_sub_inv_ge hδ
  refine ⟨c * (6 : ℝ) ^ (-δ) * C₁, by positivity, ?_⟩
  intro q _ χ hχ
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hfq : (χ.conductor : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd hq χ.conductor_dvd_level
  have hprim : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h]
    exact (DirichletCharacter.changeLevel_eq_one_iff _).mpr rfl
  -- primitive bound at t = 0
  have hL := hline χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hprim 0
  simp only [abs_zero, Complex.ofReal_zero, mul_zero, add_zero] at hL
  have hL' : c * (6 : ℝ) ^ (-δ) * (q : ℝ) ^ (-δ) ≤ ‖χ.primitiveCharacter.LFunction 1‖ := by
    refine le_trans ?_ hL
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) hq0.le]
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    linarith
  have hP := hprod q hq
  have hred := norm_LFunction_one_ge_primitive hχ
  have hqε : (q : ℝ) ^ (-ε) ≤ (q : ℝ) ^ (-δ) * (q : ℝ) ^ (-δ) := by
    rw [← Real.rpow_add hq0]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hA0 : 0 ≤ c * (6 : ℝ) ^ (-δ) * (q : ℝ) ^ (-δ) := by positivity
  have hB0 : 0 ≤ C₁ * (q : ℝ) ^ (-δ) := by positivity
  calc c * (6 : ℝ) ^ (-δ) * C₁ * (q : ℝ) ^ (-ε)
      ≤ c * (6 : ℝ) ^ (-δ) * C₁ * ((q : ℝ) ^ (-δ) * (q : ℝ) ^ (-δ)) :=
        mul_le_mul_of_nonneg_left hqε (by positivity)
    _ = (c * (6 : ℝ) ^ (-δ) * (q : ℝ) ^ (-δ)) * (C₁ * (q : ℝ) ^ (-δ)) := by ring
    _ ≤ ‖χ.primitiveCharacter.LFunction 1‖ * ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) :=
        mul_le_mul hL' hP hB0 (hA0.trans hL')
    _ ≤ ‖χ.LFunction 1‖ := hred

end RhSiegel
