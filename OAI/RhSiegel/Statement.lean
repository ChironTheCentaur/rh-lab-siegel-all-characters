import OAI.NumberTheory.PrimeGaps.SiegelBounds

/-!
# Siegel's theorem (1935) for the RH map node `rh:barrier:siegel-zeros`

The node quotes Siegel, Acta Arith. 1 (1935) 83-86, eq. (2): `log L_d(1) = o(log |d|)`, where `L_d` is the
L-function of the real primitive character of the quadratic field of discriminant `d` (so `|d|` is its conductor).

The mathematics is openai/math's (github.com/openai/math at `fd4aeeb2`, file
`lean/OAI/NumberTheory/PrimeGaps/SiegelBounds.lean`): `OAI.LargePrimeGaps.quadratic_siegel` is Siegel's lower bound
`c(ε) (q+1)^(-ε) ≤ ‖L(1, χ)‖` for primitive nontrivial quadratic `χ` mod `q`, and
`OAI.LargePrimeGaps.LFunction_norm_small_power` (DirichletGrowth.lean) is the upper bound `‖L(s, χ)‖ ≤ K(ε)((q+2)(‖s‖+2))^(2ε)`
for `Re s ≥ 1 - ε`. This file only restates them with Mathlib constants and combines them into the node's form.
Nothing here is new mathematics.

Every statement below uses Mathlib's `DirichletCharacter.LFunction` (the analytic continuation of `∑ χ(n) n^(-s)`),
`DirichletCharacter.IsPrimitive`, `Real.log` and `Real.rpow` only.

Not stated here, and not provable as a theorem: the *ineffectivity* of the constant. The openai/math proof is the
classical one, by cases on whether some quadratic character has a real zero near 1 (`by_cases hex` in
`quadratic_siegel_eventual`), which is exactly why the constant is not computable from it; that is a remark about the
proof, not a Lean statement. Heath-Brown's 1983 twin-prime dichotomy is not stated here either.
-/

namespace RhSiegel

open OAI.LargePrimeGaps

/-- For a nontrivial quadratic Dirichlet character, `L(1, χ)` is a positive real number. -/
theorem LFunction_one_real_pos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hχ2 : χ ^ 2 = 1) :
    χ.LFunction 1 = ((χ.LFunction 1).re : ℂ) ∧ 0 < (χ.LFunction 1).re := by
  refine ⟨?_, quadratic_LFunction_re_pos_one hχ hχ2⟩
  have him : (χ.LFunction ((1 : ℝ) : ℂ)).im = 0 := quadratic_LFunction_im hχ hχ2 one_pos
  rw [Complex.ofReal_one] at him
  apply Complex.ext <;> simp [him]

theorem norm_LFunction_one_eq_re {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hχ2 : χ ^ 2 = 1) : ‖χ.LFunction 1‖ = (χ.LFunction 1).re := by
  obtain ⟨he, hpos⟩ := LFunction_one_real_pos hχ hχ2
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using hpos)]
  simp

/-- Siegel's lower bound, log form: for every `ε > 0` there is `A` with
`log L(1, χ) ≥ -A - ε log q` for every primitive nontrivial quadratic character `χ` mod `q`. -/
theorem log_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 →
        -A - ε * Real.log q ≤ Real.log (χ.LFunction 1).re := by
  set e := min ε 1 with he_def
  have he0 : 0 < e := lt_min hε one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  obtain ⟨c, hc, h⟩ := quadratic_siegel he0 he1
  refine ⟨|Real.log c| + Real.log 2, by positivity, ?_⟩
  intro q _ χ hprim hχ hχ2
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hlow := h q χ hprim hχ hχ2
  rw [norm_LFunction_one_eq_re hχ hχ2] at hlow
  have hpos : 0 < c * ((q : ℝ) + 1) ^ (-e) := by positivity
  have hlog := Real.log_le_log hpos hlow
  rw [Real.log_mul hc.ne' (by positivity), Real.log_rpow (by linarith)] at hlog
  have h2q : Real.log ((q : ℝ) + 1) ≤ Real.log 2 + Real.log q := by
    rw [← Real.log_mul (by norm_num) hq0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlq1 : 0 ≤ Real.log ((q : ℝ) + 1) := Real.log_nonneg (by linarith)
  have habs : -|Real.log c| ≤ Real.log c := neg_abs_le _
  nlinarith [mul_le_mul_of_nonneg_left h2q he0.le, mul_le_mul_of_nonneg_right heε hlq,
    mul_le_mul_of_nonneg_right he1 hl2]

/-- The easy upper bound, log form: for every `ε > 0` there is `B` with
`log L(1, χ) ≤ B + ε log q` for every nontrivial quadratic character `χ` mod `q`. -/
theorem log_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → χ ^ 2 = 1 →
        Real.log (χ.LFunction 1).re ≤ B + ε * Real.log q := by
  set e := min (ε / 2) (1 / 2) with he_def
  have he0 : 0 < e := lt_min (by linarith) (by norm_num)
  have he1 : e ≤ 1 / 2 := min_le_right _ _
  have heε : e ≤ ε / 2 := min_le_left _ _
  obtain ⟨K, hK, h⟩ := LFunction_norm_small_power he0 he1
  refine ⟨|Real.log K| + Real.log 9, by positivity, ?_⟩
  intro q _ χ hχ hχ2
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by linarith
  have hup := h q χ hχ 1 (by simp; linarith)
  rw [norm_LFunction_one_eq_re hχ hχ2, norm_one] at hup
  have hpos := (LFunction_one_real_pos hχ hχ2).2
  have hlog := Real.log_le_log hpos hup
  have hb : (0 : ℝ) < ((q : ℝ) + 2) * (1 + 2) := by positivity
  rw [Real.log_mul hK.ne' (by positivity), Real.log_rpow hb] at hlog
  have h9 : Real.log (((q : ℝ) + 2) * (1 + 2)) ≤ Real.log 9 + Real.log q := by
    rw [← Real.log_mul (by norm_num) hq0.ne']
    exact Real.log_le_log hb (by nlinarith)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hl9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have habs : Real.log K ≤ |Real.log K| := le_abs_self _
  have hlb : 0 ≤ Real.log (((q : ℝ) + 2) * (1 + 2)) := Real.log_nonneg (by nlinarith)
  nlinarith [mul_le_mul_of_nonneg_left h9 he0.le, mul_le_mul_of_nonneg_right heε hlq,
    mul_le_mul_of_nonneg_right he1 hl9]

/-- **Siegel (1935), eq. (2), the node's form**: `log L(1, χ) = o(log q)` over primitive nontrivial quadratic
Dirichlet characters `χ` mod `q`, i.e. for every `ε > 0`, `|log L(1, χ)| ≤ ε log q` once `q` is large enough. -/
theorem siegel_log_L_one :
    ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → Q ≤ q →
        |Real.log (χ.LFunction 1).re| ≤ ε * Real.log q := by
  intro ε hε
  obtain ⟨A, hA, hlow⟩ := log_lower (ε / 2) (by linarith)
  obtain ⟨B, hB, hup⟩ := log_upper (ε / 2) (by linarith)
  refine ⟨⌈Real.exp (2 * (A + B) / ε)⌉₊, ?_⟩
  intro q _ χ hprim hχ hχ2 hQ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hexp : Real.exp (2 * (A + B) / ε) ≤ q :=
    (Nat.le_ceil _).trans (by exact_mod_cast hQ)
  have hlogq : 2 * (A + B) / ε ≤ Real.log q := by
    rw [← Real.log_exp (2 * (A + B) / ε)]
    exact Real.log_le_log (Real.exp_pos _) hexp
  have hAB : A + B ≤ ε / 2 * Real.log q := by
    have := (div_le_iff₀ hε).mp hlogq
    nlinarith
  have h1 := hlow q χ hprim hχ hχ2
  have h2 := hup q χ hχ hχ2
  rw [abs_le]
  constructor <;> nlinarith

/-- Siegel's theorem in its usual lower-bound form: for every `ε > 0` there is `c > 0` with
`L(1, χ) ≥ c q^(-ε)` for every primitive nontrivial quadratic character `χ` mod `q`. -/
theorem siegel_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 →
        c * (q : ℝ) ^ (-ε) ≤ (χ.LFunction 1).re := by
  obtain ⟨A, hA, h⟩ := log_lower ε hε
  refine ⟨Real.exp (-A), Real.exp_pos _, ?_⟩
  intro q _ χ hprim hχ hχ2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hpos := (LFunction_one_real_pos hχ hχ2).2
  rw [← Real.exp_log hpos, Real.rpow_def_of_pos hq0, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := h q χ hprim hχ hχ2
  nlinarith

end RhSiegel
