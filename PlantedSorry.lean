import SiegelAllCharacters

/-! Planted control for the axiom audit: `check.py` must see `sorryAx` here, or the audit is not able to fail. -/
namespace StandalonePlant
theorem planted : (1 : Nat) = 2 := sorry
end StandalonePlant

#print axioms StandalonePlant.planted
