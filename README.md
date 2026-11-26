# Siegel's theorem for every nonprincipal Dirichlet character, in Lean 4

Author: Sky ([@ChironTheCentaur](https://github.com/ChironTheCentaur)). Standalone package, 2026-11-26.

> **AI disclosure.** The Lean proofs and this package were written with AI assistance (Claude, by Anthropic), under
> the author's direction. A theorem is listed only because the Lean kernel checks it here and `#print axioms`
> shows nothing beyond Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## The theorem

`RhSiegel.exists_siegel_constant`: for every ε > 0 there is C > 0 such that

    C · q^(−ε) ≤ ‖L(1, χ)‖   for every q ≥ 1 and every Dirichlet character χ ≠ 1 mod q

(real or complex, primitive or not). `L(1, χ)` is Mathlib's `DirichletCharacter.LFunction χ 1`. The constant is
ineffective, as in Siegel (1935). No hypothesis; nothing assumes RH or GRH.

Also here: `RhSiegel.siegel_lower` (L(1, χ) ≥ c(ε) q^(−ε) for primitive real χ ≠ 1) and `RhSiegel.siegel_log_L_one`
(Siegel's form log L(1, χ) = o(log q)).

**What is ours and what is not.** The deep input is openai/math's proof of Siegel's bound for primitive quadratic
characters (`OAI.LargePrimeGaps.quadratic_siegel`) and its line bound for primitive characters
(`OAI.LargePrimeGaps.nonprincipal_line_lower`). Ours is the reduction to them: passing from χ to its primitive
character (via Mathlib's `LFunction_changeLevel`) and bounding the lost Euler factors by C(δ) q^(−δ). The mathematics is
classical.

## Other Lean proofs we know of (searched 2026-11-26)

| where | characters covered | bound |
|---|---|---|
| openai/math `quadratic_siegel` | primitive, χ² = 1 | c (q+1)^(−ε) ≤ ‖L(1,χ)‖ |
| openai/math `nonprincipal_line_lower` | primitive, all χ ≠ 1 | c ((q+2)·2)^(−ε) at s = 1 |
| TauCeti `quadratic_LFunction_siegel` | any level, χ quadratic | c N^(−ε) ≤ Re L(1,χ) |
| sthubbar/goldbach-lean `siegel` | any level, χ² = 1 | c N^(−ε) ≤ ‖L(1,χ)‖ |
| this package | any level, every χ ≠ 1 | C q^(−ε) ≤ ‖L(1,χ)‖ |

Searched by GitHub code search (default branches only). "None found" is a search result with those limits, not
proof that nothing exists.

## What is in the package

The import closure, cut out so it builds on its own: 45 modules (20981 lines of Lean). `OAI/RhSiegel/`
is ours. `OAI/NumberTheory/PrimeGaps/` is the subset of openai/math (github.com/openai/math, Apache-2.0,
`LICENSE.openai-math`, commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`) that the proof imports, byte-identical, under
its original module names. Lean v4.34.1; only Mathlib (pinned at `d13f23b723b8a846827a245b89c10fc7d3f11612`) is fetched at build time. Source commit
of our files: `7dddb4c7d09f4b384a01517d87bfd95ea13ab0e4`.

## Verify it

```
python3 check.py
```

It runs `lake exe cache get` and `lake build` (every module), then:

* `AxiomAudit.lean`: 13 `#print axioms` lines (ours and the openai/math theorems used). PASS needs every one to
  report only standard axioms, and the set of reported names to equal the set listed.
* `PlantedSorry.lean`: a planted `sorry` that the audit must report as `sorryAx`.
* `controls/*.lean`: near misses (ε = 0, χ ≠ 1 dropped, q^ε for q^(−ε), a uniform bound, …) that must fail at exactly
  the lines marked `-- FAIL`, beside true statements that must be accepted.
* `MANIFEST.sha256`: every checked file hashes to the shipped bytes.

It writes `CHECK_RESULT.json` and exits 0 only on PASS.
