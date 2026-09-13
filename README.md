# An Exact Algorithmic Solution of the Belgian Chocolate Problem

This repository contains the Lean 4 formalization and reproducibility artifacts
for a **proposed exact algorithmic solution** of the Belgian Chocolate Problem.
Author: **Xuandi Cheng**. Release: `v1.0.0-proof-candidate`.
Independent verification is actively requested; external acceptance is not claimed.

## Main Result

Determine all `δ > 0` admitting nonzero real polynomials `x,y,p`, all strictly
Hurwitz stable, with `deg y ≤ deg x` and

$$p(s)=(s^2-2\delta s+1)x(s)+(s^2-1)y(s).$$

Nonzero constants are allowed; there is no degree bound or monic normalization.
Set `q=(1-δ)/(1+δ)`. The concrete real `Q=analyticQ` satisfies `0<Q<1/2`.
For every natural precision `m`, certified finite searches give rational
`L<Q<R` with `R-L<2^(-m)`. With `Δ=(1-Q)/(1+Q)`, the original feasible set is

$$\mathcal A=(0,\Delta),\qquad\Delta\notin\mathcal A.$$

For `0<q<1`, analytic feasibility is exactly `Q≤q`, while original polynomial
feasibility is exactly `Q<q`. Analytic endpoint attainment and polynomial
endpoint exclusion are separate results. The all-orders hierarchy criterion
is proved on **`0<q≤9/16`**, including `Q`, and is not a fixed-degree criterion.

## Formal Verification

- Lean **4.33.0**; Mathlib **4.33.0** at `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Final theorem: [`BelgianChocolate.belgianChocolate_exact_algorithmic_solution`](BCPThreshold/FinalMain.lean).
- `lake build BCPThreshold`: **PASS** on the checked source.
- `ZERO_SORRY_CHECK=PASS`; `PROJECT_AXIOM_DECLARATIONS=NONE`.
- Actual main-theorem `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
- No pending mathematical interface is a premise of the final theorem.
  `concreteFinalInterfaceBundle` implements every older interface field using proofs.
- [FinalAudit.lean](BCPThreshold/FinalAudit.lean) verifies the required declarations
  and rejects unexpected transitive axioms, including private dependencies.
- This version has 57 BCP Lean source files (the root plus 56 submodules),
  and 1,551 imported project declarations covered by the axiom audit.

### Coverage boundary

The main conclusion and its actual dependency graph are verified, **not every
paper assertion verbatim**. Lean reaches the same coefficient boxes through
the coarse Schottky/cosine-lift development, and uses a dedicated compact-polynomial
infeasibility semidecider instead of a formalization of general CAD. The paper's
algebraic-minimum/non-stabilization discussion is not separately exported as a
Lean theorem and is not needed by the final Lean result.

Finite certificate searches and finite-prefix scans are executable, with proved
soundness and completeness. The total mathematical iterator uses `Nat.find`
and remains `noncomputable`. No standalone native threshold calculator is supplied.

## Reproduction

Install Git, [elan](https://github.com/leanprover/elan), Python 3 and Bash
(Git Bash on Windows). No machine-specific absolute path is required.

```bash
git clone https://github.com/chengxuandi/belgian-chocolate-problem-lean-proof-20260910210030-init.git
cd belgian-chocolate-problem-lean-proof-20260910210030-init
git checkout v1.0.0-proof-candidate
lake exe cache get
./verify_bcp.sh
lake build BCPThreshold
```

The script first builds every BCP module in dependency order, including standalone
audits, then builds the root, runs `FinalAudit.lean`, and performs the source scan.
This serial cold-build path reduces concurrent Windows import pressure.
It exits on failure. The final separate `lake build` is an optional explicit recheck.
Expected final output:

```text
========================================
BCP FORMAL VERIFICATION: PASS
========================================
```

Logs are written to `.lake/bcp-verification/`, not used as inputs. Nonfatal
style/deprecation warnings remain. Fresh dependency download and proof checking
can require substantial disk space, memory and time; no runtime bound is claimed.

## Key Artifacts

- [Final manuscript (PDF)](output/pdf/GBCP_Final_Manuscript.pdf) / [LaTeX](output/pdf/GBCP_Final_Manuscript.tex).
- [Verification Guide (PDF)](output/pdf/GBCP_Verification_Guide.pdf) / [LaTeX](output/pdf/GBCP_Verification_Guide.tex).
- [One-page Summary (PDF)](output/pdf/GBCP_One_Page_Summary.pdf) / [LaTeX](output/pdf/GBCP_One_Page_Summary.tex).
- [Lean source](BCPThreshold/) and [original definitions](BCPThreshold/Definitions.lean).
- [Tagged proof-candidate release](https://github.com/chengxuandi/belgian-chocolate-problem-lean-proof-20260910210030-init/releases/tag/v1.0.0-proof-candidate).
- [Expert outreach notes](EXPERT_OUTREACH_NOTES.md) and [release checklist](RELEASE_CHECKLIST.md).

The PDF sources compile with Tectonic 0.17.0: in `output/pdf/`, run
`tectonic -X compile GBCP_Final_Manuscript.tex` and likewise for the guide and
summary. The checked outputs are 13, 3 and 1 pages respectively.

Historical PDFs are retained under `development/archive/`. They are not the
current manuscript or evidence of independent external referee acceptance.
Standalone `Audit*.lean` files are historical entry points; the aggregate
current audit is `FinalAudit.lean`.

## What this result does NOT claim

- No closed form, algebraicity, minimal polynomial or special-function formula.
- No practical complexity bound or benchmarked numerical threshold.
- No fixed finite truncation deciding `Q`.
- No general finite-time black-box equality test `q=Q`.
- No proof-assistant certification of novelty, intended modeling, or external acceptance.

## AI-assisted research

AI models assisted mathematical exploration, route search, adversarial review,
proof engineering and Lean formalization. The artifacts are public for independent
scrutiny. The label deliberately remains **proof candidate**.

## Independent Verification

Independent verification is actively requested. Priorities are the original
formulation, parameter transforms, all-orders realization, exact polynomial
realization, and endpoint degree-cancellation handling. The guide provides
control-theory, complex-analysis and formal-methods reviewer routes.

Use [GitHub Issues](https://github.com/chengxuandi/belgian-chocolate-problem-lean-proof-20260910210030-init/issues)
for review/contact. Preparation of this package does not imply that any expert
has been contacted or has endorsed the claim. Lean source follows its existing
Apache-2.0 headers; see [LICENSE](LICENSE) and [CITATION.cff](CITATION.cff).
