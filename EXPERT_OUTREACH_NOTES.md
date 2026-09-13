# Expert outreach notes

Preparation notes only: not an email, an endorsement list, or evidence that
outreach occurred. No messages are sent by preparing this package.

## Author identity

- Release name: **Xuandi Cheng**.
- User-supplied description: undergraduate student in electrical/electronic
  engineering. Confirm exact institution, program and present status before
  using these details in correspondence; no school is inferred here.
- Personal email and institution are not supplied for publication. The public
  summary uses GitHub Issues as the contact route.
- Optional, subject to author confirmation before sending: currently preparing
  graduate entrance examinations and therefore having limited time.

## Wording and essential facts

Use **“proposed exact algorithmic solution”** or **“complete solution candidate”**.
Do not say “universally accepted,” “expert-approved,” or “every line of the
paper is formalized.” Modeling, interpretation, novelty and exposition still
deserve independent review.

Explain “exact” as proved termination and correctness of arbitrary prescribed-
precision rational enclosures, combined with the original feasible interval
and independent endpoint treatment. It is not a closed form or an efficient solver.

- Repository: https://github.com/chengxuandi/belgian-chocolate-problem-lean-proof-20260910210030-init
- Release: https://github.com/chengxuandi/belgian-chocolate-problem-lean-proof-20260910210030-init/releases/tag/v1.0.0-proof-candidate
- Main theorem: `BelgianChocolate.belgianChocolate_exact_algorithmic_solution`.
- Lean / Mathlib 4.33.0; no project axioms or proof holes.
- Main-theorem axioms: `propext`, `Classical.choice`, `Quot.sound`.
- On `0<q<1`, `A(q) ↔ Q≤q` but `P(q) ↔ Q<q`.
- All-orders hierarchy domain: `0<q≤9/16`.
- Finite scans are executable; the total iterator is noncomputable `Nat.find`.
- The paper's Hempel/CAD routes and non-stabilization discussion are not
  separately formalized Lean theorems. See the explicit coverage boundary.

## Reviewer selection and goals

Prepare a small, personally verified recipient list before sending anything:

1. Control theory / simultaneous stabilization: original definition, parameters,
   polynomial interface, endpoint and actual-degree handling.
2. Complex analysis: omitted-value representation, coefficient uniformity,
   compatible compact limits, inverse identities and simple fibres.
3. Lean / formal methods: definitions, dependencies, concrete interfaces,
   axiom audit and clean reproduction.

No named recipient, address, willingness to review, or endorsement has yet
been independently verified in this package. Do not mass-mail a speculative list.

First goal: **independent verification**, ideally of one bounded high-risk
interface. Second goal, only if the candidate survives checking: possible
collaboration on manuscript refinement and publication. Do not request
authorship in the first message. Offer the one-page summary first and link
the guide and paper rather than sending large unsolicited attachments.

## AI disclosure and availability

Suggested sentence: “AI models were used for mathematical exploration,
adversarial review, proof engineering, and Lean formalization; the proof
artifacts and source are public for independent verification.”

After confirming the author's circumstances, limited availability during
graduate entrance examination preparation may be mentioned briefly. If an
expert validates the result, the author may express willingness to discuss
further refinement and submission. Do not imply an existing collaboration.

## Before sending

- Confirm identity, affiliation, contact email and optional examination context.
- Verify the recipient's current institutional address and expertise.
- Include the frozen release and one specific review question.
- Get author approval of a separate email draft.
- Make no claims of acceptance, closed form, algebraicity, practical complexity,
  or a generic equality detector.
