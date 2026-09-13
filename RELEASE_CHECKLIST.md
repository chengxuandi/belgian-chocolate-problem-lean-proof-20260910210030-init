# GBCP Public Release Checklist

Independent-review checklist: boxes are intentionally blank for the verifier.
Maintainer results are in README and the live release metadata. Resolve the
frozen commit with `git rev-parse v1.0.0-proof-candidate^{commit}`.

## Lean

- [ ] Final main theorem compiled
- [ ] Full `lake build BCPThreshold` and `./verify_bcp.sh` PASS
- [ ] ZERO_SORRY_CHECK=PASS; PROJECT_AXIOM_DECLARATIONS=NONE
- [ ] Final `#print axioms` checked; no pending interfaces

## Paper

- [ ] Main theorem matches Lean; coverage boundary explicit
- [ ] Endpoint and parameter conventions consistent
- [ ] AI disclosure and scope/non-claims included
- [ ] Guide is 2–4 pages; summary is exactly 1 page

## GitHub

- [ ] Repository Public; README finalized; no secrets
- [ ] Final commit frozen; tag and release resolve to that commit
- [ ] Three PDFs uploaded and match tagged source
- [ ] Public URLs and clone/reproduction commands tested

## Outreach

- [ ] Verification Guide and one-page Summary ready
- [ ] Author details and initial recipient list confirmed
- [ ] Separate email draft prepared and approved
- [ ] No unconfirmed endorsement or outreach implied
