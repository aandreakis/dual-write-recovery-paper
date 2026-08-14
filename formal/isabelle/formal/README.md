# DBLog_Virtual_Cuts — Isabelle/HOL formal development

This is the machine-checked formal development that accompanies the paper

> **A Theoretical Study of DBLog**  
> *Certified Virtual Cuts for a Snapshot-Equivalent Replay of Live Databases*  
> Andreas Andreakis

The paper studies DBLog as a *snapshot-equivalent replay protocol for live
databases*: it produces a logical, replay-equivalent snapshot of a live
database scope without taking a physical database snapshot. The central
formal object is the **certified virtual cut** — a finite, asynchronously
gathered mix of change-data-capture events and chunk reads whose certified
replay reaches the same state as the source at a chosen frontier (a position
in the source-event order, analogous to a CDC watermark or log sequence
number) on a chosen key scope (the subset of keys the certificate claims to
reconstruct, for example a single table's primary keys).

The paper's formal definitions and its named theorem ladder are formalized
and machine-checked here, each under the conditional premises stated in its
theorem (see the *Main results* section below). The Isabelle/HOL kernel
checks the proofs under the assumptions stated in the paper; it does not,
and cannot, discharge the *Deployment obligations* (conditions the operator
or implementation must establish in a deployment — for example, faithful
CDC delivery and watermark placement) or the *External observation
assumption* (that the source-side observation is faithful, which the model
cannot prove from the certificate alone). The role of the machine check
is to guard against drift between the paper and the formalization.

## Building

The development is built and checked with **Isabelle2025-2**
(https://isabelle.in.tum.de/). The shared source/replay substrate is factored
into the sibling `Dual_Write_Layer0` session; that parent depends only on
`HOL-Library` from the Isabelle distribution. No other Archive of Formal Proofs
entries are required.

In this deposit the two session directories are `dual_write_layer0/` and
`formal/` (this directory), siblings under the archive's `isabelle/` tree.
From the `isabelle/` directory:

    isabelle build -d dual_write_layer0 -d formal DBLog_Virtual_Cuts

(The archive's top-level README gives the full-closure build command for
all eight bundled sessions; the command above builds just this
development and its parent.)

The build checks all thirty-nine theories across `Dual_Write_Layer0` (5) and
`DBLog_Virtual_Cuts` (34) `sorry`-free and generates the entry documents (PDFs),
which require a working LaTeX toolchain. The sessions' `ROOT` files pin
`document = pdf`, and session options take precedence over command-line `-o`
options, so `-o document=false` does not disable them; to check the proofs
without LaTeX, remove the `document = pdf, document_output = "output"` options
from the relevant `ROOT` files before building.

## Contents

The development is layered: each layer builds on the ones before it. The
shared `Dual_Write_Layer0` parent contains the source/replay substrate and the
one shared `virtual_cut_state` predicate. The `formal/` child contains the DBLog
run, certificate, theorem, witness, and fixture layers.

| Layer | Theory | Content |
|-------|--------|---------|
| 0 | `Dual_Write_Layer0.Source_History` | the source database: source coordinates (`src_coord`), source events, the append-only source history, frontiers, and the source state `Src` at a frontier |
| 0 | `Dual_Write_Layer0.Replay` | replay events (CDC events and chunk-read refreshes) and the `Apply` replay function |
| 0 | `Dual_Write_Layer0.Scope` | key-scope restriction of a per-key state |
| 0 | `Dual_Write_Layer0.Source_Coordinates` | named concrete source coordinates via the embedding `coord_of_nat` of `nat` into `src_coord`, with order, distinctness, and injectivity lemmas proved by `nat` arithmetic (shared by the witnesses and fixtures) |
| 0 | `Dual_Write_Layer0.Virtual_Cut_State` | the shared `virtual_cut_state` predicate used by both the DBLog and Dual-Write developments |
| 0–1 | `DBLog_Run_Core` | carrier-independent core: chunk-read records, the canonical clean-prefix construction and its normalisation lemmas, and the per-key / per-coordinate source-history slicing helpers |
| 1 | `DBLog_Run` | the concrete DBLog run — a single-constructor datatype with named selectors, chunk identifiers being plain naturals; the run and chunk-plan accessors as ordinary definitions; the distinct chunk enumeration `chunks_list` with its set and distinctness lemmas proved; the `wellformed_dblog_run` predicate |
| 1 | `DBLog_Run_Substrate` | the `dblog_run_substrate` locale — the run/chunk accessor interface over abstract type variables — together with its canonical interpretation at the concrete run accessors |
| 2 | `DBLog_Run_Substrate_Layer2` | the Layer 2 clean-prefix lemmas and the run-side soundness theorem, proved inside the run-substrate locale |
| 2–4 | `Virtual_Cut_Core` | carrier-independent virtual-cut support around the shared Layer-0 state predicate, plus the pure Layer 4 anchor-domain / table-scope definitions with their bridge lemmas |
| 2–3 | `Virtual_Cut` | the virtual cut and the Layer 2 result; the concrete certificate (scope, frontier, clean prefix), the evidence carrier (which records the run backing the certificate), and the three-way verifier `verify` (`Accept` / `Reject` / `Unsupported`); the decomposition of run wellformedness into a checker-checkable half (`checker_run_wellformed`) and an external observation half (`run_reflects_source`), rejoined by the proved lemma `wellformed_dblog_run_decompose`; the `layer3_checker_substrate` locale and the Layer 3 certificate-soundness theorems |
| 3–4 | `DBLog_Cert_Substrate` | the `dblog_cert_substrate` / `dblog_checker_substrate` locale hierarchy — the certificate side over abstract carriers — with locale-level versions of the Layer 3/4 theorems |
| 3–4 | `DBLog_Cert_Substrate_Inst` | the canonical concrete interpretation of the certificate substrate, plus locale-level continuation corollaries |
| 4 | `Layer4_Whole_Table` | the whole-table anchor-domain specialization |
| post-core extension | `Continuation` | source-side continuation across frontiers and sub-scope restriction of virtual cuts |

One modelling note: the run- and certificate-layer theorems (the core
ladder and the accepted-certificate continuation result) carry a
`linorder` (linear-order) hypothesis on the key type `'k`. It enters in
the canonical clean-prefix construction (`DBLog_Run_Core`), which
enumerates each chunk-read domain with `sorted_list_of_set` and
interleaves the emitted events by source coordinate with a stable
`sort_key` — making "for each key in the chunk domain" a deterministic
enumeration, as the paper implicitly assumes; `clean_prefix_of`
propagates the constraint upward. The four state-level continuation /
restriction results (`virtual_cut_state_continuation`,
`virtual_cut_state_restrict_scope`, `whole_table_state_continuation`,
`virtual_cut_restrict_to_subscope`) are constraint-free. Database
primary keys are totally ordered in practice, so the hypothesis does not
narrow the intended interpretation.

The remaining twenty-four theories are not required to state or prove
the main theorems; they exercise the definitions and guard against
vacuity. They come in families of up to three theories: `*_Core` holds
carrier-independent data (named coordinates, base states, source
histories, expected-value lemmas); `*_Model` exhibits a small concrete
model — datatype or numeric carriers with definitional accessors realizing
exactly the values the witness needs; `*_Inst` interprets the substrate
locales at that model and proves the witness or fixture facts there. Some
families share a model or interpret directly, so not every family has all
three pieces.

- `Layer01_Witnesses_{Core,Model,Inst}` — the minimum-viable wellformed-run positive witness.
- `Layer01_Witness_Topics_{Core,Model,Inst}` — two further positive run witnesses over different base-state and source-history shapes.
- `Layer01_Virtual_Cut_Example_{Core,Model,Inst}` — the paper's running example (the accounts-table backfill) as a fully worked virtual cut.
- `Layer01_Fixtures_{Core,Model,Inst}` — Layer 0/1 negative and boundary fixtures: runs violating individual wellformedness clauses are rejected.
- `Layer2_Fixtures_{Core,Inst}` — canonical clean-prefix structural and frontier boundary fixtures; the `Inst` reuses the Layer 0/1 models.
- `Layer4_Witnesses_Core` and `Layer3_Witnesses_Inst` — the Layer 3 accepted-certificate and Layer 4 whole-table positive witnesses: anchor data in the `Core`, one shared interpretation proving both.
- `Layer3_Fixtures_{Core,Inst}` — checker fixtures, including wrong-base-state and wrong-history scenarios with unfaithful source observation.
- `Layer3_Defect_Regressions` — permanent kernel-checked regressions for retained Layer-3 fixture defects, added at an external defect-review round.
- `Layer4_Fixtures_{Core,Inst}` — boundary and counterexample fixtures for the whole-table specialization.
- `Continuation_Fixtures_{Core,Inst}` — the positive continuation witness and the load-bearing and boundary fixtures of the extension.
- `Public_Checker_Witness` — the closing non-vacuity gate (below).

### Constructed witnesses and fixtures

Every witness and fixture fact is established constructively: a concrete
model is exhibited as closed-form data, the substrate locales are
interpreted at it (or the facts are proved directly over the public
carriers), and the non-vacuity, acceptance, and rejection claims are
proved at that instance by computation. Nothing in the session is
axiomatized — there is no `axiomatization`, `typedecl`, or `consts`
declaration. The only `typedef` is the source coordinate type,
`typedef src_coord = "UNIV :: nat set"` in `Source_History` — a
conservative extension over a provably nonempty set, with its `linorder`
and `order_bot` instances proved, not assumed. The Isabelle kernel
therefore checks every fact in the development down to definitions; no
claim rests on a postulated model shape.

The final theory, `Public_Checker_Witness`, is the non-vacuity gate: it
exhibits a concrete certificate / evidence pair over the public carriers
that `verify` genuinely accepts, a deployment environment under which
`faithful_source_observation` genuinely holds, and fires all nine main
theorems at such concrete witnesses. Two closing exhibits — an accepted
pair whose observation is unfaithful, and faithful evidence the verifier
rejects — show the two headline premises are independent and not vacuous.

## Main results

### Core ladder (Layers 2–4)

Four core theorems carry the development.

- **`wellformed_run_implies_virtual_cut`** — the clean prefix of a wellformed
  DBLog run is a virtual cut: replaying it reproduces the source state,
  restricted to the run's scope, at the run's frontier.

- **`accepted_certificate_implies_wellformed_run`** — a certificate accepted
  by the verifier, paired with a faithful observation of the source, is
  witnessed by a wellformed run that is coherent with the certificate.

- **`accepted_virtual_cut_sound`** — a certificate accepted by the verifier,
  under faithful source observation, is a virtual cut: its certified replay
  reaches the source state at the certified frontier on the certified scope.

- **`accepted_whole_table_anchor_domain_specialization`** — when the
  certificate's claim scope is the whole table, applying its clean prefix
  reproduces the entire source state at the frontier.

Each core result is conditional. The Layer 2 result,
`wellformed_run_implies_virtual_cut`, is conditional on the hypotheses named
in its statement — chiefly the `wellformed_dblog_run` premise. The Layer 3
and Layer 4 results are established *inside* the `layer3_checker_substrate`
locale, which abstracts the verifier as a set of soundness obligations: an
accepted certificate has a wellformed materializing run whose accessors
agree with the certificate, under faithful source observation. Their
conditions are the hypotheses named in each statement — verifier
acceptance, faithful source observation, and, for the whole-table result, a
whole-table claim scope — *together with* these checker-substrate
obligations. The obligations are proved for the concrete verifier in
`Virtual_Cut`, and `Public_Checker_Witness` exercises them at an accepted
pair, so the locale hypotheses are satisfiable. All of these correspond to
the Deployment obligations and the External observation assumption
discussed in the paper: the formalization makes them explicit hypotheses;
it does not discharge them.

### Continuation extension

The continuation extension is the promoted source-side fragment of the
"certificate algebra" future-work catalog (see the paper's "Source-Side
Continuation and Restriction of Virtual Cuts" section). It is built source-side
over the core ladder: each result is an `Apply`-against-`Src` equality, and
the proofs compose with Layer 2 and Layer 3 without re-opening the DBLog
run model.

- **`virtual_cut_state_continuation`** — primary continuation theorem. On a
  wellformed source history, a virtual cut at frontier `f` on scope `K`
  extends to a virtual cut at any later frontier `f'` on `K` by appending the
  faithful CDC continuation segment for the half-open interval `(f, f']` on
  `K`. The premise that the appended segment is exactly the
  `cdc_segment_between` for `(f, f']` on `K` is the source-side faithfulness
  obligation; the wellformedness of the source history is the second
  conditional premise.

- **`virtual_cut_state_restrict_scope`** — sub-scope restriction lemma. A
  virtual cut on key scope `K` restricts to a virtual cut on any `K' ⊆ K`.
  The converse — scope widening — is not stated and would assert agreement on
  keys never certified.

- **`whole_table_state_continuation`** — whole-table instance of continuation.
  On a wellformed source history, when `Apply σ = Src b0 H f` holds
  unrestricted — the all-keys equality the Layer 4 specialisation yields —
  appending the full CDC segment for `(f, f']` on `UNIV` reaches the source
  state at `f'` on every key. A scoped continuation does not become
  whole-table for free.

- **`virtual_cut_restrict_to_subscope`** — certificate-accessor sub-scope
  restriction. An accepted certificate's virtual cut, read through its
  accessors, restricts to any sub-scope `K' ⊆ scope C` as a source-side
  `virtual_cut_state` equality on `clean_prefix C` at `frontier C`. This is
  *not* a claim that a restricted certificate is accepted by the verifier;
  verifier acceptance of any concrete restricted certificate is an evidence
  obligation, not a consequence of the source-side algebra.

- **`accepted_certificate_continuation_sound`** — accessor-level accepted-
  certificate continuation. Inside the `layer3_checker_substrate` locale, an
  accepted certificate under faithful source observation extends, by a
  faithful CDC continuation segment for `(frontier C, f']` on `scope C`, to
  a virtual-cut-state equality on `clean_prefix C @ δ` at the later frontier
  `f'`. The conditional premises are verifier acceptance, faithful source
  observation, wellformedness of the source history, the locale's
  checker-substrate obligations, *and* the continuation-segment faithfulness
  premise on `δ`.

Each continuation-extension result is conditional on the hypotheses named
in its statement, with the same Deployment-obligation and
External-observation-assumption interpretation as the core ladder. The
extension is source-side throughout: no result here is a destination-state,
delivery, sink, or extended-certificate-acceptance claim.

## Release metadata

For the artifact as deposited on Zenodo, the verification environment is
pinned as follows.

- **Sessions.** `Dual_Write_Layer0` (5 theories) and `DBLog_Virtual_Cuts`
  (34 theories), checked `sorry`-free.
- **Prover.** Isabelle2025-2 (`ISABELLE_IDENTIFIER=Isabelle2025-2`),
  using `HOL-Library` only — no other Archive of Formal Proofs entry.
- **Release identification.** This directory is the `DBLog_Virtual_Cuts`
  development, bundled in this deposit for build closure of its worked
  instance. The development's own published archival records are
  version 2.1 (10.5281/zenodo.21732790; released 2026-08-01; the
  concept DOI 10.5281/zenodo.20389696 resolves to the latest version),
  version 2.0 (10.5281/zenodo.20652511; released 2026-06-12;
  byte-frozen), and v1.0 (version DOI 10.5281/zenodo.20389697; the
  17-theory surface, frozen).

The build command and the shape of its output — an illustration of the
expected run, not a verbatim log; elapsed times are machine-dependent
and elided:

    Building Dual_Write_Layer0 ...
    Finished Dual_Write_Layer0 (...)
    Running DBLog_Virtual_Cuts ...
    Preparing DBLog_Virtual_Cuts/document ...
    Finished DBLog_Virtual_Cuts/document (0:00:10 elapsed time)
    Document at "formal/output/document.pdf"
    Finished DBLog_Virtual_Cuts (...)

A successful build exits with status 0; no theory uses `sorry` or
`oops` (the `quick_and_dirty=false` build is the check).

## License

Released under the BSD 3-Clause License. See [`LICENSE`](LICENSE).

## Author

Andreas Andreakis.
