# The twelve principal results

This is a reader-oriented map for the paper
"Machine-Checked Dual-Write Recovery from a Committed Log."

The short titles below are handles, not formal statements. For citation or
technical comparison, read the theorem in <code>paper/main.tex</code>, then
follow the principal Isabelle theorem and its premises through
<code>formal/THEOREM_INDEX.md</code>. The Isabelle source is authoritative.

## T1 - Observation Bound

**Paper statement location:** Section 3,
<code>thm:obsbound</code>.

**Principal Isabelle results:**
<code>observation_measured_dilemma</code> and the practitioner form
<code>observation_duplicate_or_lost</code>.

**Source:**
<code>formal/isabelle/dual_write_effect/Dual_Write_Effect_Observation_Bound.thy</code>.

**Meaning.** The mechanization constructs two reachable, hazard-free,
genuinely emitting states that agree on the effect machine's modeled core
observation and generation but differ in the emitted-effect ledger. Every
policy that factors through an observation equal on the pair chooses the
same batch. One repaired member is unsafe or the other remains incomplete
at the judged frontier.

**Scope.** This is an exists-system information bound at a designed pair.
It is not a universal theorem about all source-only recovery algorithms.
The policy being tested need not have produced the pair's earlier history.

## T2 - Control-Plane Bound

**Paper statement location:** Section 3,
<code>thm:controlplane</code>.

**Principal Isabelle results:**
<code>recovery_information_dilemma_pair</code> and
<code>epoch_measured_dilemma_pair</code>.

**Source:**
<code>formal/isabelle/dual_write_effect/Dual_Write_Effect_Dilemma.thy</code>.

**Meaning.** Store-measured policies and policies that additionally read
the modeled generation choose the same batch on the constructed pair and
are defeated on one member.

**Scope.** The theorem is about the modeled projections named in the
statement. It does not say that every conceivable control plane is
uninformative. A durable sink acceptance record lies on the escape side.

## T3 - Checkpoint Dilemma

**Paper statement location:** Section 4,
<code>thm:checkpoint</code>.

**Principal Isabelle results:**
<code>checkpoint_dilemma_pair</code> and
<code>same_protocol_batch_agreement_dilemma</code>.

**Source:**
<code>formal/isabelle/dual_write_effect/Dual_Write_Effect_Cursor.thy</code>.

**Meaning.** A single deterministic deliver-then-checkpoint protocol has
two reachable crash endpoints with the same durable-local view, cursor
included, and different acceptance/emission histories. Crash timing is the
only nondeterminism. Recovery therefore fires the same batch and duplicates
one effect or leaves one owed.

**Scope.** This closes a loophole left by the pair-specific information
bound: the states come from one concrete protocol. It does not claim that
every protocol has the same window.

## T4 - Sink-Reading Escape

**Paper statement location:** Section 5,
<code>thm:escape</code>.

**Principal Isabelle result:**
<code>sink_reading_escape_general</code>.

**Source:**
<code>formal/isabelle/dual_write_effect/Dual_Write_Effect_Dilemma.thy</code>.

**Meaning.** Recovery can compute the missing batch as committed
obligations minus the sink's accepted identities when the accepted record
is authoritative, complete, current, and operations have stable
distinguishing source coordinates.

**Scope.** The theorem reads acceptance history, not merely current sink
contents. Completeness and freshness are separate obligations. The theorem
does not itself handle in-flight arrivals or concurrent recoverers; T5-T8
address those hazards.

## T5 - Wire Bound

**Paper statement location:** Section 6,
<code>thm:wire</code>.

**Principal Isabelle result:**
<code>no_channel_blind_policy_escapes</code>.

**Source:**
<code>formal/isabelle/dual_write_effect/Dual_Write_Effect_Channel_Blind.thy</code>.

**Meaning.** On the designed reachable channel pair, a batch selector that
cannot observe the in-flight wire is defeated when inserted into the fixed
unfenced re-drive relation.

**Scope.** The quantifier ranges over channel-blind batch selectors in one
specified relation. It is not a bound on every recovery algorithm that
cannot inspect a network queue.

## T6 - Arrival Fence

**Paper statement location:** Section 6,
<code>thm:fence</code>.

**Principal Isabelle results:**
<code>fenced_redrive_exactly_once</code> and the reachable-state package
<code>fenced_redrive_reachable_package</code>.

**Source:**
<code>formal/isabelle/dual_write_effect/Dual_Write_Effect_Fencing.thy</code>.

**Meaning.** One atomic fenced re-drive heals the store, lands the recovery
delta synchronously in the accepted record, and raises the acceptance fence.
It is exact at its own frontier. Old in-flight requests then fail the
generation test.

**Corollary 6.1 - Rescue Conversion.**
<code>fence_rescue_conversion</code> proves the price: the same fence that
rejects a stale duplicate may also reject an old request that would have
rescued missing work.

**Corollary 6.2 - Residual-Wire Stability.**
<code>fenced_redrive_all_stale</code> and
<code>fenced_result_wire_preserves_eo</code> establish stability for the
specified arrive/lose-only continuation.

**Scope.** Immediate exactness relies on the fenced re-drive being one
atomic act. Raising the fence before the batch can stop the recovery's own
work; raising it only after resume can let the old request arrive first.
Unscoped post-resume preservation is false.

## T7 - Second-Recoverer Bound

**Paper statement location:** Section 7,
<code>thm:second</code>.

**Principal Isabelle result:**
<code>u_concurrent_recovery_dilemma</code>.

**Source:**
<code>formal/isabelle/dual_write_unified/DWU_Concurrent_Recovery.thy</code>.

**Meaning.** On the constructed concurrency machine, two claimless
recoverers that use the sink delta can jointly produce a duplicate or leave
work owed within the theorem's schedule class.

**Scope.** The headline grammar records final armed, fired, and healer sets;
one duplicate witness relies on a member firing without its own heal. The
phase-ordered addendum proves ordered silent-death defeats and transports
them to the loose grammar, but the headline for-all conclusion is false if
the ordered extension simply replaces the loose extension at the landed
witness. Preserve this distinction.

## T8 - Completed-Claim Exactness

**Paper statement location:** Section 7,
<code>thm:claim</code>.

**Principal Isabelle results:**
<code>u_fenced_multiwriter_discipline_safe</code> and
<code>u_exactly_once_at_completed_claim</code>.

**Source:**
<code>formal/isabelle/dual_write_unified/DWU_Fenced_Discipline.thy</code>.

**Lemma 7.1 - Claim-fence safety.**
Every trace following the claim discipline is hazard-free on the modeled
machine.

**Meaning.** An atomic claim sets the fence, reads the accepted record, and
arms the batch in one step. A completed claim is exact at its fence under
the statement's premises.

**Corollary 7.1 - Journal-grade exactness.**
The journal-grade forms connect retained-grade and permanent-source
specifications under explicit retention premises.

**Scope.** This is not an unconditional concurrent exactly-once theorem.
The atomic claim discipline and source/retention premises are
load-bearing.

## T9 - Deduplicated-View Coverage Identity

**Paper statement location:** Section 8,
<code>thm:dedup</code>.

**Principal Isabelle results:**
<code>dedup_sink_exactly_once_iff_at_least_once</code> and the substantive
per-instance form <code>dedup_sink_instance_exact_iff</code>.

**Source:**
<code>formal/isabelle/dual_write_effect/Dual_Write_Effect_Exactly_Once.thy</code>.

**Meaning.** On an absorbing permanent-memory deduplicated view,
duplicate-freedom holds by construction, so exactly-once reduces to
coverage. The per-instance corollary connects this view to ascending stable
source coordinates.

**Scope.** The displayed identity is definitional at the view layer. It
does not verify an atomic consumer transaction, and bounded deduplication
does not have the same property.

## T10 - Truncation Dilemma

**Paper statement location:** Section 8,
<code>thm:trunc</code>.

**Principal Isabelle result:**
<code>u_truncation_recovery_dilemma</code>.

**Source:**
<code>formal/isabelle/dual_write_unified/DWU_Truncation.thy</code>.

**Meaning.** The development constructs histories that look the same
through the retained view but differ in the journal specification. A
policy based only on retained history must fabricate, abandon, or enter the
statement's unsafe branch.

**Scope.** Loss is graded against the full journal specification, not only
the retained view seen by the policy.

## T11 - Faithful-Image Equivalence

**Paper statement location:** Section 9,
<code>thm:image</code>.

**Principal Isabelle result:**
<code>safe_iff_running_image_faithful</code>.

**Source:**
<code>formal/isabelle/dual_write_core/Dual_Write_Converse.thy</code>.

**Meaning.** On the store machine, under the crash-closure premise, safety
is equivalent to the running state remaining a faithful image of committed
source history.

**Scope.** The safe-side boundary is effectiveness rather than scope size.
This is a store-tier characterization, not a delivery theorem.

## T12 - Shared-Core Agreement

**Paper statement location:** Section 10,
<code>thm:agree</code>.

**Principal Isabelle results:**
<code>Π_section</code>, <code>u_landed_embedding</code>,
<code>u_solo_projection</code>, <code>u_hazards_once</code>, and
<code>u_sink_delta_commutes</code>.

**Sources:**
<code>formal/isabelle/dual_write_unified/DWU_Machine.thy</code> and
<code>formal/isabelle/dual_write_unified/DWU_Conservativity.thy</code>.

**Meaning.** The effect, unified concurrency, and store models share
selected projections and relations when the stated alignment premises
hold.

**Scope.** The theorem does not merge the machines. The wire relation does
not lift, and safety transports through the acceptance interface without an
unconditional exactness result.

## Supporting interfaces

- **Acceptance interface:** locale <code>transit_iface</code> and theorem
  <code>a_safety</code> in
  <code>formal/isabelle/dual_write_transit/DWT_Interface.thy</code>.
- **Certified schedule validator:** exported validator and its correctness
  theorems in
  <code>formal/isabelle/dual_write_schedule_validator/Dual_Write_Schedule_Validator.thy</code>.
- **DBLog worked-instance bridge:**
  <code>virtual_cut_certifies_dblog</code> in
  <code>formal/isabelle/dual_write_dblog_instance/DBLog_Instance.thy</code>.

## Safe citation rule

When citing a result, include:

1. the paper result number and title;
2. the policy class or machine named in its statement;
3. its judged frontier or evidence regime where applicable;
4. any atomicity, completeness, ordering, or retention premise used by the
   positive conclusion.

Do not cite the one-line title alone.
