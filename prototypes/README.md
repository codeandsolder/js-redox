# VM semantic-lifting prototypes

These are analysis prototypes used to validate the next generic `jsvm-lift` stages before porting them to Rust.

- `fireye-state-lift.cjs` — statically partial-evaluates one recovered Fireye flattened opcode state machine for concrete selector values. It follows only decidable state transitions and records terminal semantics; it does **not** execute the protected application.
- `normalize-vm-semantics.cjs` — canonicalizes those terminal semantics with identifier anonymization, local copy propagation, and simple bitwise algebra to produce cross-build-comparable structural signatures.

Validated Fireye shard result:
- selector domain: 0..15 from four one-bit flags;
- opcodes 0..13: 14 distinct normalized semantics;
- opcodes 14/15: identical empty/no-op terminal signatures.

These are intentionally prototypes, not generic CLI interfaces yet. The generic Rust implementation should derive the state variable, selector shape, flag variables, and terminal semantics from `DecoderCandidate` / `StateMachineCandidate` provenance instead of relying on this shard's variable names.
