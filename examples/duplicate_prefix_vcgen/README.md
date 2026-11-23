# Generated safety VC for duplicate_prefix

The Rust function in [duplicate_prefix.rs](duplicate_prefix.rs) is the
archived implementation using `copy_nonoverlapping`. The CLI generates a
Lean safety VC from this standalone Rust file. The stock runner uses the
separate [runtime harness](runtime.rs) to prepare actual call states with
Tree Borrows enabled.

With the pinned MIR-enabled sysroot in `MIRI_SYSROOT`, build `native_runner`
and the Lean libraries, then run:

```sh
tools/check-duplicate-prefix-vc.sh
```

The script typechecks the proof interface in
[VerifyGenerated.lean](VerifyGenerated.lean) against the emitted Lean file.
The runner loads the saved standalone MIR and the same root with the same
loader as the generated Lean file. Each certificate checks that the standalone
root's lowered body and identity equal those of the live prepared frame.
A missing certificate fails the test. The proofs cover these seven entries
under the concrete runtime input tape and every typed core choice (`Unit`).
The profile reports certificate replay time separately from generation and
Lean typechecking.

| Slice length | Count | Result |
| --- | --- | --- |
| 8 | 0 | Accept |
| 8 | 2 | Copy two bytes |
| 8 | 4 | Copy four bytes |
| 8 | 5 | Reject |
| 8 | `usize::MAX` | Reject |
| 0 | 0 | Accept |
| 0 | 1 | Reject |

The harness independently checks each return value and all eight bytes after
each nonempty call. Certificate search has a finite budget. A successful
search yields a proof of `GeneratedBodySafety.requiredAt` for that entry,
using the exact finite-outcome semantics of the generated VC.

### Mutable slice call boundary

[The adversarial caller](runtime_adversarial.rs) uses unsafe raw-pointer
dereferences to create a mutable slice while its enclosing frame still holds
a protected shared slice over the same two bytes. The borrow checker rejects
the analogous overlap constructed with ordinary shared and mutable borrows.
The replay enters the same typed `duplicate_prefix` body with either count.
Count zero returns normally. Count one reaches the copy and fails on the
destination byte at offset one, where the write would disable a protected
Frozen tag. The script checks both outcomes against the standalone generated
safety condition.

[VerifyGenerated.lean](VerifyGenerated.lean) turns a rejected replay
certificate into a proof of the negated emitted condition at that prepared
frame. Its permission lemma explains why successful entry is weaker than
write authority. When implicit writes are disabled, the mutable slice retag
requires a read and installs a protected reservation. A reusable mutable
slice contract therefore needs read and write authority over the referent in
its calling context, including compatibility with the permissions and active
protectors at the bytes it can touch. Layout, initialization, and the slice
descriptor can all agree while that authority differs.
