/-
Erdős–Gyárfás problem 64 — one triangle-certificate record action.

This module models only the byte-level action performed for one candidate already produced by the
accepted restricted-growth schedule.  It follows the released checker's source lines 261–267,
273–283, and 369–382: structural rejection reads no byte; otherwise tags `08`, `10`, and `20`
select a C8 payload, a C16 payload, or expansion.  C16 indices are checked for repetition
immediately after each consumed byte, so the first duplicate wins over every later EOF or malformed
byte.  A disabled C16 fails immediately after its tag, before its payload.  The official
`tri_v29_o1.cert` offsets used by the fixtures are documented below.

This is deliberately a branch-local bridge.  Search points already have type `Fin 29`; the
pre-cap side-29 boundary belongs to candidate generation.  There is no generic side-cap wrapper,
recursion, schedule traversal, header or root handling, counter aggregation, completion, EOF
acceptance, rollback, or completeness claim.  Accepted witness records establish rejection
soundness only: they yield genuine Berge lengths 4 and 8.  Expansion does not assert cycle absence,
and this module proves neither witness completeness, stream acceptance, finite-search
completeness, nor Erdős 64.
-/

import Erdos.Erdos64.TriangleCandidateSchedule

set_option autoImplicit false

namespace Erdos64

/-- A total cursor into certificate bytes. -/
structure ByteCursor where
  /-- The complete immutable byte stream. -/
  bytes : List UInt8
  /-- The next byte offset. -/
  pos : Nat
  deriving DecidableEq, Repr

/-- Failures possible while decoding or validating one candidate record. -/
inductive DecodeError
  | eof (offset : Nat)
  | invalidTag (offset : Nat) (tag : UInt8)
  | invalidIndex (offset raw : Nat)
  | invalidEndpoint (offset raw : Nat)
  | repeatedC16Index (offset raw : Nat)
  | c16Disabled (offset : Nat)
  | invalidC8Witness
  | invalidC16Witness
  deriving DecidableEq, Repr

/-- A decoding result retains the exact cursor on both success and failure. -/
inductive DecodeResult (α : Type*)
  | ok (value : α) (cursor : ByteCursor)
  | error (reason : DecodeError) (cursor : ByteCursor)
  deriving DecidableEq, Repr

/-- Read one byte.  Success advances by exactly one; EOF reports and retains the attempted offset. -/
def readByte (cursor : ByteCursor) : DecodeResult UInt8 :=
  match cursor.bytes[cursor.pos]? with
  | some byte => .ok byte { cursor with pos := cursor.pos + 1 }
  | none => .error (.eof cursor.pos) cursor

/-- A successful byte read returns the byte at the current offset and advances exactly once. -/
theorem readByte_eq_ok_iff {cursor next : ByteCursor} {byte : UInt8} :
    readByte cursor = .ok byte next ↔
      cursor.bytes[cursor.pos]? = some byte ∧
        next = { cursor with pos := cursor.pos + 1 } := by
  unfold readByte
  split <;> aesop

/-- An EOF byte read reports exactly the current offset and leaves the cursor byte-for-byte equal. -/
theorem readByte_eq_eof_iff {cursor next : ByteCursor} {offset : Nat} :
    readByte cursor = .error (.eof offset) next ↔
      cursor.bytes[cursor.pos]? = none ∧ offset = cursor.pos ∧ next = cursor := by
  unfold readByte
  split <;> aesop

/-- Read and range-check one old-block index.  The byte is consumed before range failure. -/
def readBlockIndex (m : Nat) (cursor : ByteCursor) : DecodeResult (Fin m) :=
  match readByte cursor with
  | .error e next => .error e next
  | .ok byte next =>
      match decodeBlockIndex m byte.toNat with
      | some index => .ok index next
      | none => .error (.invalidIndex cursor.pos byte.toNat) next

/-- Read and range-check one C16 endpoint code.  The byte is consumed before range failure. -/
def readEndpointCode (cursor : ByteCursor) : DecodeResult (Fin 3) :=
  match readByte cursor with
  | .error e next => .error e next
  | .ok byte next =>
      match decodeEndpointCode byte.toNat with
      | some code => .ok code next
      | none => .error (.invalidEndpoint cursor.pos byte.toNat) next

/-- The syntactic payload of one record, indexed by the current old-block count. -/
inductive WireRecord (m : Nat)
  | c8 (ids : Fin 3 → Fin m)
  | c16 (code : Fin 3) (ids : Fin 7 → Fin m)
  | expansion
  deriving DecidableEq

/-- Read the three sequential old-block indices of a C8 payload. -/
def readC8Payload (m : Nat) (cursor : ByteCursor) : DecodeResult (Fin 3 → Fin m) :=
  match readBlockIndex m cursor with
  | .error e c => .error e c
  | .ok i0 c0 =>
    match readBlockIndex m c0 with
    | .error e c => .error e c
    | .ok i1 c1 =>
      match readBlockIndex m c1 with
      | .error e c => .error e c
      | .ok i2 c2 => .ok ![i0, i1, i2] c2

/-- Read the seven sequential old-block indices of a C16 payload.  In the released source's
lines 273–283, each index is compared with all earlier indices immediately after it is consumed;
the first repetition therefore returns with the duplicate byte consumed and no later byte read. -/
def readC16Ids (m : Nat) (cursor : ByteCursor) : DecodeResult (Fin 7 → Fin m) :=
  match readBlockIndex m cursor with
  | .error e c => .error e c
  | .ok i0 c0 =>
    match readBlockIndex m c0 with
    | .error e c => .error e c
    | .ok i1 c1 =>
      if i1 = i0 then .error (.repeatedC16Index c0.pos i1.val) c1 else
      match readBlockIndex m c1 with
      | .error e c => .error e c
      | .ok i2 c2 =>
        if i2 = i0 ∨ i2 = i1 then .error (.repeatedC16Index c1.pos i2.val) c2 else
        match readBlockIndex m c2 with
        | .error e c => .error e c
        | .ok i3 c3 =>
          if i3 = i0 ∨ i3 = i1 ∨ i3 = i2 then
            .error (.repeatedC16Index c2.pos i3.val) c3
          else
          match readBlockIndex m c3 with
          | .error e c => .error e c
          | .ok i4 c4 =>
            if i4 = i0 ∨ i4 = i1 ∨ i4 = i2 ∨ i4 = i3 then
              .error (.repeatedC16Index c3.pos i4.val) c4
            else
            match readBlockIndex m c4 with
            | .error e c => .error e c
            | .ok i5 c5 =>
              if i5 = i0 ∨ i5 = i1 ∨ i5 = i2 ∨ i5 = i3 ∨ i5 = i4 then
                .error (.repeatedC16Index c4.pos i5.val) c5
              else
              match readBlockIndex m c5 with
              | .error e c => .error e c
              | .ok i6 c6 =>
                if i6 = i0 ∨ i6 = i1 ∨ i6 = i2 ∨ i6 = i3 ∨ i6 = i4 ∨ i6 = i5 then
                  .error (.repeatedC16Index c5.pos i6.val) c6
                else .ok ![i0, i1, i2, i3, i4, i5, i6] c6

/-- Decode one tagged record.  Unknown tags are consumed; disabled C16 consumes only its tag. -/
def decodeRecord (m : Nat) (c16Enabled : Bool) (cursor : ByteCursor) :
    DecodeResult (WireRecord m) :=
  match readByte cursor with
  | .error e next => .error e next
  | .ok tag afterTag =>
      if tag = (0x08 : UInt8) then
        match readC8Payload m afterTag with
        | .ok ids next => .ok (.c8 ids) next
        | .error e next => .error e next
      else if tag = (0x10 : UInt8) then
        if c16Enabled then
          match readEndpointCode afterTag with
          | .error e next => .error e next
          | .ok code afterCode =>
              match readC16Ids m afterCode with
              | .ok ids next => .ok (.c16 code ids) next
              | .error e next => .error e next
        else .error (.c16Disabled cursor.pos) afterTag
      else if tag = (0x20 : UInt8) then
        .ok .expansion afterTag
      else .error (.invalidTag cursor.pos tag) afterTag

/-- Every successfully decoded C8 record consumes exactly four bytes including its tag. -/
theorem decodeRecord_c8_length {m : Nat} {enabled : Bool} {cursor next : ByteCursor}
    {ids : Fin 3 → Fin m} (h : decodeRecord m enabled cursor = .ok (.c8 ids) next) :
    next.pos = cursor.pos + 4 := by
  simp only [decodeRecord, readByte, readC8Payload, readBlockIndex] at h
  grind (splits := 30) (gen := 20)

/-- Every successfully decoded C16 record consumes exactly nine bytes including its tag. -/
theorem decodeRecord_c16_length {m : Nat} {cursor next : ByteCursor}
    {code : Fin 3} {ids : Fin 7 → Fin m}
    (h : decodeRecord m true cursor = .ok (.c16 code ids) next) :
    next.pos = cursor.pos + 9 := by
  simp only [decodeRecord, readByte, readEndpointCode, readC16Ids, readBlockIndex] at h
  grind (splits := 60) (gen := 30)

/-- Every successfully decoded expansion record consumes exactly its one-byte tag. -/
theorem decodeRecord_expansion_length {m : Nat} {enabled : Bool} {cursor next : ByteCursor}
    (h : decodeRecord m enabled cursor = .ok (.expansion : WireRecord m) next) :
    next.pos = cursor.pos + 1 := by
  simp only [decodeRecord, readByte] at h
  grind

/-- A checked record either carries a genuine rejection witness or a clean branch-local expansion. -/
inductive CheckedAction {m : Nat} (s : SearchState m) (t : SearchBlock)
  | c8 (ids : Fin 3 → Fin m) (witness : C8Witness s t ids)
  | c16 (code : Fin 3) (ids : Fin 7 → Fin m) (witness : C16Witness s t code ids)
  | expansion (clean : CleanStructuralOK s t)

/-- Validate wire syntax semantically, reflecting witness checks into genuine propositions. -/
def checkRecord {m : Nat} (s : SearchState m) (t : SearchBlock) (record : WireRecord m)
    (hclean : CleanStructuralOK s t) : Except DecodeError (CheckedAction s t) :=
  match record with
  | .c8 ids =>
      if h : c8Check s t ids = true then
        .ok (.c8 ids ((c8Check_iff s t ids).mp h))
      else .error .invalidC8Witness
  | .c16 code ids =>
      if h : c16Check s t code ids = true then
        .ok (.c16 code ids ((c16Check_iff s t code ids).mp h))
      else .error .invalidC16Witness
  | .expansion => .ok (.expansion hclean)

/-- A checked C8 rejection is sound: it exhibits a genuine Berge cycle of length four. -/
theorem CheckedAction.c8_rejection_sound {m : Nat} {s : SearchState m} {t : SearchBlock}
    {ids : Fin 3 → Fin m} (w : C8Witness s t ids) :
    (s.addConfig t).HasBergeCycleLength 4 :=
  w.hasBergeCycleLength

/-- A checked C16 rejection is sound: it exhibits a genuine Berge cycle of length eight. -/
theorem CheckedAction.c16_rejection_sound {m : Nat} {s : SearchState m} {t : SearchBlock}
    {code : Fin 3} {ids : Fin 7 → Fin m} (w : C16Witness s t code ids) :
    (s.addConfig t).HasBergeCycleLength 8 :=
  w.hasBergeCycleLength

/-- The released structural predicate at the state's exact introduced count. -/
def structuralInvalid {m : Nat} (s : SearchState m) (t : SearchBlock) : Bool :=
  cppStructurallyInvalid s s.introduced.val t

/-- Structural validity yields cleanliness under the state's label invariant. -/
theorem clean_of_structurally_valid {m : Nat} {s : SearchState m} {t : SearchBlock}
    (hinv : StateInvariant s) (hvalid : structuralInvalid s t = false) :
    CleanStructuralOK s t := by
  rw [structuralInvalid] at hvalid
  by_contra hnot
  have htrue : cppStructurallyInvalid s s.introduced.val t = true :=
    (cppStructurallyInvalid_iff hinv.1).mpr hnot
  simp_all

/-- The outcome for one already-generated candidate: no record, or one checked record action. -/
inductive CandidateOutcome {m : Nat} (s : SearchState m) (t : SearchBlock)
  | structural
  | checked (action : CheckedAction s t)

/-- Decode and validate exactly one candidate action, unless structural rejection consumes none. -/
def decodeCandidate {m : Nat} (s : SearchState m) (t : SearchBlock)
    (hinv : StateInvariant s) (_hdisc : CandidateDiscipline s.introduced t)
    (c16Enabled : Bool) (cursor : ByteCursor) : DecodeResult (CandidateOutcome s t) :=
  if hbad : structuralInvalid s t = true then
    .ok .structural cursor
  else
    have hvalid : structuralInvalid s t = false := Bool.eq_false_of_not_eq_true hbad
    let hclean := clean_of_structurally_valid hinv hvalid
    match decodeRecord m c16Enabled cursor with
    | .error e next => .error e next
    | .ok record next =>
        match checkRecord s t record hclean with
        | .ok action => .ok (.checked action) next
        | .error e => .error e next

/-- A structurally invalid candidate consumes no bytes, including when the input stream is empty. -/
theorem decodeCandidate_structural_unchanged {m : Nat} {s : SearchState m} {t : SearchBlock}
    (hinv : StateInvariant s) (hdisc : CandidateDiscipline s.introduced t)
    (enabled : Bool) (cursor : ByteCursor) (hbad : structuralInvalid s t = true) :
    decodeCandidate s t hinv hdisc enabled cursor = .ok .structural cursor := by
  simp [decodeCandidate, hbad]

/-- Branch-local expansion preserves the invariant, installs `t` last, and performs the exact
introduced-count update.  It makes no assertion that the expanded state avoids any cycle. -/
theorem expand_sound {m : Nat} (s : SearchState m) (t : SearchBlock)
    (hinv : StateInvariant s) (hdisc : CandidateDiscipline s.introduced t)
    (hvalid : structuralInvalid s t = false) :
    StateInvariant (s.install t hdisc) ∧
      (s.install t hdisc).blocks (Fin.last m) = t ∧
      (s.install t hdisc).introduced.val = nextIntroducedNat s.introduced t := by
  have hclean : CleanStructuralOK s t := clean_of_structurally_valid hinv hvalid
  exact ⟨stateInvariant_install s t hinv hdisc hclean,
    SearchState.install_blocks_last s t hdisc,
    nextIntroduced_val s.introduced t hdisc⟩

/-! ### Executable fixtures -/

section Fixtures

set_option maxRecDepth 4000

/-- Compact bytes corresponding to official offsets 60–63 (`08 01 02 03`). -/
def officialFirstC8Bytes : List UInt8 := [0x08, 0x01, 0x02, 0x03]

/-- The first official C8 bytes decode exactly to `orbitOneIds` and consume four bytes. -/
theorem officialFirstC8_decode :
    decodeRecord 4 true ⟨officialFirstC8Bytes, 0⟩ =
      .ok (.c8 orbitOneIds) ⟨officialFirstC8Bytes, 4⟩ := by
  decide

/-- The first official C8 record validates to a genuine rejection action. -/
theorem officialFirstC8_validate :
    ∃ action, checkRecord orbitOneState orbitOneCandidate (.c8 orbitOneIds) orbitOne_clean =
      .ok action := by
  refine ⟨.c8 orbitOneIds orbitOne_c8Witness, ?_⟩
  simp [checkRecord, orbitOne_c8Check]

/-- The first official C8 record soundly yields Berge length four. -/
theorem officialFirstC8_sound :
    (orbitOneState.addConfig orbitOneCandidate).HasBergeCycleLength 4 :=
  CheckedAction.c8_rejection_sound orbitOne_c8Witness

/-- The expansion candidate at official offset 72 is `{1,7,8}`. -/
def orbitOneExpansionCandidate : SearchBlock :=
  ⟨1, 7, 8, by decide, by decide⟩

/-- The offset-72 expansion candidate follows the restricted-growth discipline. -/
theorem orbitOneExpansion_discipline :
    CandidateDiscipline orbitOneState.introduced orbitOneExpansionCandidate := by decide

/-- The offset-72 expansion candidate is structurally valid. -/
theorem orbitOneExpansion_valid :
    structuralInvalid orbitOneState orbitOneExpansionCandidate = false := by decide

/-- The official offset-72 tag is one byte and decodes as expansion. -/
theorem officialExpansion_decode :
    decodeRecord 4 true ⟨[0x20], 0⟩ =
      .ok (.expansion : WireRecord 4) ⟨[0x20], 1⟩ := by decide

/-- Installing the official expansion preserves the invariant, installs `{1,7,8}` last, and
advances the exact introduced count.  This instantiates all hypotheses of `expand_sound`. -/
theorem officialExpansion_sound :
    StateInvariant
        (orbitOneState.install orbitOneExpansionCandidate orbitOneExpansion_discipline) ∧
      (orbitOneState.install orbitOneExpansionCandidate orbitOneExpansion_discipline).blocks
          (Fin.last 4) = orbitOneExpansionCandidate ∧
      (orbitOneState.install orbitOneExpansionCandidate
          orbitOneExpansion_discipline).introduced.val =
        nextIntroducedNat orbitOneState.introduced orbitOneExpansionCandidate :=
  expand_sound orbitOneState orbitOneExpansionCandidate orbitOne_stateInvariant
    orbitOneExpansion_discipline orbitOneExpansion_valid

/-- Installing the official expansion advances the introduced count from 7 to 9. -/
theorem officialExpansion_introduced :
    (orbitOneState.install orbitOneExpansionCandidate orbitOneExpansion_discipline).introduced.val =
      9 := by decide

/-- Compact bytes of the official first C16 record. -/
def officialFirstC16Bytes : List UInt8 :=
  [0x10, 0x00, 0x04, 0x00, 0x03, 0x01, 0x05, 0x0a, 0x09]

/-- The official first C16 payload decodes exactly and consumes nine bytes. -/
theorem officialFirstC16_decode :
    decodeRecord 13 true ⟨officialFirstC16Bytes, 0⟩ =
      .ok (.c16 c16FixtureCode c16FixtureIds) ⟨officialFirstC16Bytes, 9⟩ := by
  decide

/-- The official first C16 record validates to a genuine rejection action. -/
theorem officialFirstC16_validate :
    ∃ action, checkRecord c16FixtureState c16FixtureCandidate
      (.c16 c16FixtureCode c16FixtureIds) (by decide) = .ok action := by
  refine ⟨.c16 c16FixtureCode c16FixtureIds c16Fixture_witness, ?_⟩
  simp [checkRecord, c16Fixture_check]

/-- The official first C16 record soundly yields Berge length eight. -/
theorem officialFirstC16_sound :
    (c16FixtureState.addConfig c16FixtureCandidate).HasBergeCycleLength 8 :=
  CheckedAction.c16_rejection_sound c16Fixture_witness

/-- The scheduled `{3,4,6}` candidate is rejected without consulting even an empty stream. -/
theorem invalidCandidate_empty_unchanged :
    decodeCandidate orbitOneState orbitOneInvalidCandidate orbitOne_stateInvariant
      orbitOneInvalidCandidate_discipline true ⟨[], 0⟩ =
        .ok .structural ⟨[], 0⟩ := by
  exact decodeCandidate_structural_unchanged orbitOne_stateInvariant
    orbitOneInvalidCandidate_discipline true ⟨[], 0⟩ (by decide)

/-- An unknown `ff` tag is consumed before its error. -/
theorem unknownTag_fixture :
    decodeRecord 4 true ⟨[0xff], 0⟩ =
      .error (.invalidTag 0 0xff) ⟨[0xff], 1⟩ := by decide

/-- A C8 payload truncated after two indices reports EOF at offset three. -/
theorem truncatedC8_fixture :
    decodeRecord 4 true ⟨[0x08, 0x01, 0x02], 0⟩ =
      .error (.eof 3) ⟨[0x08, 0x01, 0x02], 3⟩ := by decide

/-- Repeating the first C16 ID as the second stops after tag, endpoint, and two IDs.  The
reported offset `3` is the duplicate byte's offset and cursor `4` records that it was consumed. -/
theorem repeatedC16Index_fixture :
    decodeRecord 13 true ⟨[0x10, 0x00, 0x04, 0x04, 0x03, 0x01, 0x05, 0x0a, 0x09], 0⟩ =
      .error (.repeatedC16Index 3 4)
        ⟨[0x10, 0x00, 0x04, 0x04, 0x03, 0x01, 0x05, 0x0a, 0x09], 4⟩ := by decide

/-- EOF immediately after a duplicate C16 ID is not observed: duplicate rejection has precedence. -/
theorem repeatedC16BeforeEof_fixture :
    decodeRecord 13 true ⟨[0x10, 0x00, 0x04, 0x04], 0⟩ =
      .error (.repeatedC16Index 3 4) ⟨[0x10, 0x00, 0x04, 0x04], 4⟩ := by decide

/-- An invalid `ff` byte after a duplicate C16 ID is left unread at cursor offset four. -/
theorem repeatedC16BeforeInvalid_fixture :
    decodeRecord 13 true ⟨[0x10, 0x00, 0x04, 0x04, 0xff], 0⟩ =
      .error (.repeatedC16Index 3 4) ⟨[0x10, 0x00, 0x04, 0x04, 0xff], 4⟩ := by decide

/-- A C16 payload truncated after its endpoint and two distinct indices reports EOF at offset four. -/
theorem truncatedC16_fixture :
    decodeRecord 13 true ⟨[0x10, 0x00, 0x04, 0x01], 0⟩ =
      .error (.eof 4) ⟨[0x10, 0x00, 0x04, 0x01], 4⟩ := by decide

/-- A disabled C16 stops immediately after consuming its tag, before even an absent endpoint. -/
theorem disabledC16_fixture :
    decodeRecord 13 false ⟨[0x10], 0⟩ =
      .error (.c16Disabled 0) ⟨[0x10], 1⟩ := by decide

/-- An `ff` old-block index is consumed and rejected without wrapping or substitution. -/
theorem invalidIndex_fixture :
    decodeRecord 4 true ⟨[0x08, 0xff], 0⟩ =
      .error (.invalidIndex 1 255) ⟨[0x08, 0xff], 2⟩ := by decide

/-- An `ff` endpoint is consumed and rejected without wrapping or substitution. -/
theorem invalidEndpoint_fixture :
    decodeRecord 13 true ⟨[0x10, 0xff], 0⟩ =
      .error (.invalidEndpoint 1 255) ⟨[0x10, 0xff], 2⟩ := by decide

/-- Repeated C8 IDs decode syntactically but are rejected by semantic validation. -/
theorem repeatedC8Witness_fixture :
    checkRecord orbitOneState orbitOneCandidate (.c8 repeatedIdsPayload) orbitOne_clean =
      .error .invalidC8Witness := by
  simp [checkRecord, repeatedIdsCheck]

/-- The existing wrong C16 endpoint decodes syntactically but fails semantic validation. -/
theorem wrongC16Endpoint_fixture :
    checkRecord c16FixtureState c16FixtureCandidate (.c16 1 c16FixtureIds) (by decide) =
      .error .invalidC16Witness := by
  simp [checkRecord, c16Fixture_wrongCodeCheck]

end Fixtures

end Erdos64
