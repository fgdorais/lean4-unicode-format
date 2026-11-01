/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import UnicodeFormat.Basic

/-! # Decoding and encoding iterators

Decoders and encoders transform pure iterators, `Std.Iter` over `Id`, of one kind of token into
another: bytes into code units, code units into characters, and back.

A *decoder* `d : δ` with `[Decoder δ τ σ]` reads one token of type `σ` from the tokens of type `τ`
at an iterator: `Decoder.decode d it` continues with the token and the iterator after it, with a
`DecodeError.Kind` and the iterator after the ill-formed input, or with the end of the input. It
looks ahead by stepping copies of `it`, so it needs no buffer. `DecodeIterator δ ι` repeats it over
an iterator of type `ι`. A strict decoding iterator stops at ill-formed input, where
`it.decodeError?` tells why, and `it.decodeFailure?` finds the first ill-formed input ahead; a lossy
one yields `Decoder.replacement d` instead and goes on after the ill-formed input.
`DecodeError.Kind` and `DecodeError` have `ToString` instances for error messages.

An *encoder* `e : ε` with `[Encoder ε σ τ]` gives the tokens of type `τ` that encode a token of
type `σ`, and `EncodeIterator ε ι` yields them for each token of an iterator of type `ι`.

Each step of these iterators either moves the inner iterator strictly forward or, for encoders,
yields a token that is still pending from the last one. The inner iterator is `it.decodeBase` or
`it.encodeBase`, and `it.encodeBoundary` tells whether nothing is pending. Decoders always stop
between two tokens, so the position of the inner iterator is the position of the error.
-/

namespace Unicode
open Std

section Advanced

variable {ι τ : Type} [Iterator ι Id τ]

/-- `it'` is reachable from `it` by one or more plausible successor steps. -/
@[expose]
public def Advanced (it' it : Iter (α := ι) τ) : Prop :=
  IterM.TerminationMeasures.Finite.Rel it'.finitelyManySteps! it.finitelyManySteps!

public theorem Advanced.trans {it'' it' it : Iter (α := ι) τ} :
    Advanced it'' it' → Advanced it' it → Advanced it'' it :=
  Relation.TransGen.trans

public theorem Advanced.of_yield {it' it : Iter (α := ι) τ} {out : τ}
    (h : it.IsPlausibleStep (.yield it' out)) : Advanced it' it :=
  IterM.TerminationMeasures.Finite.rel_of_yield h

public theorem Advanced.of_skip {it' it : Iter (α := ι) τ}
    (h : it.IsPlausibleStep (.skip it')) : Advanced it' it :=
  IterM.TerminationMeasures.Finite.rel_of_skip h

/-- `nextToken` after a `skip` step: the loop over any further `skip` steps. -/
@[specialize]
public def nextTokenAfterSkip [Iterators.Productive ι Id] {β : Sort _} (it : Iter (α := ι) τ)
    (yield : (rest : Iter (α := ι) τ) → Advanced rest it → τ → β) (done : Unit → β) : β :=
  match it.step with
  | ⟨.yield it' x, h⟩ => yield it' (.of_yield h) x
  | ⟨.skip it', h⟩ =>
    nextTokenAfterSkip it' (fun rest h' x => yield rest (h'.trans (.of_skip h)) x) done
  | ⟨.done, _⟩ => done ()
termination_by it.finitelyManySkips

/--
Steps `it` past any `skip` steps. Calls `yield` with the next token and the iterator after it, or
`done` at the end of the input. Written in continuation-passing style, and the first step is
inlined, so that specialization avoids allocating an intermediate result; only further `skip` steps
go through `nextTokenAfterSkip`.
-/
@[inline]
public def nextToken [Iterators.Productive ι Id] {β : Sort _} (it : Iter (α := ι) τ)
    (yield : (rest : Iter (α := ι) τ) → Advanced rest it → τ → β) (done : Unit → β) : β :=
  match it.step with
  | ⟨.yield it' x, h⟩ => yield it' (.of_yield h) x
  | ⟨.skip it', h⟩ =>
    nextTokenAfterSkip it' (fun rest h' x => yield rest (h'.trans (.of_skip h)) x) done
  | ⟨.done, _⟩ => done ()

end Advanced

/-- Why input is ill-formed. -/
public inductive DecodeError.Kind where
  /-- A maximal subpart of an ill-formed UTF-8 byte sequence. -/
  | illFormedUTF8
  /-- A UTF-16 surrogate code unit that is not part of a surrogate pair. -/
  | unpairedSurrogate
  /-- A UTF-32 code unit that is not a Unicode scalar value. -/
  | notScalarValue
  /-- An incomplete code unit at the end of the bytes of UTF-16 or UTF-32 code units. -/
  | incompleteCodeUnit
  deriving Inhabited, DecidableEq, Repr

/-- A description of ill-formed input of kind `k`, for error messages. -/
public def DecodeError.Kind.toString : DecodeError.Kind → String
  | .illFormedUTF8 => "ill-formed UTF-8"
  | .unpairedSurrogate => "unpaired surrogate"
  | .notScalarValue => "not a Unicode scalar value"
  | .incompleteCodeUnit => "incomplete code unit"

public instance : ToString DecodeError.Kind := ⟨DecodeError.Kind.toString⟩

/--
Ill-formed input: why, and where. The position is the index of the first token of the ill-formed
input: of the code unit for UTF-16 and UTF-32, and of the byte for UTF-8 and the encoding schemes,
counting a byte order mark or signature.
-/
public structure DecodeError where
  /-- Why the input is ill-formed. -/
  kind : DecodeError.Kind
  /-- The index of the first token of the ill-formed input, in code units or bytes. -/
  pos : Nat
  deriving Inhabited, DecidableEq, Repr

/-- A description of the error `e` for error messages, such as `unpaired surrogate at index 2`. -/
public def DecodeError.toString (e : DecodeError) : String :=
  s!"{e.kind} at index {e.pos}"

public instance : ToString DecodeError := ⟨DecodeError.toString⟩

/-- One step of reading a token, as data, so that a loop over it is a self tail call. -/
private inductive Step (ι τ σ : Type) where
  | yield (rest : Iter (α := ι) τ) (x : σ)
  | error (rest : Iter (α := ι) τ)
  | done

/-! ## Decoders -/

/-- A decoder `d : δ` reads tokens of type `σ` from tokens of type `τ`. -/
public class Decoder (δ : Type) (τ σ : outParam Type) where
  /-- The token that lossy decoding yields for ill-formed input. -/
  replacement : δ → σ
  /--
  Decodes one token from `it`. Calls `yield` with the token and the iterator after it, `error`
  with the error and the iterator after the ill-formed input, or `done` at the end of the input.
  -/
  decode {ι : Type} [Iterator ι Id τ] [Iterators.Productive ι Id] {β : Type} (d : δ)
    (it : Iter (α := ι) τ) (yield : (rest : Iter (α := ι) τ) → Advanced rest it → σ → β)
    (error : DecodeError.Kind → (rest : Iter (α := ι) τ) → Advanced rest it → β)
    (done : Unit → β) : β

/-- Iterator over the tokens decoded by `decoder` from an iterator of type `ι`. -/
public structure DecodeIterator (δ ι : Type) {τ σ : Type} [Decoder δ τ σ] where
  /-- The decoder. -/
  decoder : δ
  /-- Whether ill-formed input yields `Decoder.replacement decoder` rather than ending. -/
  lossy : Bool
  /-- The input iterator. -/
  inner : Iter (α := ι) τ

namespace DecodeIterator

variable {δ ι τ σ : Type} [Decoder δ τ σ] [Iterator ι Id τ] [Iterators.Productive ι Id]

public instance : Iterator (DecodeIterator δ ι) Id σ where
  IsPlausibleStep it
    | .yield it' _ => it'.internalState.decoder = it.internalState.decoder ∧
      it'.internalState.lossy = it.internalState.lossy ∧
      Advanced it'.internalState.inner it.internalState.inner
    | .skip _ => False
    | .done => True
  step := fun ⟨⟨d, lossy, inner⟩⟩ =>
    pure <| Decoder.decode d inner
      (fun rest h x => .deflate ⟨.yield ⟨⟨d, lossy, rest⟩⟩ x, ⟨rfl, rfl, h⟩⟩)
      (fun _ rest h =>
        if lossy then .deflate ⟨.yield ⟨⟨d, lossy, rest⟩⟩ (Decoder.replacement d), ⟨rfl, rfl, h⟩⟩
        else .deflate ⟨.done, trivial⟩)
      (fun _ => .deflate ⟨.done, trivial⟩)

/-- Every step moves the input iterator strictly forward. -/
public theorem advanced_of_successor {it' it : IterM (α := DecodeIterator δ ι) Id σ}
    (h : it'.IsPlausibleSuccessorOf it) :
    Advanced it'.internalState.inner it.internalState.inner := by
  obtain ⟨step, hs, hp⟩ := h
  cases step with
  | yield it'' _ => cases hs; exact hp.2.2
  | skip _ => cases hp
  | done => cases hs

private def finitenessRelation [Iterators.Finite ι Id] :
    Iterators.FinitenessRelation (DecodeIterator δ ι) Id where
  Rel := InvImage IterM.TerminationMeasures.Finite.Rel
    (fun it => it.internalState.inner.finitelyManySteps)
  wf := InvImage.wf _ IterM.TerminationMeasures.instWellFoundedRelationFinite.wf
  subrelation h := advanced_of_successor h

public instance [Iterators.Finite ι Id] : Iterators.Finite (DecodeIterator δ ι) Id :=
  .of_finitenessRelation finitenessRelation

public instance (priority := low) [Monad m] : IteratorLoop (DecodeIterator δ ι) Id m :=
  .defaultImplementation

-- Each token goes through `lift`, like each step of the iterator in the default implementation, so
-- the two agree for every lawful `lift`, which is what core's consumers pass. The loop recurses
-- after `bind`, not inside the function passed to `lift`: when `lift` is not inlined, a recursive
-- call there takes a stack frame for each token.
@[inline]
private unsafe def forInImpl {n : Type → Type} [Monad n]
    (lift : (γ : Type) → (δ : Type) → (γ → n δ) → Id γ → n δ) (γ : Type)
    (Pl : σ → γ → ForInStep γ → Prop) (it : IterM (α := DecodeIterator δ ι) Id σ) (init : γ)
    (f : (b : σ) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) : n γ :=
  let s := it.internalState
  loop s.decoder s.lossy s.inner init
where
  @[specialize] loop (d : δ) (lossy : Bool) (inner : Iter (α := ι) τ) (c : γ) : n γ :=
    let step : Step ι τ σ := Decoder.decode d inner (fun rest _ x => .yield rest x)
      (fun _ rest _ => if lossy then .yield rest (Decoder.replacement d) else .error rest)
      (fun _ => .done)
    match step with
    | .yield rest x => do
      match ← lift _ _ (fun _ => f x lcProof c) (pure x) with
      | ⟨.yield c, _⟩ => loop d lossy rest c
      | ⟨.done c, _⟩ => pure c
    | .error _ | .done => pure c

/--
The loop behind `for` loops and the `Std.Iterators` consumers on decoding iterators. Logically it
is `Std.IteratorLoop.defaultImplementation`, which steps the iterator one token at a time; it is
implemented by decoding directly from the input iterator.
-/
@[implemented_by forInImpl]
public def forIn {n : Type → Type} [Monad n]
    (lift : (γ : Type) → (δ : Type) → (γ → n δ) → Id γ → n δ) (γ : Type)
    (Pl : σ → γ → ForInStep γ → Prop) (it : IterM (α := DecodeIterator δ ι) Id σ) (init : γ)
    (f : (b : σ) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) : n γ :=
  IteratorLoop.defaultImplementation.forIn lift γ Pl it init f

public instance {n : Type → Type} [Monad n] : IteratorLoop (DecodeIterator δ ι) Id n where
  forIn := forIn

public instance {n : Type → Type} [Monad n] : LawfulIteratorLoop (DecodeIterator δ ι) Id n where
  lawful _ _ _ _ _ _ _ _ := rfl

/-- The input iterator, at the start of the next token to decode. -/
@[inline]
public def _root_.Std.Iter.decodeBase (it : Iter (α := DecodeIterator δ ι) σ) : Iter (α := ι) τ :=
  it.internalState.inner

/--
The error in the input at `it`, if the input there is ill-formed. When a strict decoding iterator
stops, this is why: `none` means that it reached the end of the input.
-/
public def _root_.Std.Iter.decodeError? (it : Iter (α := DecodeIterator δ ι) σ) :
    Option DecodeError.Kind :=
  Decoder.decode it.internalState.decoder it.internalState.inner (fun _ _ _ => none)
    (fun e _ _ => some e) (fun _ => none)

/-- Whether `it` yields `Decoder.replacement` for ill-formed input rather than ending there. -/
@[inline]
public def _root_.Std.Iter.decodeIsLossy (it : Iter (α := DecodeIterator δ ι) σ) : Bool :=
  it.internalState.lossy

end DecodeIterator

/--
Decodes the tokens of `it` with `d`, stopping at the first ill-formed input.

A `for` loop or fold over the result ends at ill-formed input just as at the end of the input. To
tell them apart, check `it.decodeError?` on the iterator where decoding stopped, find the first
ill-formed input ahead with `it.decodeFailure?`, or decode with `Decoder.iterLossy` instead.
-/
@[inline]
public def Decoder.iter {δ ι τ σ : Type} [Decoder δ τ σ] (d : δ) (it : Iter (α := ι) τ) :
    Iter (α := DecodeIterator δ ι) σ :=
  ⟨⟨d, false, it⟩⟩

/-- Decodes the tokens of `it` with `d`, replacing each ill-formed input with
`Decoder.replacement d`. -/
@[inline]
public def Decoder.iterLossy {δ ι τ σ : Type} [Decoder δ τ σ] (d : δ) (it : Iter (α := ι) τ) :
    Iter (α := DecodeIterator δ ι) σ :=
  ⟨⟨d, true, it⟩⟩

/-- One decoding step with the proof that it advances, for loops by well-founded recursion. -/
private inductive DecodeStep {ι τ : Type} [Iterator ι Id τ] (it : Iter (α := ι) τ) (σ : Type) where
  | yield (rest : Iter (α := ι) τ) (h : Advanced rest it) (x : σ)
  | error (kind : DecodeError.Kind) (rest : Iter (α := ι) τ) (h : Advanced rest it)
  | done

/--
Decodes the tokens of `it` with `d` and folds them with `f` from `init`, up to the first ill-formed
input. Returns the result, and the kind of error and the iterator at the ill-formed input, if any.
-/
@[specialize]
public def Decoder.foldUntilError {δ ι τ σ γ : Type} [Decoder δ τ σ] [Iterator ι Id τ]
    [Iterators.Finite ι Id] (d : δ) (f : γ → σ → γ) (init : γ) (it : Iter (α := ι) τ) :
    γ × Option (DecodeError.Kind × Iter (α := ι) τ) :=
  match (Decoder.decode d it (fun rest h x => .yield rest h x) (fun k rest h => .error k rest h)
      (fun _ => .done) : DecodeStep it σ) with
  | .yield rest _ x => foldUntilError d f (f init x) rest
  | .error k _ _ => (init, some (k, it))
  | .done => (init, none)
termination_by it.finitelyManySteps
decreasing_by assumption

/--
Decodes the tokens of `it` with `d` and folds them with `f` from `init`, with
`Decoder.replacement d` for each ill-formed input.
-/
@[specialize]
public def Decoder.foldLossy {δ ι τ σ γ : Type} [Decoder δ τ σ] [Iterator ι Id τ]
    [Iterators.Finite ι Id] (d : δ) (f : γ → σ → γ) (init : γ) (it : Iter (α := ι) τ) : γ :=
  match (Decoder.decode d it (fun rest h x => .yield rest h x) (fun k rest h => .error k rest h)
      (fun _ => .done) : DecodeStep it σ) with
  | .yield rest _ x => foldLossy d f (f init x) rest
  | .error _ rest _ => foldLossy d f (f init (Decoder.replacement d)) rest
  | .done => init
termination_by it.finitelyManySteps
decreasing_by all_goals assumption

section Failure

variable {δ ι τ σ : Type} [Decoder δ τ σ] [Iterator ι Id τ] [Iterators.Finite ι Id]

/--
The first ill-formed input from `it` on, if any: its kind, and the iterator with the same decoder at
its start. A strict decoding iterator stops there, so this finds where and why a parser or a loop
over `it` would see the end of the input early.
-/
public def _root_.Std.Iter.decodeFailure? (it : Iter (α := DecodeIterator δ ι) σ) :
    Option (DecodeError.Kind × Iter (α := DecodeIterator δ ι) σ) :=
  let s := it.internalState
  match Decoder.foldUntilError s.decoder (fun _ _ => ()) () s.inner with
  | (_, some (k, base)) => some (k, ⟨⟨s.decoder, s.lossy, base⟩⟩)
  | (_, none) => none

end Failure

/-! ## Encoders -/

/-- An encoder `e : ε` writes each token of type `σ` as tokens of type `τ`. -/
public class Encoder (ε : Type) (σ τ : outParam Type) where
  /-- The number of tokens that encode `x`. -/
  length : ε → σ → Nat
  /-- The token at index `i` of the encoding of `x`, for `i < length e x`. -/
  unit : ε → σ → Nat → τ

/--
Iterator over the tokens that `encoder` writes for each token of an iterator of type `ι`. The
encoding of the last input token `current` has `length` tokens, of which those before `index` have
been yielded.
-/
public structure EncodeIterator (ε ι : Type) {σ τ : Type} [Encoder ε σ τ] where
  /-- The encoder. -/
  encoder : ε
  /-- The input iterator, after `current`. -/
  inner : Iter (α := ι) σ
  /-- The last input token. -/
  current : σ
  /-- The index of the next token of the encoding of `current`. -/
  index : Nat
  /-- The number of tokens of the encoding of `current`. -/
  length : Nat

namespace EncodeIterator

variable {ε ι σ τ : Type} [Encoder ε σ τ] [Iterator ι Id σ]

/-- Plausible steps: yield a pending token, or read the next input token. -/
@[expose, reducible]
public def PlausibleStep (it : IterM (α := EncodeIterator ε ι) Id τ) :
    IterStep (IterM (α := EncodeIterator ε ι) Id τ) τ → Prop
  | .yield it' t =>
    let s := it.internalState
    if s.index < s.length then
      it'.internalState = { s with index := s.index + 1 } ∧
        t = Encoder.unit s.encoder s.current s.index
    else
      ∃ i' x, s.inner.IsPlausibleStep (.yield i' x) ∧ 0 < Encoder.length s.encoder x ∧
        it'.internalState = ⟨s.encoder, i', x, 1, Encoder.length s.encoder x⟩ ∧
        t = Encoder.unit s.encoder x 0
  | .skip it' =>
    let s := it.internalState
    ¬ s.index < s.length ∧
      ((∃ i', s.inner.IsPlausibleStep (.skip i') ∧ it'.internalState = { s with inner := i' }) ∨
       (∃ i' x, s.inner.IsPlausibleStep (.yield i' x) ∧ Encoder.length s.encoder x = 0 ∧
        it'.internalState = ⟨s.encoder, i', x, 0, 0⟩))
  | .done => ¬ it.internalState.index < it.internalState.length ∧
    it.internalState.inner.IsPlausibleStep .done

public instance : Iterator (EncodeIterator ε ι) Id τ where
  IsPlausibleStep := PlausibleStep
  step := fun ⟨⟨e, inner, cur, i, n⟩⟩ =>
    if h : i < n then
      pure (.deflate ⟨.yield ⟨⟨e, inner, cur, i + 1, n⟩⟩ (Encoder.unit e cur i),
        by simp [PlausibleStep, h]⟩)
    else
      match inner.step with
      | ⟨.yield i' x, h'⟩ =>
        if hx : 0 < Encoder.length e x then
          pure (.deflate ⟨.yield ⟨⟨e, i', x, 1, Encoder.length e x⟩⟩ (Encoder.unit e x 0),
            by simp only [PlausibleStep, h, ↓reduceIte]; exact ⟨i', x, h', hx, rfl, rfl⟩⟩)
        else
          pure (.deflate ⟨.skip ⟨⟨e, i', x, 0, 0⟩⟩,
            by simp only [PlausibleStep]; exact ⟨h, .inr ⟨i', x, h', by omega, rfl⟩⟩⟩)
      | ⟨.skip i', h'⟩ =>
        pure (.deflate ⟨.skip ⟨⟨e, i', cur, i, n⟩⟩,
          by simp only [PlausibleStep]; exact ⟨h, .inl ⟨i', h', by first | rfl | trivial⟩⟩⟩)
      | ⟨.done, h'⟩ => pure (.deflate ⟨.done, by simp only [PlausibleStep]; exact ⟨h, h'⟩⟩)

private theorem isPlausibleStep_eq {it : IterM (α := EncodeIterator ε ι) Id τ} {step} :
    it.IsPlausibleStep step = PlausibleStep it step := rfl

/-- A single step either yields a pending token or steps the input iterator. -/
private theorem successor_cases {it' it : IterM (α := EncodeIterator ε ι) Id τ}
    (h : it'.IsPlausibleSuccessorOf it) :
    (it'.internalState.inner = it.internalState.inner ∧
      it'.internalState.length - it'.internalState.index <
        it.internalState.length - it.internalState.index) ∨
      (¬ it.internalState.index < it.internalState.length ∧
        Advanced it'.internalState.inner it.internalState.inner) := by
  obtain ⟨step, hs, hp⟩ := h
  rw [isPlausibleStep_eq] at hp
  cases step with
  | yield it'' t =>
    cases hs
    simp only [PlausibleStep] at hp
    split at hp
    · next hi =>
      obtain ⟨h1, _⟩ := hp
      exact .inl ⟨by rw [h1], by rw [h1]; simp only; omega⟩
    · next hi =>
      obtain ⟨i', x, h1, _, h2, _⟩ := hp
      exact .inr ⟨hi, by rw [h2]; exact .of_yield h1⟩
  | skip it'' =>
    cases hs
    simp only [PlausibleStep] at hp
    obtain ⟨hi, ⟨i', h1, h2⟩ | ⟨i', x, h1, _, h2⟩⟩ := hp
    · exact .inr ⟨hi, by rw [h2]; exact .of_skip h1⟩
    · exact .inr ⟨hi, by rw [h2]; exact .of_yield h1⟩
  | done => cases hs

private def finitenessRelation [Iterators.Finite ι Id] :
    Iterators.FinitenessRelation (EncodeIterator ε ι) Id where
  Rel := InvImage (Prod.Lex IterM.TerminationMeasures.Finite.Rel (· < ·))
    (fun it => (it.internalState.inner.finitelyManySteps,
      it.internalState.length - it.internalState.index))
  wf := InvImage.wf _
    (Prod.lex IterM.TerminationMeasures.instWellFoundedRelationFinite Nat.lt_wfRel).wf
  subrelation {it it'} h := by
    rcases successor_cases h with ⟨h1, h2⟩ | ⟨_, h2⟩
    · show Prod.Lex _ _ (_, _) (_, _)
      rw [h1]
      exact Prod.Lex.right _ h2
    · exact Prod.Lex.left _ _ h2

public instance [Iterators.Finite ι Id] : Iterators.Finite (EncodeIterator ε ι) Id :=
  .of_finitenessRelation finitenessRelation

public instance (priority := low) [Monad m] : IteratorLoop (EncodeIterator ε ι) Id m :=
  .defaultImplementation

-- Each token goes through `lift`, like each step of the iterator in the default implementation, so
-- the two agree for every lawful `lift`, which is what core's consumers pass. The loop recurses
-- after `bind`, not inside the function passed to `lift`: when `lift` is not inlined, a recursive
-- call there takes a stack frame for each token.
@[inline]
private unsafe def forInImpl {n : Type x → Type x'} [Monad n] [Iterators.Productive ι Id]
    (lift : (γ : Type) → (δ : Type x) → (γ → n δ) → Id γ → n δ) (γ : Type x)
    (Pl : τ → γ → ForInStep γ → Prop) (it : IterM (α := EncodeIterator ε ι) Id τ) (init : γ)
    (f : (b : τ) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) : n γ :=
  let s := it.internalState
  loop s.encoder s.inner s.current s.index s.length init
where
  @[specialize] loop (e : ε) (inner : Iter (α := ι) σ) (cur : σ) (i len : Nat) (c : γ) : n γ :=
    if i < len then do
      let u := Encoder.unit e cur i
      match ← lift _ _ (fun _ => f u lcProof c) (pure u) with
      | ⟨.yield c, _⟩ => loop e inner cur (i + 1) len c
      | ⟨.done c, _⟩ => pure c
    else
      match (nextToken inner (fun rest _ x => .yield rest x) (fun _ => .done) : Step ι σ σ) with
      | .yield rest x => loop e rest x 0 (Encoder.length e x) c
      | .error _ | .done => pure c

/--
The loop behind `for` loops and the `Std.Iterators` consumers on encoding iterators. Logically it
is `Std.IteratorLoop.defaultImplementation`, which steps the iterator one token at a time; it is
implemented by reading the input iterator directly.
-/
@[implemented_by forInImpl]
public def forIn {n : Type x → Type x'} [Monad n] [Iterators.Productive ι Id]
    (lift : (γ : Type) → (δ : Type x) → (γ → n δ) → Id γ → n δ) (γ : Type x)
    (Pl : τ → γ → ForInStep γ → Prop) (it : IterM (α := EncodeIterator ε ι) Id τ) (init : γ)
    (f : (b : τ) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))) : n γ :=
  IteratorLoop.defaultImplementation.forIn lift γ Pl it init f

public instance {n : Type x → Type x'} [Monad n] [Iterators.Productive ι Id] :
    IteratorLoop (EncodeIterator ε ι) Id n where
  forIn := forIn

public instance {n : Type x → Type x'} [Monad n] [Iterators.Productive ι Id] :
    LawfulIteratorLoop (EncodeIterator ε ι) Id n where
  lawful _ _ _ _ _ _ _ _ := rfl

/-- The input iterator, after the token whose encoding is being yielded. -/
@[inline]
public def _root_.Std.Iter.encodeBase (it : Iter (α := EncodeIterator ε ι) τ) : Iter (α := ι) σ :=
  it.internalState.inner

/-- Whether the encoding of the last input token has been yielded entirely. -/
@[inline]
public def _root_.Std.Iter.encodeBoundary (it : Iter (α := EncodeIterator ε ι) τ) : Bool :=
  it.internalState.length ≤ it.internalState.index

end EncodeIterator

/-- Encodes the tokens of `it` with `e`. -/
@[inline]
public def Encoder.iter {ε ι σ τ : Type} [Encoder ε σ τ] [Inhabited σ] (e : ε)
    (it : Iter (α := ι) σ) : Iter (α := EncodeIterator ε ι) τ :=
  ⟨⟨e, it, default, 0, 0⟩⟩

end Unicode
